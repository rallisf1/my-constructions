function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.wholeText !== data)
        text.data = data;
}
function set_input_value(input, value) {
    input.value = value == null ? '' : value;
}
function set_style(node, key, value, important) {
    if (value === null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            else
                this.e = element(target.nodeName);
            this.t = target;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
const render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro ??? we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro ??? needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.55.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link1;
	let link2;
	let link3;
	let title_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let meta7;
	let meta8;
	let meta9;
	let meta10;
	let meta11;
	let meta12;
	let meta13;
	let link4;
	let style;
	let t;
	document.title = title_value = /*seo_title*/ ctx[0];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			meta7 = element("meta");
			meta8 = element("meta");
			meta9 = element("meta");
			meta10 = element("meta");
			meta11 = element("meta");
			meta12 = element("meta");
			meta13 = element("meta");
			link4 = element("link");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\n  /* Colors */\n  --color-primary: #ffc329;\n  --color-white: #fff;\n  --color-black: #000;\n  --color-gray: #242424;\n  --color-dark: #0f0f0f;\n  --color-text: #727272;\n  --border-color: #c1c1c1;\n\n  /* Default property values */\n  --padding: 1rem; \n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 0; \n  --max-width: 1200px;\n  --transition: 0.3s all ease-in-out;\n}\n\n.primo-page {\n  font-family: Arimo, sans-serif;\n  color: var(--color-text);\n  line-height: 1.6; \n  font-size: 1rem;\n  background: var(--color-white);\n  position: relative;\n}\n\n.primo-section .primo-content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n}\n\n.primo-section .primo-content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.primo-section .primo-content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n\n.primo-section .primo-content a {\n    text-decoration: none;\n  }\n\n.primo-section .primo-content a:hover {\n      color: var(--color-primary);\n    }\n\n.primo-section .primo-content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.primo-section .primo-content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.primo-section .primo-content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.primo-section .primo-content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container, .section.has-content {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 0 var(--padding, 1rem); \n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 700;\n  margin: 0;\n}\n\n.button {\n  background: var(--color-dark);\n  border-radius: 3px;\n  padding: 8px 20px;\n  transition: var(--transition);\n  color: var(--color-white);\n}\n\n.button:hover {\n    background: var(--color-primary);\n    color: var(--color-black);\n  }\n\n.button.inverted {\n    background: var(--color-primary);\n    color: var(--color-black);\n  }\n\n.button.inverted:hover {\n      background: var(--color-white);\n    }\n\na {\n  transition: var(--transition);\n}\n\nbody .primo-section.has-component {position: relative;}\nbody .primo-section.has-component.visible {min-height: auto;}\nli > a {display: block;}\n\n#page .section.component-nqfta {\n  z-index: 2;\n}#page > .section {\n  position: relative;\n  z-index: 1;\n}\n\n#page > .section:first-of-type {\n  position: absolute;\n  top: 0;\n  left: 0;\n  z-index: 0;\n}\n\n#page > .section:nth-child(3) {\n  z-index: 2;\n}\n\n#top-bar {\n  background-color: transparent!important;\n}\n\n#top-bar a {\n    color: var(--color-white);\n  }\n\n#top-bar a:hover {\n      color: var(--color-primary);\n    }\n\n#nav nav .logo svg .st0{fill:var(--color-white);}\n\n#nav nav > ul > li a.link {\n            color: var(--color-white);\n          }\n\n#nav nav > ul > li a.link:hover {\n              color: var(--color-primary);\n            }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1ger8es', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, crossorigin: true });
			link2 = claim_element(head_nodes, "LINK", { href: true, rel: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			meta7 = claim_element(head_nodes, "META", { name: true, content: true });
			meta8 = claim_element(head_nodes, "META", { property: true, content: true });
			meta9 = claim_element(head_nodes, "META", { property: true, content: true });
			meta10 = claim_element(head_nodes, "META", { property: true, content: true });
			meta11 = claim_element(head_nodes, "META", { property: true, content: true });
			meta12 = claim_element(head_nodes, "META", { property: true, content: true });
			meta13 = claim_element(head_nodes, "META", { property: true, content: true });
			link4 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\n  /* Colors */\n  --color-primary: #ffc329;\n  --color-white: #fff;\n  --color-black: #000;\n  --color-gray: #242424;\n  --color-dark: #0f0f0f;\n  --color-text: #727272;\n  --border-color: #c1c1c1;\n\n  /* Default property values */\n  --padding: 1rem; \n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 0; \n  --max-width: 1200px;\n  --transition: 0.3s all ease-in-out;\n}\n\n.primo-page {\n  font-family: Arimo, sans-serif;\n  color: var(--color-text);\n  line-height: 1.6; \n  font-size: 1rem;\n  background: var(--color-white);\n  position: relative;\n}\n\n.primo-section .primo-content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n}\n\n.primo-section .primo-content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.primo-section .primo-content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n\n.primo-section .primo-content a {\n    text-decoration: none;\n  }\n\n.primo-section .primo-content a:hover {\n      color: var(--color-primary);\n    }\n\n.primo-section .primo-content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.primo-section .primo-content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.primo-section .primo-content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.primo-section .primo-content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container, .section.has-content {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 0 var(--padding, 1rem); \n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 700;\n  margin: 0;\n}\n\n.button {\n  background: var(--color-dark);\n  border-radius: 3px;\n  padding: 8px 20px;\n  transition: var(--transition);\n  color: var(--color-white);\n}\n\n.button:hover {\n    background: var(--color-primary);\n    color: var(--color-black);\n  }\n\n.button.inverted {\n    background: var(--color-primary);\n    color: var(--color-black);\n  }\n\n.button.inverted:hover {\n      background: var(--color-white);\n    }\n\na {\n  transition: var(--transition);\n}\n\nbody .primo-section.has-component {position: relative;}\nbody .primo-section.has-component.visible {min-height: auto;}\nli > a {display: block;}\n\n#page .section.component-nqfta {\n  z-index: 2;\n}#page > .section {\n  position: relative;\n  z-index: 1;\n}\n\n#page > .section:first-of-type {\n  position: absolute;\n  top: 0;\n  left: 0;\n  z-index: 0;\n}\n\n#page > .section:nth-child(3) {\n  z-index: 2;\n}\n\n#top-bar {\n  background-color: transparent!important;\n}\n\n#top-bar a {\n    color: var(--color-white);\n  }\n\n#top-bar a:hover {\n      color: var(--color-primary);\n    }\n\n#nav nav .logo svg .st0{fill:var(--color-white);}\n\n#nav nav > ul > li a.link {\n            color: var(--color-white);\n          }\n\n#nav nav > ul > li a.link:hover {\n              color: var(--color-primary);\n            }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "preconnect");
			attr(link0, "href", "https://fonts.googleapis.com");
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.gstatic.com");
			attr(link1, "crossorigin", "");
			attr(link2, "href", "https://fonts.googleapis.com/css2?family=Arimo:ital,wght@0,400;0,500;0,700;1,400&display=swap");
			attr(link2, "rel", "stylesheet");
			attr(link3, "rel", "preconnect");
			attr(link3, "href", "https://zzyumdkmbkvyfpswmpyz.supabase.co");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*seo_description*/ ctx[1]);
			attr(meta3, "name", "twitter:title");
			attr(meta3, "content", /*seo_title*/ ctx[0]);
			attr(meta4, "name", "twitter:site");
			attr(meta4, "content", "@mytkolliconstructions");
			attr(meta5, "name", "twitter:handle");
			attr(meta5, "content", "@mytkolliconstructions");
			attr(meta6, "name", "twitter:cardType");
			attr(meta6, "content", "summary");
			attr(meta7, "name", "twitter:description");
			attr(meta7, "content", /*seo_description*/ ctx[1]);
			attr(meta8, "property", "og:type");
			attr(meta8, "content", "website");
			attr(meta9, "property", "og:title");
			attr(meta9, "content", /*seo_title*/ ctx[0]);
			attr(meta10, "property", "og:description");
			attr(meta10, "content", /*seo_description*/ ctx[1]);
			attr(meta11, "property", "og:url");
			attr(meta11, "content", "https://www.myconstructions.gr/");
			attr(meta12, "property", "og:locale");
			attr(meta12, "content", "el");
			attr(meta13, "property", "og:site_name");
			attr(meta13, "content", "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????");
			attr(link4, "rel", "icon");
			attr(link4, "href", "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/favicon.png");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, meta7);
			append_hydration(document.head, meta8);
			append_hydration(document.head, meta9);
			append_hydration(document.head, meta10);
			append_hydration(document.head, meta11);
			append_hydration(document.head, meta12);
			append_hydration(document.head, meta13);
			append_hydration(document.head, link4);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*seo_title*/ 1 && title_value !== (title_value = /*seo_title*/ ctx[0])) {
				document.title = title_value;
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta2, "content", /*seo_description*/ ctx[1]);
			}

			if (dirty & /*seo_title*/ 1) {
				attr(meta3, "content", /*seo_title*/ ctx[0]);
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta7, "content", /*seo_description*/ ctx[1]);
			}

			if (dirty & /*seo_title*/ 1) {
				attr(meta9, "content", /*seo_title*/ ctx[0]);
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta10, "content", /*seo_description*/ ctx[1]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(meta7);
			detach(meta8);
			detach(meta9);
			detach(meta10);
			detach(meta11);
			detach(meta12);
			detach(meta13);
			detach(link4);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(2, company = $$props.company);
		if ('address' in $$props) $$invalidate(3, address = $$props.address);
		if ('phone' in $$props) $$invalidate(4, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(5, email = $$props.email);
		if ('social' in $$props) $$invalidate(6, social = $$props.social);
		if ('nav' in $$props) $$invalidate(7, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(8, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(9, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(10, phone2 = $$props.phone2);
		if ('seo_title' in $$props) $$invalidate(0, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(1, seo_description = $$props.seo_description);
	};

	return [
		seo_title,
		seo_description,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			company: 2,
			address: 3,
			phone: 4,
			email: 5,
			social: 6,
			nav: 7,
			cta: 8,
			breadcrumbs: 9,
			phone2: 10,
			seo_title: 0,
			seo_description: 1
		});
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$1(ctx) {
	let div2;
	let div1;
	let div0;
	let video_1;
	let source;
	let source_src_value;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			video_1 = element("video");
			source = element("source");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			video_1 = claim_element(div0_nodes, "VIDEO", { class: true });
			var video_1_nodes = children(video_1);
			source = claim_element(video_1_nodes, "SOURCE", { src: true, type: true });
			video_1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(source.src, source_src_value = /*video*/ ctx[0])) attr(source, "src", source_src_value);
			attr(source, "type", "video/mp4");
			video_1.autoplay = true;
			video_1.muted = true;
			video_1.loop = true;
			attr(video_1, "class", "svelte-18ewb93");
			attr(div0, "class", "video-wrapper svelte-18ewb93");
			attr(div1, "class", "component");
			attr(div2, "class", "section has-component");
			attr(div2, "id", "jsdoj");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, video_1);
			append_hydration(video_1, source);
		},
		p(ctx, [dirty]) {
			if (dirty & /*video*/ 1 && !src_url_equal(source.src, source_src_value = /*video*/ ctx[0])) {
				attr(source, "src", source_src_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { video } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(1, company = $$props.company);
		if ('address' in $$props) $$invalidate(2, address = $$props.address);
		if ('phone' in $$props) $$invalidate(3, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(4, email = $$props.email);
		if ('social' in $$props) $$invalidate(5, social = $$props.social);
		if ('nav' in $$props) $$invalidate(6, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(7, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(8, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(9, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(10, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(11, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(12, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(13, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(14, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(15, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(16, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(17, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(18, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(19, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(20, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(21, seo_description = $$props.seo_description);
		if ('video' in $$props) $$invalidate(0, video = $$props.video);
	};

	return [
		video,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			company: 1,
			address: 2,
			phone: 3,
			email: 4,
			social: 5,
			nav: 6,
			cta: 7,
			breadcrumbs: 8,
			phone2: 9,
			cplgk: 10,
			jsdoj: 11,
			pfjyn: 12,
			klxal: 13,
			gxlkm: 14,
			nmtxv: 15,
			vqimh: 16,
			mkegn: 17,
			zecgs: 18,
			cxxvx: 19,
			seo_title: 20,
			seo_description: 21,
			video: 0
		});
	}
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const result = {
    attributes: {
      width: width.toString(),
      height: height.toString(),
      viewBox: box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString()
    },
    body
  };
  return result;
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + "$3");
  });
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToURL(svg) {
  return 'url("data:image/svg+xml,' + encodeSVGforURL(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url,
    width: fixSize(renderAttribs.width),
    height: fixSize(renderAttribs.height),
    ...commonProps,
    ...useMask ? monotoneProps : coloredProps
  };
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.55.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$2(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$2, safe_not_equal, {});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[25] = list[i];
	return child_ctx;
}

// (80:4) {#each social as s}
function create_each_block(ctx) {
	let a;
	let icon;
	let t;
	let a_href_value;
	let a_title_value;
	let current;

	icon = new Component$2({
			props: { icon: /*s*/ ctx[25].icon, height: "20" }
		});

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {
				href: true,
				title: true,
				target: true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*s*/ ctx[25].link);
			attr(a, "title", a_title_value = /*s*/ ctx[25].title);
			attr(a, "target", "_social");
			attr(a, "class", "svelte-3dvnpj");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 2) icon_changes.icon = /*s*/ ctx[25].icon;
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 2 && a_href_value !== (a_href_value = /*s*/ ctx[25].link)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social*/ 2 && a_title_value !== (a_title_value = /*s*/ ctx[25].title)) {
				attr(a, "title", a_title_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$3(ctx) {
	let div4;
	let div3;
	let section;
	let div2;
	let div0;
	let t0;
	let div1;
	let a0;
	let icon0;
	let span;
	let t1;
	let a0_href_value;
	let t2;
	let a1;
	let icon1;
	let a1_href_value;
	let current;
	let mounted;
	let dispose;
	let each_value = /*social*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	icon0 = new Component$2({
			props: { icon: "mdi:phone", height: "20" }
		});

	icon1 = new Component$2({ props: { icon: "mdi:at", height: "20" } });

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			section = element("section");
			div2 = element("div");
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			div1 = element("div");
			a0 = element("a");
			create_component(icon0.$$.fragment);
			span = element("span");
			t1 = text(/*phone*/ ctx[0]);
			t2 = space();
			a1 = element("a");
			create_component(icon1.$$.fragment);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { id: true, class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a0 = claim_element(div1_nodes, "A", { href: true, title: true, class: true });
			var a0_nodes = children(a0);
			claim_component(icon0.$$.fragment, a0_nodes);
			span = claim_element(a0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, /*phone*/ ctx[0]);
			span_nodes.forEach(detach);
			a0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);

			a1 = claim_element(div1_nodes, "A", {
				href: true,
				title: true,
				class: true,
				"data-name": true,
				"data-domain": true,
				"data-tld": true
			});

			var a1_nodes = children(a1);
			claim_component(icon1.$$.fragment, a1_nodes);
			a1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "social svelte-3dvnpj");
			attr(span, "class", "svelte-3dvnpj");
			attr(a0, "href", a0_href_value = "tel:" + /*phone*/ ctx[0].split(' ').join(''));
			attr(a0, "title", "?????????? ?????? ????????????????");
			attr(a0, "class", "svelte-3dvnpj");
			attr(a1, "href", a1_href_value = "#");
			attr(a1, "title", "?????????????? ?????? email");
			attr(a1, "class", "cryptedmail svelte-3dvnpj");
			attr(a1, "data-name", /*to*/ ctx[2]);
			attr(a1, "data-domain", /*domain*/ ctx[3]);
			attr(a1, "data-tld", /*tld*/ ctx[4]);
			attr(div1, "class", "info svelte-3dvnpj");
			attr(div2, "class", "section-container svelte-3dvnpj");
			attr(section, "id", "top-bar");
			attr(section, "class", "svelte-3dvnpj");
			attr(div3, "class", "component");
			attr(div4, "class", "section has-component");
			attr(div4, "id", "cplgk");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, section);
			append_hydration(section, div2);
			append_hydration(div2, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div0, null);
			}

			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, a0);
			mount_component(icon0, a0, null);
			append_hydration(a0, span);
			append_hydration(span, t1);
			append_hydration(div1, t2);
			append_hydration(div1, a1);
			mount_component(icon1, a1, null);
			current = true;

			if (!mounted) {
				dispose = listen(a1, "click", prevent_default(/*click_handler*/ ctx[24]));
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*social*/ 2) {
				each_value = /*social*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div0, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (!current || dirty & /*phone*/ 1) set_data(t1, /*phone*/ ctx[0]);

			if (!current || dirty & /*phone*/ 1 && a0_href_value !== (a0_href_value = "tel:" + /*phone*/ ctx[0].split(' ').join(''))) {
				attr(a0, "href", a0_href_value);
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_each(each_blocks, detaching);
			destroy_component(icon0);
			destroy_component(icon1);
			mounted = false;
			dispose();
		}
	};
}

function handleMailLink(e) {
	let el = e.target;
	window.open('mailto:' + el.dataset.name + '@' + el.dataset.domain + '.' + el.dataset.tld);
}

function instance$3($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	const [to, domain, tld] = [...email.split(/[@\.]/)];
	const click_handler = e => handleMailLink(e);

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(5, company = $$props.company);
		if ('address' in $$props) $$invalidate(6, address = $$props.address);
		if ('phone' in $$props) $$invalidate(0, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(7, email = $$props.email);
		if ('social' in $$props) $$invalidate(1, social = $$props.social);
		if ('nav' in $$props) $$invalidate(8, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(9, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(10, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(11, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(12, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(13, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(14, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(15, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(16, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(17, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(18, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(19, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(20, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(21, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(22, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(23, seo_description = $$props.seo_description);
	};

	return [
		phone,
		social,
		to,
		domain,
		tld,
		company,
		address,
		email,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description,
		click_handler
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			company: 5,
			address: 6,
			phone: 0,
			email: 7,
			social: 1,
			nav: 8,
			cta: 9,
			breadcrumbs: 10,
			phone2: 11,
			cplgk: 12,
			jsdoj: 13,
			pfjyn: 14,
			klxal: 15,
			gxlkm: 16,
			nmtxv: 17,
			vqimh: 18,
			mkegn: 19,
			zecgs: 20,
			cxxvx: 21,
			seo_title: 22,
			seo_description: 23
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.55.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[25] = list[i].link;
	child_ctx[27] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[25] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[25] = list[i].link;
	child_ctx[27] = i;
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[31] = list[i];
	return child_ctx;
}

function get_each_context_4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[34] = list[i];
	return child_ctx;
}

// (283:10) {#if item.submenu && item.submenu.length}
function create_if_block_1$1(ctx) {
	let ul;
	let each_value_4 = /*item*/ ctx[31].submenu;
	let each_blocks = [];

	for (let i = 0; i < each_value_4.length; i += 1) {
		each_blocks[i] = create_each_block_4(get_each_context_4(ctx, each_value_4, i));
	}

	return {
		c() {
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "submenu svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(ul, null);
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1) {
				each_value_4 = /*item*/ ctx[31].submenu;
				let i;

				for (i = 0; i < each_value_4.length; i += 1) {
					const child_ctx = get_each_context_4(ctx, each_value_4, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_4(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_4.length;
			}
		},
		d(detaching) {
			if (detaching) detach(ul);
			destroy_each(each_blocks, detaching);
		}
	};
}

// (285:10) {#each item.submenu as subitem}
function create_each_block_4(ctx) {
	let li;
	let a;
	let t0_value = /*subitem*/ ctx[34].sublink.label + "";
	let t0;
	let a_href_value;
	let t1;

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*subitem*/ ctx[34].sublink.url);
			attr(a, "class", "sublink svelte-194kat7");
			attr(li, "class", "svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1 && t0_value !== (t0_value = /*subitem*/ ctx[34].sublink.label + "")) set_data(t0, t0_value);

			if (dirty[0] & /*nav*/ 1 && a_href_value !== (a_href_value = /*subitem*/ ctx[34].sublink.url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (280:6) {#each nav as item}
function create_each_block_3(ctx) {
	let li;
	let a;
	let t0_value = /*item*/ ctx[31].link.label + "";
	let t0;
	let a_href_value;
	let t1;
	let t2;
	let if_block = /*item*/ ctx[31].submenu && /*item*/ ctx[31].submenu.length && create_if_block_1$1(ctx);

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			if (if_block) if_block.l(li_nodes);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*item*/ ctx[31].link.url);
			attr(a, "class", "link svelte-194kat7");
			attr(li, "class", "svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t2);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1 && t0_value !== (t0_value = /*item*/ ctx[31].link.label + "")) set_data(t0, t0_value);

			if (dirty[0] & /*nav*/ 1 && a_href_value !== (a_href_value = /*item*/ ctx[31].link.url)) {
				attr(a, "href", a_href_value);
			}

			if (/*item*/ ctx[31].submenu && /*item*/ ctx[31].submenu.length) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_1$1(ctx);
					if_block.c();
					if_block.m(li, t2);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
		}
	};
}

// (302:6) {#each cta as {link}
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[25].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[25].url);
			attr(a, "class", "button inverted svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*cta*/ 2 && t_value !== (t_value = /*link*/ ctx[25].label + "")) set_data(t, t_value);

			if (dirty[0] & /*cta*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[25].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (306:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav_1;
	let a;
	let svg0;
	let polygon0;
	let polyline0;
	let polyline1;
	let polyline2;
	let polygon1;
	let rect0;
	let path0;
	let path1;
	let path2;
	let path3;
	let path4;
	let path5;
	let path6;
	let path7;
	let path8;
	let rect1;
	let path9;
	let path10;
	let path11;
	let t0;
	let t1;
	let hr;
	let t2;
	let t3;
	let button;
	let svg1;
	let path12;
	let nav_1_transition;
	let current;
	let mounted;
	let dispose;
	let each_value_1 = /*nav*/ ctx[0];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let each_value = /*cta*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			nav_1 = element("nav");
			a = element("a");
			svg0 = svg_element("svg");
			polygon0 = svg_element("polygon");
			polyline0 = svg_element("polyline");
			polyline1 = svg_element("polyline");
			polyline2 = svg_element("polyline");
			polygon1 = svg_element("polygon");
			rect0 = svg_element("rect");
			path0 = svg_element("path");
			path1 = svg_element("path");
			path2 = svg_element("path");
			path3 = svg_element("path");
			path4 = svg_element("path");
			path5 = svg_element("path");
			path6 = svg_element("path");
			path7 = svg_element("path");
			path8 = svg_element("path");
			rect1 = svg_element("rect");
			path9 = svg_element("path");
			path10 = svg_element("path");
			path11 = svg_element("path");
			t0 = space();

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			hr = element("hr");
			t2 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			button = element("button");
			svg1 = svg_element("svg");
			path12 = svg_element("path");
			this.h();
		},
		l(nodes) {
			nav_1 = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_1_nodes = children(nav_1);
			a = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);

			svg0 = claim_svg_element(a_nodes, "svg", {
				viewBox: true,
				"xml:space": true,
				xmlns: true,
				class: true
			});

			var svg0_nodes = children(svg0);
			polygon0 = claim_svg_element(svg0_nodes, "polygon", { class: true, points: true });
			children(polygon0).forEach(detach);
			polyline0 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline0).forEach(detach);
			polyline1 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline1).forEach(detach);
			polyline2 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline2).forEach(detach);
			polygon1 = claim_svg_element(svg0_nodes, "polygon", { class: true, points: true });
			children(polygon1).forEach(detach);

			rect0 = claim_svg_element(svg0_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect0).forEach(detach);
			path0 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path0).forEach(detach);
			path1 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path1).forEach(detach);
			path2 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path2).forEach(detach);
			path3 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path3).forEach(detach);
			path4 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path4).forEach(detach);
			path5 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path5).forEach(detach);
			path6 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path6).forEach(detach);
			path7 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path7).forEach(detach);
			path8 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path8).forEach(detach);

			rect1 = claim_svg_element(svg0_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect1).forEach(detach);
			path9 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path9).forEach(detach);
			path10 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path10).forEach(detach);
			path11 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path11).forEach(detach);
			svg0_nodes.forEach(detach);
			a_nodes.forEach(detach);
			t0 = claim_space(nav_1_nodes);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_1_nodes);
			}

			t1 = claim_space(nav_1_nodes);
			hr = claim_element(nav_1_nodes, "HR", { class: true });
			t2 = claim_space(nav_1_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			t3 = claim_space(nav_1_nodes);

			button = claim_element(nav_1_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);

			svg1 = claim_svg_element(button_nodes, "svg", {
				xmlns: true,
				viewBox: true,
				fill: true,
				class: true
			});

			var svg1_nodes = children(svg1);

			path12 = claim_svg_element(svg1_nodes, "path", {
				fill: true,
				"fill-rule": true,
				d: true,
				"clip-rule": true
			});

			children(path12).forEach(detach);
			svg1_nodes.forEach(detach);
			button_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(polygon0, "class", "st0 svelte-194kat7");
			attr(polygon0, "points", "173 105.8 122.6 0.2 5 249.8 105.8 249.8");
			attr(polyline0, "class", "st0 svelte-194kat7");
			attr(polyline0, "points", "355.5 146.6 406.2 249.8 507 249.8 405.9 38.6");
			attr(polyline1, "class", "st1 svelte-194kat7");
			attr(polyline1, "points", "158.6 137 173 105.8 122.6 0.2");
			attr(polyline2, "class", "st1 svelte-194kat7");
			attr(polyline2, "points", "355.4 146.6 367.5 170.6 405.9 38.6 405.8 38.6");
			attr(polygon1, "class", "st2 svelte-194kat7");
			attr(polygon1, "points", "324.8 213 405.9 38.6 307.8 38.6 274.8 108 223.5 0.2 122.6 0.2 224.3 213.8 224.6 213.8 173.4 321.8 274.2 321.8 324.4 213.8 325.2 213.8");
			attr(rect0, "class", "st2 svelte-194kat7");
			attr(rect0, "x", "1436.9");
			attr(rect0, "y", "24.6");
			attr(rect0, "width", "25.4");
			attr(rect0, "height", "39.4");
			attr(path0, "class", "st0 svelte-194kat7");
			attr(path0, "d", "m625.8 69.3c-6.8 0-13.1 1.7-18.8 5.1-5.8 3.4-10.7 8.3-14.8 14.7s-7.3 14.4-9.6 23.8c-2.3 9.5-3.5 20.3-3.5 32.4s1.1 22.7 3.2 31.8 5.1 16.8 9.1 22.9c3.9 6.1 8.8 10.8 14.4 13.9 5.7 3.1 12.1 4.7 19.3 4.7 5.2 0 10.4-0.6 15.8-1.8s10.4-3 15.1-5.4v32.4c-4.8 2-9.9 3.7-15.4 4.8-5.5 1.2-11.2 1.8-17.2 1.8-11.6 0-21.7-2.5-30.5-7.4-8.8-5-16.1-12-22-21s-10.3-19.9-13.3-32.5-4.4-26.5-4.4-41.8c0-15.6 1.6-30.2 4.7-43.5 3.2-13.4 7.7-25 13.7-34.8s13.4-17.5 22.4-23.2c9-5.6 19.1-8.5 30.4-8.6 5.8 0 11.3 0.6 16.4 1.8 5.2 1.2 9.8 2.8 14 5v31.9c-5.4-2.6-10.5-4.3-15.2-5.4s-9.3-1.6-13.8-1.6z");
			attr(path1, "class", "st0 svelte-194kat7");
			attr(path1, "d", "m772.9 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7 2.2 9.6 3.4 20.2 3.4 31.9zm-25.1 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path2, "class", "st0 svelte-194kat7");
			attr(path2, "d", "m816.6 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path3, "class", "st0 svelte-194kat7");
			attr(path3, "d", "m954.1 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(path4, "class", "st0 svelte-194kat7");
			attr(path4, "d", "m1059.4 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.6v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(path5, "class", "st0 svelte-194kat7");
			attr(path5, "d", "m1137.1 126.8h-2c-7.4 0-13.9 1.7-19.6 5-5.6 3.3-10 8.4-13 15.3v99.5h-24.2v-148.6h20l2.2 20.7h0.4c2.9-7.6 6.8-13.5 11.8-17.9 5-4.3 11-6.5 18-6.5 2.5 0 4.6 0.2 6.3 0.6v31.9z");
			attr(path6, "class", "st0 svelte-194kat7");
			attr(path6, "d", "m1195.1 250.4c-9.9 0-18.2-2.5-24.7-7.6s-11.5-11.9-14.8-20.5c-1.8-4.6-3.1-9.7-3.9-15.2-0.9-5.5-1.3-11.7-1.3-18.4v-90.7h24.2v86.9c0 5 0.2 9.3 0.7 13 0.5 3.6 1.2 6.8 2.1 9.4 1.6 4.5 3.9 7.8 6.9 10s6.6 3.3 10.7 3.3c4.4 0 8.1-1.2 11.2-3.7s5.4-6.2 7-11.2c1.6-4.8 2.3-11.5 2.3-20.1v-87.6h24.2v90.8c0 12.1-1.4 22.2-4.2 30.5-1.6 4.7-3.6 9-6.1 12.8s-5.4 7.1-8.8 9.8-7.2 4.8-11.4 6.3c-4.1 1.5-8.9 2.2-14.1 2.2z");
			attr(path7, "class", "st0 svelte-194kat7");
			attr(path7, "d", "m1336.6 243.3c-3.1 1.9-6.8 3.6-11.2 5s-9.1 2.1-14 2.1c-7.1 0-13.8-1.5-20-4.6s-11.6-7.7-16.2-14c-4.6-6.2-8.3-14.1-10.9-23.7-2.7-9.6-4-20.7-4-33.5 0-14.3 1.5-26.6 4.6-36.8s7-18.5 11.9-24.9 10.3-11.1 16.4-14.1 12.1-4.5 18-4.5c4.4 0 8.7 0.6 12.8 1.8s7.8 2.8 11.1 4.8v29.6c-3-1.9-6.2-3.5-9.5-4.7-3.4-1.2-7-1.8-10.9-1.8s-7.6 0.9-11.1 2.7-6.7 4.6-9.4 8.5-4.9 9-6.5 15.4-2.4 14.1-2.4 23.1c0 6.5 0.6 12.7 1.8 18.5s3 10.7 5.4 14.8c2.3 4.1 5.3 7.4 9 9.9 3.6 2.5 7.9 3.8 12.9 3.8 4.4 0 8.4-0.7 12-2s7-3 10.2-4.9v29.5z");
			attr(path8, "class", "st0 svelte-194kat7");
			attr(path8, "d", "m1418 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.5v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(rect1, "class", "st0 svelte-194kat7");
			attr(rect1, "x", "1437.5");
			attr(rect1, "y", "98");
			attr(rect1, "width", "24.2");
			attr(rect1, "height", "148.6");
			attr(path9, "class", "st0 svelte-194kat7");
			attr(path9, "d", "m1583.2 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7s3.4 20.2 3.4 31.9zm-25 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path10, "class", "st0 svelte-194kat7");
			attr(path10, "d", "m1626.9 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path11, "class", "st0 svelte-194kat7");
			attr(path11, "d", "m1764.4 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(svg0, "viewBox", "0 0 1790 322");
			attr(svg0, "xml:space", "preserve");
			attr(svg0, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg0, "class", "svelte-194kat7");
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-194kat7");
			attr(hr, "class", "svelte-194kat7");
			attr(path12, "fill", "currentColor");
			attr(path12, "fill-rule", "evenodd");
			attr(path12, "d", "M4.293 4.293a1 1 0 011.414 0L10 8.586l4.293-4.293a1 1 0 111.414 1.414L11.414 10l4.293 4.293a1 1 0 01-1.414 1.414L10 11.414l-4.293 4.293a1 1 0 01-1.414-1.414L8.586 10 4.293 5.707a1 1 0 010-1.414z");
			attr(path12, "clip-rule", "evenodd");
			attr(svg1, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg1, "viewBox", "0 0 20 20");
			attr(svg1, "fill", "currentColor");
			attr(svg1, "class", "svelte-194kat7");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-194kat7");
			attr(nav_1, "id", "mobile-nav");
			attr(nav_1, "class", "svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, nav_1, anchor);
			append_hydration(nav_1, a);
			append_hydration(a, svg0);
			append_hydration(svg0, polygon0);
			append_hydration(svg0, polyline0);
			append_hydration(svg0, polyline1);
			append_hydration(svg0, polyline2);
			append_hydration(svg0, polygon1);
			append_hydration(svg0, rect0);
			append_hydration(svg0, path0);
			append_hydration(svg0, path1);
			append_hydration(svg0, path2);
			append_hydration(svg0, path3);
			append_hydration(svg0, path4);
			append_hydration(svg0, path5);
			append_hydration(svg0, path6);
			append_hydration(svg0, path7);
			append_hydration(svg0, path8);
			append_hydration(svg0, rect1);
			append_hydration(svg0, path9);
			append_hydration(svg0, path10);
			append_hydration(svg0, path11);
			append_hydration(nav_1, t0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].m(nav_1, null);
			}

			append_hydration(nav_1, t1);
			append_hydration(nav_1, hr);
			append_hydration(nav_1, t2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(nav_1, null);
			}

			append_hydration(nav_1, t3);
			append_hydration(nav_1, button);
			append_hydration(button, svg1);
			append_hydration(svg1, path12);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[23]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1) {
				each_value_1 = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav_1, t1);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty[0] & /*cta*/ 2) {
				each_value = /*cta*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, t3);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, true);
				nav_1_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, false);
			nav_1_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav_1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			if (detaching && nav_1_transition) nav_1_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (331:6) {#each nav as {link}}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[25].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[25].url);
			attr(a, "class", "link svelte-194kat7");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1 && t_value !== (t_value = /*link*/ ctx[25].label + "")) set_data(t, t_value);

			if (dirty[0] & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[25].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (335:6) {#each cta as {link}
function create_each_block$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[25].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[25].url);
			attr(a, "class", "svelte-194kat7");
			toggle_class(a, "button", /*cta*/ ctx[1].length - 1 === /*i*/ ctx[27]);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*cta*/ 2 && t_value !== (t_value = /*link*/ ctx[25].label + "")) set_data(t, t_value);

			if (dirty[0] & /*cta*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[25].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty[0] & /*cta*/ 2) {
				toggle_class(a, "button", /*cta*/ ctx[1].length - 1 === /*i*/ ctx[27]);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$4(ctx) {
	let div3;
	let div2;
	let header;
	let div1;
	let nav_1;
	let a;
	let svg0;
	let polygon0;
	let polyline0;
	let polyline1;
	let polyline2;
	let polygon1;
	let rect0;
	let path0;
	let path1;
	let path2;
	let path3;
	let path4;
	let path5;
	let path6;
	let path7;
	let path8;
	let rect1;
	let path9;
	let path10;
	let path11;
	let t0;
	let ul;
	let t1;
	let div0;
	let button;
	let svg1;
	let path12;
	let t2;
	let t3;
	let current;
	let mounted;
	let dispose;
	let each_value_3 = /*nav*/ ctx[0];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks_1[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	let each_value_2 = /*cta*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let if_block = /*mobileNavOpen*/ ctx[2] && create_if_block$1(ctx);

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			header = element("header");
			div1 = element("div");
			nav_1 = element("nav");
			a = element("a");
			svg0 = svg_element("svg");
			polygon0 = svg_element("polygon");
			polyline0 = svg_element("polyline");
			polyline1 = svg_element("polyline");
			polyline2 = svg_element("polyline");
			polygon1 = svg_element("polygon");
			rect0 = svg_element("rect");
			path0 = svg_element("path");
			path1 = svg_element("path");
			path2 = svg_element("path");
			path3 = svg_element("path");
			path4 = svg_element("path");
			path5 = svg_element("path");
			path6 = svg_element("path");
			path7 = svg_element("path");
			path8 = svg_element("path");
			rect1 = svg_element("rect");
			path9 = svg_element("path");
			path10 = svg_element("path");
			path11 = svg_element("path");
			t0 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			div0 = element("div");
			button = element("button");
			svg1 = svg_element("svg");
			path12 = svg_element("path");
			t2 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { id: true, class: true });
			var header_nodes = children(header);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			nav_1 = claim_element(div1_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);
			a = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);

			svg0 = claim_svg_element(a_nodes, "svg", {
				viewBox: true,
				"xml:space": true,
				xmlns: true,
				class: true
			});

			var svg0_nodes = children(svg0);
			polygon0 = claim_svg_element(svg0_nodes, "polygon", { class: true, points: true });
			children(polygon0).forEach(detach);
			polyline0 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline0).forEach(detach);
			polyline1 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline1).forEach(detach);
			polyline2 = claim_svg_element(svg0_nodes, "polyline", { class: true, points: true });
			children(polyline2).forEach(detach);
			polygon1 = claim_svg_element(svg0_nodes, "polygon", { class: true, points: true });
			children(polygon1).forEach(detach);

			rect0 = claim_svg_element(svg0_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect0).forEach(detach);
			path0 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path0).forEach(detach);
			path1 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path1).forEach(detach);
			path2 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path2).forEach(detach);
			path3 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path3).forEach(detach);
			path4 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path4).forEach(detach);
			path5 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path5).forEach(detach);
			path6 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path6).forEach(detach);
			path7 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path7).forEach(detach);
			path8 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path8).forEach(detach);

			rect1 = claim_svg_element(svg0_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect1).forEach(detach);
			path9 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path9).forEach(detach);
			path10 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path10).forEach(detach);
			path11 = claim_svg_element(svg0_nodes, "path", { class: true, d: true });
			children(path11).forEach(detach);
			svg0_nodes.forEach(detach);
			a_nodes.forEach(detach);
			t0 = claim_space(nav_1_nodes);
			ul = claim_element(nav_1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			button = claim_element(div0_nodes, "BUTTON", {
				id: true,
				title: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);

			svg1 = claim_svg_element(button_nodes, "svg", {
				width: true,
				height: true,
				viewBox: true,
				xmlns: true,
				class: true
			});

			var svg1_nodes = children(svg1);
			path12 = claim_svg_element(svg1_nodes, "path", { d: true });
			children(path12).forEach(detach);
			svg1_nodes.forEach(detach);
			button_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(polygon0, "class", "st0 svelte-194kat7");
			attr(polygon0, "points", "173 105.8 122.6 0.2 5 249.8 105.8 249.8");
			attr(polyline0, "class", "st0 svelte-194kat7");
			attr(polyline0, "points", "355.5 146.6 406.2 249.8 507 249.8 405.9 38.6");
			attr(polyline1, "class", "st1 svelte-194kat7");
			attr(polyline1, "points", "158.6 137 173 105.8 122.6 0.2");
			attr(polyline2, "class", "st1 svelte-194kat7");
			attr(polyline2, "points", "355.4 146.6 367.5 170.6 405.9 38.6 405.8 38.6");
			attr(polygon1, "class", "st2 svelte-194kat7");
			attr(polygon1, "points", "324.8 213 405.9 38.6 307.8 38.6 274.8 108 223.5 0.2 122.6 0.2 224.3 213.8 224.6 213.8 173.4 321.8 274.2 321.8 324.4 213.8 325.2 213.8");
			attr(rect0, "class", "st2 svelte-194kat7");
			attr(rect0, "x", "1436.9");
			attr(rect0, "y", "24.6");
			attr(rect0, "width", "25.4");
			attr(rect0, "height", "39.4");
			attr(path0, "class", "st0 svelte-194kat7");
			attr(path0, "d", "m625.8 69.3c-6.8 0-13.1 1.7-18.8 5.1-5.8 3.4-10.7 8.3-14.8 14.7s-7.3 14.4-9.6 23.8c-2.3 9.5-3.5 20.3-3.5 32.4s1.1 22.7 3.2 31.8 5.1 16.8 9.1 22.9c3.9 6.1 8.8 10.8 14.4 13.9 5.7 3.1 12.1 4.7 19.3 4.7 5.2 0 10.4-0.6 15.8-1.8s10.4-3 15.1-5.4v32.4c-4.8 2-9.9 3.7-15.4 4.8-5.5 1.2-11.2 1.8-17.2 1.8-11.6 0-21.7-2.5-30.5-7.4-8.8-5-16.1-12-22-21s-10.3-19.9-13.3-32.5-4.4-26.5-4.4-41.8c0-15.6 1.6-30.2 4.7-43.5 3.2-13.4 7.7-25 13.7-34.8s13.4-17.5 22.4-23.2c9-5.6 19.1-8.5 30.4-8.6 5.8 0 11.3 0.6 16.4 1.8 5.2 1.2 9.8 2.8 14 5v31.9c-5.4-2.6-10.5-4.3-15.2-5.4s-9.3-1.6-13.8-1.6z");
			attr(path1, "class", "st0 svelte-194kat7");
			attr(path1, "d", "m772.9 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7 2.2 9.6 3.4 20.2 3.4 31.9zm-25.1 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path2, "class", "st0 svelte-194kat7");
			attr(path2, "d", "m816.6 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path3, "class", "st0 svelte-194kat7");
			attr(path3, "d", "m954.1 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(path4, "class", "st0 svelte-194kat7");
			attr(path4, "d", "m1059.4 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.6v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(path5, "class", "st0 svelte-194kat7");
			attr(path5, "d", "m1137.1 126.8h-2c-7.4 0-13.9 1.7-19.6 5-5.6 3.3-10 8.4-13 15.3v99.5h-24.2v-148.6h20l2.2 20.7h0.4c2.9-7.6 6.8-13.5 11.8-17.9 5-4.3 11-6.5 18-6.5 2.5 0 4.6 0.2 6.3 0.6v31.9z");
			attr(path6, "class", "st0 svelte-194kat7");
			attr(path6, "d", "m1195.1 250.4c-9.9 0-18.2-2.5-24.7-7.6s-11.5-11.9-14.8-20.5c-1.8-4.6-3.1-9.7-3.9-15.2-0.9-5.5-1.3-11.7-1.3-18.4v-90.7h24.2v86.9c0 5 0.2 9.3 0.7 13 0.5 3.6 1.2 6.8 2.1 9.4 1.6 4.5 3.9 7.8 6.9 10s6.6 3.3 10.7 3.3c4.4 0 8.1-1.2 11.2-3.7s5.4-6.2 7-11.2c1.6-4.8 2.3-11.5 2.3-20.1v-87.6h24.2v90.8c0 12.1-1.4 22.2-4.2 30.5-1.6 4.7-3.6 9-6.1 12.8s-5.4 7.1-8.8 9.8-7.2 4.8-11.4 6.3c-4.1 1.5-8.9 2.2-14.1 2.2z");
			attr(path7, "class", "st0 svelte-194kat7");
			attr(path7, "d", "m1336.6 243.3c-3.1 1.9-6.8 3.6-11.2 5s-9.1 2.1-14 2.1c-7.1 0-13.8-1.5-20-4.6s-11.6-7.7-16.2-14c-4.6-6.2-8.3-14.1-10.9-23.7-2.7-9.6-4-20.7-4-33.5 0-14.3 1.5-26.6 4.6-36.8s7-18.5 11.9-24.9 10.3-11.1 16.4-14.1 12.1-4.5 18-4.5c4.4 0 8.7 0.6 12.8 1.8s7.8 2.8 11.1 4.8v29.6c-3-1.9-6.2-3.5-9.5-4.7-3.4-1.2-7-1.8-10.9-1.8s-7.6 0.9-11.1 2.7-6.7 4.6-9.4 8.5-4.9 9-6.5 15.4-2.4 14.1-2.4 23.1c0 6.5 0.6 12.7 1.8 18.5s3 10.7 5.4 14.8c2.3 4.1 5.3 7.4 9 9.9 3.6 2.5 7.9 3.8 12.9 3.8 4.4 0 8.4-0.7 12-2s7-3 10.2-4.9v29.5z");
			attr(path8, "class", "st0 svelte-194kat7");
			attr(path8, "d", "m1418 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.5v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(rect1, "class", "st0 svelte-194kat7");
			attr(rect1, "x", "1437.5");
			attr(rect1, "y", "98");
			attr(rect1, "width", "24.2");
			attr(rect1, "height", "148.6");
			attr(path9, "class", "st0 svelte-194kat7");
			attr(path9, "d", "m1583.2 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7s3.4 20.2 3.4 31.9zm-25 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path10, "class", "st0 svelte-194kat7");
			attr(path10, "d", "m1626.9 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path11, "class", "st0 svelte-194kat7");
			attr(path11, "d", "m1764.4 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(svg0, "viewBox", "0 0 1790 322");
			attr(svg0, "xml:space", "preserve");
			attr(svg0, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg0, "class", "svelte-194kat7");
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-194kat7");
			attr(ul, "class", "svelte-194kat7");
			attr(nav_1, "class", "svelte-194kat7");
			attr(path12, "d", "M19.4643 17.0213H0.535714C0.239866 17.0213 0 17.3071 0 17.6596V19.3617C0 19.7142 0.239866 20 0.535714 20H19.4643C19.7601 20 20 19.7142 20 19.3617V17.6596C20 17.3071 19.7601 17.0213 19.4643 17.0213ZM19.4643 8.51064H0.535714C0.239866 8.51064 0 8.79644 0 9.14894V10.8511C0 11.2036 0.239866 11.4894 0.535714 11.4894H19.4643C19.7601 11.4894 20 11.2036 20 10.8511V9.14894C20 8.79644 19.7601 8.51064 19.4643 8.51064ZM19.4643 0H0.535714C0.239866 0 0 0.285797 0 0.638296V2.34042C0 2.69292 0.239866 2.97872 0.535714 2.97872H19.4643C19.7601 2.97872 20 2.69292 20 2.34042V0.638296C20 0.285797 19.7601 0 19.4643 0Z");
			attr(svg1, "width", "20");
			attr(svg1, "height", "20");
			attr(svg1, "viewBox", "0 0 20 20");
			attr(svg1, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg1, "class", "svelte-194kat7");
			attr(button, "id", "open");
			attr(button, "title", "Menu");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-194kat7");
			attr(div0, "class", "call-to-action svelte-194kat7");
			attr(div1, "class", "section-container svelte-194kat7");
			attr(header, "id", "nav");
			attr(header, "class", "svelte-194kat7");
			toggle_class(header, "stuck", stuck);
			attr(div2, "class", "component");
			attr(div3, "class", "section has-component");
			attr(div3, "id", "klxal");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, header);
			append_hydration(header, div1);
			append_hydration(div1, nav_1);
			append_hydration(nav_1, a);
			append_hydration(a, svg0);
			append_hydration(svg0, polygon0);
			append_hydration(svg0, polyline0);
			append_hydration(svg0, polyline1);
			append_hydration(svg0, polyline2);
			append_hydration(svg0, polygon1);
			append_hydration(svg0, rect0);
			append_hydration(svg0, path0);
			append_hydration(svg0, path1);
			append_hydration(svg0, path2);
			append_hydration(svg0, path3);
			append_hydration(svg0, path4);
			append_hydration(svg0, path5);
			append_hydration(svg0, path6);
			append_hydration(svg0, path7);
			append_hydration(svg0, path8);
			append_hydration(svg0, rect1);
			append_hydration(svg0, path9);
			append_hydration(svg0, path10);
			append_hydration(svg0, path11);
			append_hydration(nav_1, t0);
			append_hydration(nav_1, ul);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].m(ul, null);
			}

			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, button);
			append_hydration(button, svg1);
			append_hydration(svg1, path12);
			append_hydration(div0, t2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div0, null);
			}

			append_hydration(div1, t3);
			if (if_block) if_block.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[22]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 1) {
				each_value_3 = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_3(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(ul, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_3.length;
			}

			if (dirty[0] & /*cta*/ 2) {
				each_value_2 = /*cta*/ ctx[1];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_2.length;
			}

			if (/*mobileNavOpen*/ ctx[2]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty[0] & /*mobileNavOpen*/ 4) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div1, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

let stuck = false;

function instance$4($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let mobileNavOpen = false;

	onMount(async () => {
		// toggle stuck class when sticky
		const observer = new IntersectionObserver(([e]) => e.target.classList.toggle('stuck', e.intersectionRatio < 1), { threshold: [1] });

		observer.observe(document.querySelector('header#nav'));

		// fix submenu z-index
		document.querySelector('header#nav').closest('div.primo-section').style.zIndex = 10;

		document.querySelector('header#nav').closest('div.primo-section').style.position = 'relative';
	});

	const click_handler = () => $$invalidate(2, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(2, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(3, company = $$props.company);
		if ('address' in $$props) $$invalidate(4, address = $$props.address);
		if ('phone' in $$props) $$invalidate(5, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(6, email = $$props.email);
		if ('social' in $$props) $$invalidate(7, social = $$props.social);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(1, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(8, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(9, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(10, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(11, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(12, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(13, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(14, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(15, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(16, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(17, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(18, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(19, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(20, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(21, seo_description = $$props.seo_description);
	};

	return [
		nav,
		cta,
		mobileNavOpen,
		company,
		address,
		phone,
		email,
		social,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description,
		click_handler,
		click_handler_1
	];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(
			this,
			options,
			instance$4,
			create_fragment$4,
			safe_not_equal,
			{
				company: 3,
				address: 4,
				phone: 5,
				email: 6,
				social: 7,
				nav: 0,
				cta: 1,
				breadcrumbs: 8,
				phone2: 9,
				cplgk: 10,
				jsdoj: 11,
				pfjyn: 12,
				klxal: 13,
				gxlkm: 14,
				nmtxv: 15,
				vqimh: 16,
				mkegn: 17,
				zecgs: 18,
				cxxvx: 19,
				seo_title: 20,
				seo_description: 21
			},
			null,
			[-1, -1]
		);
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$5(ctx) {
	let div2;
	let div1;
	let div0;
	let svg;
	let polygon0;
	let polyline0;
	let polygon1;
	let polyline1;
	let polyline2;
	let t0;
	let h1;
	let t1;
	let t2;
	let h2;
	let t3;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			svg = svg_element("svg");
			polygon0 = svg_element("polygon");
			polyline0 = svg_element("polyline");
			polygon1 = svg_element("polygon");
			polyline1 = svg_element("polyline");
			polyline2 = svg_element("polyline");
			t0 = space();
			h1 = element("h1");
			t1 = text(/*title*/ ctx[0]);
			t2 = space();
			h2 = element("h2");
			t3 = text(/*text*/ ctx[1]);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			svg = claim_svg_element(div0_nodes, "svg", {
				version: true,
				viewBox: true,
				"xml:space": true,
				xmlns: true,
				class: true
			});

			var svg_nodes = children(svg);
			polygon0 = claim_svg_element(svg_nodes, "polygon", { class: true, points: true });
			children(polygon0).forEach(detach);
			polyline0 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline0).forEach(detach);
			polygon1 = claim_svg_element(svg_nodes, "polygon", { class: true, points: true });
			children(polygon1).forEach(detach);
			polyline1 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline1).forEach(detach);
			polyline2 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline2).forEach(detach);
			svg_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			h1 = claim_element(div0_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t1 = claim_text(h1_nodes, /*title*/ ctx[0]);
			h1_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t3 = claim_text(h2_nodes, /*text*/ ctx[1]);
			h2_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(polygon0, "class", "st0 svelte-11ryedj");
			attr(polygon0, "points", "167 104.8 116.6 -0.8 -1 248.8 99.8 248.8");
			attr(polyline0, "class", "st0 svelte-11ryedj");
			attr(polyline0, "points", "349.5 145.6 400.2 248.8 501 248.8 399.9 37.6");
			attr(polygon1, "class", "st1 svelte-11ryedj");
			attr(polygon1, "points", "318.8 212 399.9 37.6 301.8 37.6 268.8 107 217.5 -0.8 116.6 -0.8 218.3 212.8 218.6 212.8 167.4 320.8 268.2 320.8 318.4 212.8 319.2 212.8");
			attr(polyline1, "class", "st2 svelte-11ryedj");
			attr(polyline1, "points", "152.6 136 167 104.8 116.6 -0.8");
			attr(polyline2, "class", "st2 svelte-11ryedj");
			attr(polyline2, "points", "349.4 145.6 361.5 169.6 399.9 37.6 399.8 37.6");
			attr(svg, "version", "1.1");
			attr(svg, "viewBox", "0 0 502 321");
			attr(svg, "xml:space", "preserve");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "class", "svelte-11ryedj");
			attr(h1, "class", "svelte-11ryedj");
			attr(h2, "class", "svelte-11ryedj");
			attr(div0, "class", "wrapper svelte-11ryedj");
			attr(div1, "class", "component");
			attr(div2, "class", "section has-component");
			attr(div2, "id", "pfjyn");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			append_hydration(div0, svg);
			append_hydration(svg, polygon0);
			append_hydration(svg, polyline0);
			append_hydration(svg, polygon1);
			append_hydration(svg, polyline1);
			append_hydration(svg, polyline2);
			append_hydration(div0, t0);
			append_hydration(div0, h1);
			append_hydration(h1, t1);
			append_hydration(div0, t2);
			append_hydration(div0, h2);
			append_hydration(h2, t3);
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 1) set_data(t1, /*title*/ ctx[0]);
			if (dirty & /*text*/ 2) set_data(t3, /*text*/ ctx[1]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { title } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(2, company = $$props.company);
		if ('address' in $$props) $$invalidate(3, address = $$props.address);
		if ('phone' in $$props) $$invalidate(4, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(5, email = $$props.email);
		if ('social' in $$props) $$invalidate(6, social = $$props.social);
		if ('nav' in $$props) $$invalidate(7, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(8, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(9, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(10, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(11, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(12, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(13, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(14, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(15, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(16, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(17, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(18, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(19, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(20, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(21, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(22, seo_description = $$props.seo_description);
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('text' in $$props) $$invalidate(1, text = $$props.text);
	};

	return [
		title,
		text,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			company: 2,
			address: 3,
			phone: 4,
			email: 5,
			social: 6,
			nav: 7,
			cta: 8,
			breadcrumbs: 9,
			phone2: 10,
			cplgk: 11,
			jsdoj: 12,
			pfjyn: 13,
			klxal: 14,
			gxlkm: 15,
			nmtxv: 16,
			vqimh: 17,
			mkegn: 18,
			zecgs: 19,
			cxxvx: 20,
			seo_title: 21,
			seo_description: 22,
			title: 0,
			text: 1
		});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[24] = list[i];
	return child_ctx;
}

// (119:6) {#if person.image.url}
function create_if_block$2(ctx) {
	let figure;
	let img;
	let img_alt_value;
	let img_src_value;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { alt: true, src: true, class: true });
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "alt", img_alt_value = /*person*/ ctx[24].image.alt);
			if (!src_url_equal(img.src, img_src_value = /*person*/ ctx[24].image.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-lwygok");
			attr(figure, "class", "svelte-lwygok");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
		},
		p(ctx, dirty) {
			if (dirty & /*people*/ 2 && img_alt_value !== (img_alt_value = /*person*/ ctx[24].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*people*/ 2 && !src_url_equal(img.src, img_src_value = /*person*/ ctx[24].image.url)) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(figure);
		}
	};
}

// (117:4) {#each people as person}
function create_each_block$2(ctx) {
	let li;
	let t0;
	let div1;
	let div0;
	let span0;
	let t1_value = /*person*/ ctx[24].name + "";
	let t1;
	let t2;
	let span1;
	let t3_value = /*person*/ ctx[24].title + "";
	let t3;
	let t4;
	let if_block = /*person*/ ctx[24].image.url && create_if_block$2(ctx);

	return {
		c() {
			li = element("li");
			if (if_block) if_block.c();
			t0 = space();
			div1 = element("div");
			div0 = element("div");
			span0 = element("span");
			t1 = text(t1_value);
			t2 = space();
			span1 = element("span");
			t3 = text(t3_value);
			t4 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			if (if_block) if_block.l(li_nodes);
			t0 = claim_space(li_nodes);
			div1 = claim_element(li_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			span0 = claim_element(div0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t1 = claim_text(span0_nodes, t1_value);
			span0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			span1 = claim_element(div0_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t3 = claim_text(span1_nodes, t3_value);
			span1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t4 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "svelte-lwygok");
			attr(span1, "class", "svelte-lwygok");
			attr(div0, "class", "details svelte-lwygok");
			attr(div1, "class", "info svelte-lwygok");
			attr(li, "class", "svelte-lwygok");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t0);
			append_hydration(li, div1);
			append_hydration(div1, div0);
			append_hydration(div0, span0);
			append_hydration(span0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, span1);
			append_hydration(span1, t3);
			append_hydration(li, t4);
		},
		p(ctx, dirty) {
			if (/*person*/ ctx[24].image.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					if_block.m(li, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (dirty & /*people*/ 2 && t1_value !== (t1_value = /*person*/ ctx[24].name + "")) set_data(t1, t1_value);
			if (dirty & /*people*/ 2 && t3_value !== (t3_value = /*person*/ ctx[24].title + "")) set_data(t3, t3_value);
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$6(ctx) {
	let div1;
	let div0;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let section;
	let h2;
	let t1;
	let t2;
	let ul;
	let each_value = /*people*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			img = element("img");
			t0 = space();
			section = element("section");
			h2 = element("h2");
			t1 = text(/*heading*/ ctx[0]);
			t2 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			img = claim_element(div0_nodes, "IMG", {
				id: true,
				src: true,
				alt: true,
				class: true
			});

			t0 = claim_space(div0_nodes);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "id", "services-bg");
			if (!src_url_equal(img.src, img_src_value = /*bg*/ ctx[2].src)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*bg*/ ctx[2].alt);
			attr(img, "class", "svelte-lwygok");
			attr(h2, "class", "heading svelte-lwygok");
			attr(ul, "class", "svelte-lwygok");
			attr(section, "class", "section-container svelte-lwygok");
			attr(div0, "class", "component");
			attr(div1, "class", "section has-component");
			attr(div1, "id", "gxlkm");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, img);
			append_hydration(div0, t0);
			append_hydration(div0, section);
			append_hydration(section, h2);
			append_hydration(h2, t1);
			append_hydration(section, t2);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(ul, null);
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*bg*/ 4 && !src_url_equal(img.src, img_src_value = /*bg*/ ctx[2].src)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*bg*/ 4 && img_alt_value !== (img_alt_value = /*bg*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*heading*/ 1) set_data(t1, /*heading*/ ctx[0]);

			if (dirty & /*people*/ 2) {
				each_value = /*people*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { heading } = $$props;
	let { people } = $$props;
	let { bg } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(3, company = $$props.company);
		if ('address' in $$props) $$invalidate(4, address = $$props.address);
		if ('phone' in $$props) $$invalidate(5, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(6, email = $$props.email);
		if ('social' in $$props) $$invalidate(7, social = $$props.social);
		if ('nav' in $$props) $$invalidate(8, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(9, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(10, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(11, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(12, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(13, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(14, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(15, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(16, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(17, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(18, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(19, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(20, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(21, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(22, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(23, seo_description = $$props.seo_description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('people' in $$props) $$invalidate(1, people = $$props.people);
		if ('bg' in $$props) $$invalidate(2, bg = $$props.bg);
	};

	return [
		heading,
		people,
		bg,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			company: 3,
			address: 4,
			phone: 5,
			email: 6,
			social: 7,
			nav: 8,
			cta: 9,
			breadcrumbs: 10,
			phone2: 11,
			cplgk: 12,
			jsdoj: 13,
			pfjyn: 14,
			klxal: 15,
			gxlkm: 16,
			nmtxv: 17,
			vqimh: 18,
			mkegn: 19,
			zecgs: 20,
			cxxvx: 21,
			seo_title: 22,
			seo_description: 23,
			heading: 0,
			people: 1,
			bg: 2
		});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[32] = list[i];
	return child_ctx;
}

// (213:4) {#each items as item}
function create_each_block$3(ctx) {
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let t0;
	let figcaption;
	let span;
	let t1_value = /*item*/ ctx[32].img.alt + "";
	let t1;
	let t2;
	let figure_intro;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			t0 = space();
			figcaption = element("figcaption");
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { src: true, alt: true, class: true });
			t0 = claim_space(figure_nodes);
			figcaption = claim_element(figure_nodes, "FIGCAPTION", { class: true });
			var figcaption_nodes = children(figcaption);
			span = claim_element(figcaption_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			figcaption_nodes.forEach(detach);
			t2 = claim_space(figure_nodes);
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[32].img.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*item*/ ctx[32].img.atl);
			attr(img, "class", "svelte-diacqi");
			attr(span, "class", "svelte-diacqi");
			attr(figcaption, "class", "svelte-diacqi");
			attr(figure, "class", "svelte-diacqi");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
			append_hydration(figure, t0);
			append_hydration(figure, figcaption);
			append_hydration(figcaption, span);
			append_hydration(span, t1);
			append_hydration(figure, t2);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*items*/ 2 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[32].img.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty[0] & /*items*/ 2 && img_alt_value !== (img_alt_value = /*item*/ ctx[32].img.atl)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty[0] & /*items*/ 2 && t1_value !== (t1_value = /*item*/ ctx[32].img.alt + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (!figure_intro) {
				add_render_callback(() => {
					figure_intro = create_in_transition(figure, fade, { duration: 200 });
					figure_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(figure);
		}
	};
}

function create_fragment$7(ctx) {
	let div4;
	let div3;
	let section;
	let div1;
	let h3;
	let t0;
	let t1;
	let div0;
	let button0;
	let t2;
	let t3;
	let button1;
	let t4;
	let t5;
	let div2;
	let mounted;
	let dispose;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$3(get_each_context$3(ctx, each_value, i));
	}

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			section = element("section");
			div1 = element("div");
			h3 = element("h3");
			t0 = text(/*title*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			button0 = element("button");
			t2 = text("<");
			t3 = space();
			button1 = element("button");
			t4 = text(">");
			t5 = space();
			div2 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			section = claim_element(div3_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h3 = claim_element(div1_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			button0 = claim_element(div0_nodes, "BUTTON", { title: true, class: true });
			var button0_nodes = children(button0);
			t2 = claim_text(button0_nodes, "<");
			button0_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			button1 = claim_element(div0_nodes, "BUTTON", { title: true, class: true });
			var button1_nodes = children(button1);
			t4 = claim_text(button1_nodes, ">");
			button1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			div2 = claim_element(section_nodes, "DIV", { class: true, style: true });
			var div2_nodes = children(div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-diacqi");
			attr(button0, "title", "???????????? ????????????????");
			attr(button0, "class", "svelte-diacqi");
			attr(button1, "title", "???????????? ??????????");
			attr(button1, "class", "svelte-diacqi");
			attr(div0, "class", "controls svelte-diacqi");
			attr(div1, "class", "section-container svelte-diacqi");
			attr(div2, "class", "items svelte-diacqi");
			set_style(div2, "margin-left", "calc(" + /*position*/ ctx[2] + "vw - " + /*gap*/ ctx[3] + "rem)");
			attr(section, "class", "svelte-diacqi");
			attr(div3, "class", "component");
			attr(div4, "class", "section has-component");
			attr(div4, "id", "nmtxv");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, section);
			append_hydration(section, div1);
			append_hydration(div1, h3);
			append_hydration(h3, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, button0);
			append_hydration(button0, t2);
			append_hydration(div0, t3);
			append_hydration(div0, button1);
			append_hydration(button1, t4);
			append_hydration(section, t5);
			append_hydration(section, div2);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div2, null);
			}

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*slideLeft*/ ctx[4]),
					listen(button1, "click", /*slideRight*/ ctx[5])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*title*/ 1) set_data(t0, /*title*/ ctx[0]);

			if (dirty[0] & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$3(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div2, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty[0] & /*position, gap*/ 12) {
				set_style(div2, "margin-left", "calc(" + /*position*/ ctx[2] + "vw - " + /*gap*/ ctx[3] + "rem)");
			}
		},
		i(local) {
			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { title } = $$props;
	let { items } = $$props;
	let position = 0;
	let perPage = 1;
	let gap = 0;
	let trueGap = 1;
	let totalItems = 1;

	let slideLeft = () => {
		if (position > -((totalItems - 1) * (100 / perPage))) {
			$$invalidate(2, position -= 100 / perPage);
			$$invalidate(3, gap = position < 0 ? gap + trueGap / perPage : 0);
		}
	};

	let slideRight = () => {
		if (position < 0) $$invalidate(2, position += 100 / perPage);
		$$invalidate(3, gap = position < 0 ? gap - trueGap / perPage : 0);
	};

	onMount(async () => {
		window.onresize = () => {
			$$invalidate(2, position = 0);
			$$invalidate(3, gap = 0);
			calcDimensions();
		};

		totalItems = document.querySelectorAll('.items > figure').length;
		calcDimensions();
	});

	function calcDimensions() {
		switch (true) {
			case innerWidth >= 1200:
				trueGap = 3;
				perPage = 4;
				break;
			case innerWidth >= 900:
				perPage = 3;
				break;
			case innerWidth >= 600:
				trueGap = 2;
				perPage = 2;
				break;
			default:
				trueGap = 1;
				perPage = 1;
		}
	}

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(6, company = $$props.company);
		if ('address' in $$props) $$invalidate(7, address = $$props.address);
		if ('phone' in $$props) $$invalidate(8, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(9, email = $$props.email);
		if ('social' in $$props) $$invalidate(10, social = $$props.social);
		if ('nav' in $$props) $$invalidate(11, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(12, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(13, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(14, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(15, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(16, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(17, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(18, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(19, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(20, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(21, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(22, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(23, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(24, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(25, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(26, seo_description = $$props.seo_description);
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
	};

	return [
		title,
		items,
		position,
		gap,
		slideLeft,
		slideRight,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(
			this,
			options,
			instance$7,
			create_fragment$7,
			safe_not_equal,
			{
				company: 6,
				address: 7,
				phone: 8,
				email: 9,
				social: 10,
				nav: 11,
				cta: 12,
				breadcrumbs: 13,
				phone2: 14,
				cplgk: 15,
				jsdoj: 16,
				pfjyn: 17,
				klxal: 18,
				gxlkm: 19,
				nmtxv: 20,
				vqimh: 21,
				mkegn: 22,
				zecgs: 23,
				cxxvx: 24,
				seo_title: 25,
				seo_description: 26,
				title: 0,
				items: 1
			},
			null,
			[-1, -1]
		);
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[27] = list[i];
	return child_ctx;
}

// (86:6) {#each items as i}
function create_each_block$4(ctx) {
	let li;
	let icon;
	let t0;
	let span;
	let t1_value = /*i*/ ctx[27].text + "";
	let t1;
	let t2;
	let current;

	icon = new Component$2({
			props: { icon: /*i*/ ctx[27].icon, width: "28" }
		});

	return {
		c() {
			li = element("li");
			create_component(icon.$$.fragment);
			t0 = space();
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			claim_component(icon.$$.fragment, li_nodes);
			t0 = claim_space(li_nodes);
			span = claim_element(li_nodes, "SPAN", {});
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(li, "class", "svelte-1f2bte");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			mount_component(icon, li, null);
			append_hydration(li, t0);
			append_hydration(li, span);
			append_hydration(span, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*items*/ 2) icon_changes.icon = /*i*/ ctx[27].icon;
			icon.$set(icon_changes);
			if ((!current || dirty & /*items*/ 2) && t1_value !== (t1_value = /*i*/ ctx[27].text + "")) set_data(t1, t1_value);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$8(ctx) {
	let div3;
	let div2;
	let section;
	let div0;
	let h3;
	let t0;
	let t1;
	let ul;
	let t2;
	let html_tag;
	let t3;
	let div1;
	let img_1;
	let img_1_src_value;
	let img_1_alt_value;
	let t4;
	let h2;
	let t5;
	let t6;
	let p;
	let t7;
	let current;
	let each_value = /*items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$4(get_each_context$4(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			section = element("section");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*title1*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			html_tag = new HtmlTagHydration(false);
			t3 = space();
			div1 = element("div");
			img_1 = element("img");
			t4 = space();
			h2 = element("h2");
			t5 = text(/*title2*/ ctx[4]);
			t6 = space();
			p = element("p");
			t7 = text(/*offer*/ ctx[5]);
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			section = claim_element(div2_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div0 = claim_element(section_nodes, "DIV", {});
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*title1*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", {});
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			html_tag = claim_html_tag(div0_nodes, false);
			div0_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			div1 = claim_element(section_nodes, "DIV", {});
			var div1_nodes = children(div1);
			img_1 = claim_element(div1_nodes, "IMG", { src: true, alt: true, class: true });
			t4 = claim_space(div1_nodes);
			h2 = claim_element(div1_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t5 = claim_text(h2_nodes, /*title2*/ ctx[4]);
			h2_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			p = claim_element(div1_nodes, "P", {});
			var p_nodes = children(p);
			t7 = claim_text(p_nodes, /*offer*/ ctx[5]);
			p_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-1f2bte");
			html_tag.a = null;
			if (!src_url_equal(img_1.src, img_1_src_value = /*img*/ ctx[3].src)) attr(img_1, "src", img_1_src_value);
			attr(img_1, "alt", img_1_alt_value = /*img*/ ctx[3].alt);
			attr(img_1, "class", "svelte-1f2bte");
			attr(h2, "class", "svelte-1f2bte");
			attr(section, "class", "section-container svelte-1f2bte");
			attr(div2, "class", "component");
			attr(div3, "class", "section has-component");
			attr(div3, "id", "vqimh");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, section);
			append_hydration(section, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div0, t1);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(ul, null);
			}

			append_hydration(div0, t2);
			html_tag.m(/*description*/ ctx[2], div0);
			append_hydration(section, t3);
			append_hydration(section, div1);
			append_hydration(div1, img_1);
			append_hydration(div1, t4);
			append_hydration(div1, h2);
			append_hydration(h2, t5);
			append_hydration(div1, t6);
			append_hydration(div1, p);
			append_hydration(p, t7);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*title1*/ 1) set_data(t0, /*title1*/ ctx[0]);

			if (dirty & /*items*/ 2) {
				each_value = /*items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$4(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$4(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (!current || dirty & /*description*/ 4) html_tag.p(/*description*/ ctx[2]);

			if (!current || dirty & /*img*/ 8 && !src_url_equal(img_1.src, img_1_src_value = /*img*/ ctx[3].src)) {
				attr(img_1, "src", img_1_src_value);
			}

			if (!current || dirty & /*img*/ 8 && img_1_alt_value !== (img_1_alt_value = /*img*/ ctx[3].alt)) {
				attr(img_1, "alt", img_1_alt_value);
			}

			if (!current || dirty & /*title2*/ 16) set_data(t5, /*title2*/ ctx[4]);
			if (!current || dirty & /*offer*/ 32) set_data(t7, /*offer*/ ctx[5]);
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { title1 } = $$props;
	let { items } = $$props;
	let { description } = $$props;
	let { img } = $$props;
	let { title2 } = $$props;
	let { offer } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(6, company = $$props.company);
		if ('address' in $$props) $$invalidate(7, address = $$props.address);
		if ('phone' in $$props) $$invalidate(8, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(9, email = $$props.email);
		if ('social' in $$props) $$invalidate(10, social = $$props.social);
		if ('nav' in $$props) $$invalidate(11, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(12, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(13, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(14, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(15, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(16, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(17, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(18, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(19, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(20, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(21, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(22, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(23, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(24, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(25, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(26, seo_description = $$props.seo_description);
		if ('title1' in $$props) $$invalidate(0, title1 = $$props.title1);
		if ('items' in $$props) $$invalidate(1, items = $$props.items);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('img' in $$props) $$invalidate(3, img = $$props.img);
		if ('title2' in $$props) $$invalidate(4, title2 = $$props.title2);
		if ('offer' in $$props) $$invalidate(5, offer = $$props.offer);
	};

	return [
		title1,
		items,
		description,
		img,
		title2,
		offer,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			company: 6,
			address: 7,
			phone: 8,
			email: 9,
			social: 10,
			nav: 11,
			cta: 12,
			breadcrumbs: 13,
			phone2: 14,
			cplgk: 15,
			jsdoj: 16,
			pfjyn: 17,
			klxal: 18,
			gxlkm: 19,
			nmtxv: 20,
			vqimh: 21,
			mkegn: 22,
			zecgs: 23,
			cxxvx: 24,
			seo_title: 25,
			seo_description: 26,
			title1: 0,
			items: 1,
			description: 2,
			img: 3,
			title2: 4,
			offer: 5
		});
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$9(ctx) {
	let div1;
	let div0;
	let section;
	let h2;
	let t0;
	let t1;
	let a;
	let t2_value = /*button*/ ctx[2].label + "";
	let t2;
	let a_href_value;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*title*/ ctx[1]);
			t1 = space();
			a = element("a");
			t2 = text(t2_value);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { style: true, class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*title*/ ctx[1]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			a = claim_element(section_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, t2_value);
			a_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "svelte-2154g1");
			attr(a, "href", a_href_value = /*button*/ ctx[2].url);
			attr(a, "class", "button");
			set_style(section, "background-image", "url('" + /*bg*/ ctx[0].src + "')");
			attr(section, "class", "svelte-2154g1");
			attr(div0, "class", "component");
			attr(div1, "class", "section has-component");
			attr(div1, "id", "mkegn");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, a);
			append_hydration(a, t2);
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 2) set_data(t0, /*title*/ ctx[1]);
			if (dirty & /*button*/ 4 && t2_value !== (t2_value = /*button*/ ctx[2].label + "")) set_data(t2, t2_value);

			if (dirty & /*button*/ 4 && a_href_value !== (a_href_value = /*button*/ ctx[2].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*bg*/ 1) {
				set_style(section, "background-image", "url('" + /*bg*/ ctx[0].src + "')");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { bg } = $$props;
	let { title } = $$props;
	let { button } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(3, company = $$props.company);
		if ('address' in $$props) $$invalidate(4, address = $$props.address);
		if ('phone' in $$props) $$invalidate(5, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(6, email = $$props.email);
		if ('social' in $$props) $$invalidate(7, social = $$props.social);
		if ('nav' in $$props) $$invalidate(8, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(9, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(10, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(11, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(12, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(13, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(14, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(15, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(16, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(17, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(18, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(19, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(20, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(21, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(22, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(23, seo_description = $$props.seo_description);
		if ('bg' in $$props) $$invalidate(0, bg = $$props.bg);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('button' in $$props) $$invalidate(2, button = $$props.button);
	};

	return [
		bg,
		title,
		button,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			company: 3,
			address: 4,
			phone: 5,
			email: 6,
			social: 7,
			nav: 8,
			cta: 9,
			breadcrumbs: 10,
			phone2: 11,
			cplgk: 12,
			jsdoj: 13,
			pfjyn: 14,
			klxal: 15,
			gxlkm: 16,
			nmtxv: 17,
			vqimh: 18,
			mkegn: 19,
			zecgs: 20,
			cxxvx: 21,
			seo_title: 22,
			seo_description: 23,
			bg: 0,
			title: 1,
			button: 2
		});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[23] = list[i];
	return child_ctx;
}

// (64:4) {#each clients as client}
function create_each_block$5(ctx) {
	let span;
	let img;
	let img_src_value;
	let img_alt_value;
	let span_title_value;

	return {
		c() {
			span = element("span");
			img = element("img");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { title: true });
			var span_nodes = children(span);
			img = claim_element(span_nodes, "IMG", { src: true, alt: true, class: true });
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*client*/ ctx[23].logo.src)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*client*/ ctx[23].logo.alt);
			attr(img, "class", "svelte-1jh08m5");
			attr(span, "title", span_title_value = /*client*/ ctx[23].logo.alt);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, img);
		},
		p(ctx, dirty) {
			if (dirty & /*clients*/ 2 && !src_url_equal(img.src, img_src_value = /*client*/ ctx[23].logo.src)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*clients*/ 2 && img_alt_value !== (img_alt_value = /*client*/ ctx[23].logo.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*clients*/ 2 && span_title_value !== (span_title_value = /*client*/ ctx[23].logo.alt)) {
				attr(span, "title", span_title_value);
			}
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

function create_fragment$a(ctx) {
	let div2;
	let div1;
	let section;
	let h3;
	let t0;
	let t1;
	let div0;
	let each_value = /*clients*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$5(get_each_context$5(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			h3 = element("h3");
			t0 = text(/*title*/ ctx[0]);
			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h3 = claim_element(section_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*title*/ ctx[0]);
			h3_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-1jh08m5");
			attr(div0, "class", "clients svelte-1jh08m5");
			attr(section, "class", "section-container svelte-1jh08m5");
			attr(div1, "class", "component");
			attr(div2, "class", "section has-component");
			attr(div2, "id", "zecgs");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, h3);
			append_hydration(h3, t0);
			append_hydration(section, t1);
			append_hydration(section, div0);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div0, null);
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 1) set_data(t0, /*title*/ ctx[0]);

			if (dirty & /*clients*/ 2) {
				each_value = /*clients*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$5(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$5(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { title } = $$props;
	let { clients } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(2, company = $$props.company);
		if ('address' in $$props) $$invalidate(3, address = $$props.address);
		if ('phone' in $$props) $$invalidate(4, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(5, email = $$props.email);
		if ('social' in $$props) $$invalidate(6, social = $$props.social);
		if ('nav' in $$props) $$invalidate(7, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(8, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(9, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(10, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(11, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(12, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(13, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(14, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(15, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(16, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(17, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(18, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(19, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(20, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(21, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(22, seo_description = $$props.seo_description);
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('clients' in $$props) $$invalidate(1, clients = $$props.clients);
	};

	return [
		title,
		clients,
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description
	];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$a, create_fragment$a, safe_not_equal, {
			company: 2,
			address: 3,
			phone: 4,
			email: 5,
			social: 6,
			nav: 7,
			cta: 8,
			breadcrumbs: 9,
			phone2: 10,
			cplgk: 11,
			jsdoj: 12,
			pfjyn: 13,
			klxal: 14,
			gxlkm: 15,
			nmtxv: 16,
			vqimh: 17,
			mkegn: 18,
			zecgs: 19,
			cxxvx: 20,
			seo_title: 21,
			seo_description: 22,
			title: 0,
			clients: 1
		});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$6(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[25] = list[i].link;
	child_ctx[26] = list[i].submenu;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[29] = list[i].sublink;
	return child_ctx;
}

// (147:8) {#each submenu as {sublink}}
function create_each_block_1$1(ctx) {
	let li;
	let a;
	let t_value = /*sublink*/ ctx[29].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			li = element("li");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*sublink*/ ctx[29].url);
			attr(a, "class", "svelte-6j66jl");
			attr(li, "class", "svelte-6j66jl");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 8 && t_value !== (t_value = /*sublink*/ ctx[29].label + "")) set_data(t, t_value);

			if (dirty[0] & /*nav*/ 8 && a_href_value !== (a_href_value = /*sublink*/ ctx[29].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (146:8) {#each nav as {link, submenu}}
function create_each_block$6(ctx) {
	let each_1_anchor;
	let each_value_1 = /*submenu*/ ctx[26];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	return {
		c() {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
		},
		l(nodes) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nodes);
			}

			each_1_anchor = empty();
		},
		m(target, anchor) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(target, anchor);
			}

			insert_hydration(target, each_1_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*nav*/ 8) {
				each_value_1 = /*submenu*/ ctx[26];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(each_1_anchor.parentNode, each_1_anchor);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			destroy_each(each_blocks, detaching);
			if (detaching) detach(each_1_anchor);
		}
	};
}

function create_fragment$b(ctx) {
	let div6;
	let div5;
	let footer;
	let div3;
	let div0;
	let h30;
	let t0;
	let t1;
	let svg;
	let polygon0;
	let polyline0;
	let polyline1;
	let polyline2;
	let polygon1;
	let rect0;
	let path0;
	let path1;
	let path2;
	let path3;
	let path4;
	let path5;
	let path6;
	let path7;
	let path8;
	let rect1;
	let path9;
	let path10;
	let path11;
	let t2;
	let ul0;
	let li0;
	let icon0;
	let t3;
	let t4;
	let li1;
	let icon1;
	let t5;
	let t6;
	let li2;
	let icon2;
	let a0;
	let t7;
	let a0_href_value;
	let t8;
	let li3;
	let icon3;
	let a1;
	let t9;
	let a1_href_value;
	let t10;
	let div1;
	let h31;
	let t11;
	let t12;
	let ul1;
	let t13;
	let div2;
	let h32;
	let t14;
	let t15;
	let p;
	let t16;
	let t17;
	let input;
	let t18;
	let button;
	let t19;
	let t20;
	let div4;
	let t21;
	let t22;
	let t23;
	let t24;
	let current;
	let mounted;
	let dispose;

	icon0 = new Component$2({
			props: { icon: "mdi:stamper", height: "20" }
		});

	icon1 = new Component$2({
			props: {
				icon: "mdi:office-building-marker",
				height: "20"
			}
		});

	icon2 = new Component$2({
			props: { icon: "mdi:phone", height: "20" }
		});

	icon3 = new Component$2({
			props: { icon: "mdi:phone", height: "20" }
		});

	let each_value = /*nav*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$6(get_each_context$6(ctx, each_value, i));
	}

	return {
		c() {
			div6 = element("div");
			div5 = element("div");
			footer = element("footer");
			div3 = element("div");
			div0 = element("div");
			h30 = element("h3");
			t0 = text("?????????????? ???? ????????");
			t1 = space();
			svg = svg_element("svg");
			polygon0 = svg_element("polygon");
			polyline0 = svg_element("polyline");
			polyline1 = svg_element("polyline");
			polyline2 = svg_element("polyline");
			polygon1 = svg_element("polygon");
			rect0 = svg_element("rect");
			path0 = svg_element("path");
			path1 = svg_element("path");
			path2 = svg_element("path");
			path3 = svg_element("path");
			path4 = svg_element("path");
			path5 = svg_element("path");
			path6 = svg_element("path");
			path7 = svg_element("path");
			path8 = svg_element("path");
			rect1 = svg_element("rect");
			path9 = svg_element("path");
			path10 = svg_element("path");
			path11 = svg_element("path");
			t2 = space();
			ul0 = element("ul");
			li0 = element("li");
			create_component(icon0.$$.fragment);
			t3 = text(/*company*/ ctx[0]);
			t4 = space();
			li1 = element("li");
			create_component(icon1.$$.fragment);
			t5 = text(/*address*/ ctx[1]);
			t6 = space();
			li2 = element("li");
			create_component(icon2.$$.fragment);
			a0 = element("a");
			t7 = text(/*phone*/ ctx[2]);
			t8 = space();
			li3 = element("li");
			create_component(icon3.$$.fragment);
			a1 = element("a");
			t9 = text(/*phone2*/ ctx[4]);
			t10 = space();
			div1 = element("div");
			h31 = element("h3");
			t11 = text("??????????????????");
			t12 = space();
			ul1 = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t13 = space();
			div2 = element("div");
			h32 = element("h3");
			t14 = text("???????????????????? ?????? Newsletter");
			t15 = space();
			p = element("p");
			t16 = text("?????? ???? ?????????????????? ?????? ???? ?????? & ?????? ?????????????????? ??????");
			t17 = space();
			input = element("input");
			t18 = space();
			button = element("button");
			t19 = text("??????????????");
			t20 = space();
			div4 = element("div");
			t21 = text("???????????????????? ???????????????????? ???????????????????????? ?? ");
			t22 = text(/*year*/ ctx[5]);
			t23 = space();
			t24 = text(/*company*/ ctx[0]);
			this.h();
		},
		l(nodes) {
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			footer = claim_element(div5_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div3 = claim_element(footer_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h30 = claim_element(div0_nodes, "H3", { class: true });
			var h30_nodes = children(h30);
			t0 = claim_text(h30_nodes, "?????????????? ???? ????????");
			h30_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);

			svg = claim_svg_element(div0_nodes, "svg", {
				viewBox: true,
				"xml:space": true,
				xmlns: true,
				class: true
			});

			var svg_nodes = children(svg);
			polygon0 = claim_svg_element(svg_nodes, "polygon", { class: true, points: true });
			children(polygon0).forEach(detach);
			polyline0 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline0).forEach(detach);
			polyline1 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline1).forEach(detach);
			polyline2 = claim_svg_element(svg_nodes, "polyline", { class: true, points: true });
			children(polyline2).forEach(detach);
			polygon1 = claim_svg_element(svg_nodes, "polygon", { class: true, points: true });
			children(polygon1).forEach(detach);

			rect0 = claim_svg_element(svg_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect0).forEach(detach);
			path0 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path0).forEach(detach);
			path1 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path1).forEach(detach);
			path2 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path2).forEach(detach);
			path3 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path3).forEach(detach);
			path4 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path4).forEach(detach);
			path5 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path5).forEach(detach);
			path6 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path6).forEach(detach);
			path7 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path7).forEach(detach);
			path8 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path8).forEach(detach);

			rect1 = claim_svg_element(svg_nodes, "rect", {
				class: true,
				x: true,
				y: true,
				width: true,
				height: true
			});

			children(rect1).forEach(detach);
			path9 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path9).forEach(detach);
			path10 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path10).forEach(detach);
			path11 = claim_svg_element(svg_nodes, "path", { class: true, d: true });
			children(path11).forEach(detach);
			svg_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			ul0 = claim_element(div0_nodes, "UL", {});
			var ul0_nodes = children(ul0);
			li0 = claim_element(ul0_nodes, "LI", { class: true });
			var li0_nodes = children(li0);
			claim_component(icon0.$$.fragment, li0_nodes);
			t3 = claim_text(li0_nodes, /*company*/ ctx[0]);
			li0_nodes.forEach(detach);
			t4 = claim_space(ul0_nodes);
			li1 = claim_element(ul0_nodes, "LI", { class: true });
			var li1_nodes = children(li1);
			claim_component(icon1.$$.fragment, li1_nodes);
			t5 = claim_text(li1_nodes, /*address*/ ctx[1]);
			li1_nodes.forEach(detach);
			t6 = claim_space(ul0_nodes);
			li2 = claim_element(ul0_nodes, "LI", { class: true });
			var li2_nodes = children(li2);
			claim_component(icon2.$$.fragment, li2_nodes);
			a0 = claim_element(li2_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			t7 = claim_text(a0_nodes, /*phone*/ ctx[2]);
			a0_nodes.forEach(detach);
			li2_nodes.forEach(detach);
			t8 = claim_space(ul0_nodes);
			li3 = claim_element(ul0_nodes, "LI", { class: true });
			var li3_nodes = children(li3);
			claim_component(icon3.$$.fragment, li3_nodes);
			a1 = claim_element(li3_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t9 = claim_text(a1_nodes, /*phone2*/ ctx[4]);
			a1_nodes.forEach(detach);
			li3_nodes.forEach(detach);
			ul0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t10 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h31 = claim_element(div1_nodes, "H3", { class: true });
			var h31_nodes = children(h31);
			t11 = claim_text(h31_nodes, "??????????????????");
			h31_nodes.forEach(detach);
			t12 = claim_space(div1_nodes);
			ul1 = claim_element(div1_nodes, "UL", { id: true });
			var ul1_nodes = children(ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul1_nodes);
			}

			ul1_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t13 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h32 = claim_element(div2_nodes, "H3", { class: true });
			var h32_nodes = children(h32);
			t14 = claim_text(h32_nodes, "???????????????????? ?????? Newsletter");
			h32_nodes.forEach(detach);
			t15 = claim_space(div2_nodes);
			p = claim_element(div2_nodes, "P", {});
			var p_nodes = children(p);
			t16 = claim_text(p_nodes, "?????? ???? ?????????????????? ?????? ???? ?????? & ?????? ?????????????????? ??????");
			p_nodes.forEach(detach);
			t17 = claim_space(div2_nodes);

			input = claim_element(div2_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			t18 = claim_space(div2_nodes);
			button = claim_element(div2_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			t19 = claim_text(button_nodes, "??????????????");
			button_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t20 = claim_space(footer_nodes);
			div4 = claim_element(footer_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			t21 = claim_text(div4_nodes, "???????????????????? ???????????????????? ???????????????????????? ?? ");
			t22 = claim_text(div4_nodes, /*year*/ ctx[5]);
			t23 = claim_space(div4_nodes);
			t24 = claim_text(div4_nodes, /*company*/ ctx[0]);
			div4_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h30, "class", "svelte-6j66jl");
			attr(polygon0, "class", "st0 svelte-6j66jl");
			attr(polygon0, "points", "173 105.8 122.6 0.2 5 249.8 105.8 249.8");
			attr(polyline0, "class", "st0 svelte-6j66jl");
			attr(polyline0, "points", "355.5 146.6 406.2 249.8 507 249.8 405.9 38.6");
			attr(polyline1, "class", "st1 svelte-6j66jl");
			attr(polyline1, "points", "158.6 137 173 105.8 122.6 0.2");
			attr(polyline2, "class", "st1 svelte-6j66jl");
			attr(polyline2, "points", "355.4 146.6 367.5 170.6 405.9 38.6 405.8 38.6");
			attr(polygon1, "class", "st2 svelte-6j66jl");
			attr(polygon1, "points", "324.8 213 405.9 38.6 307.8 38.6 274.8 108 223.5 0.2 122.6 0.2 224.3 213.8 224.6 213.8 173.4 321.8 274.2 321.8 324.4 213.8 325.2 213.8");
			attr(rect0, "class", "st2 svelte-6j66jl");
			attr(rect0, "x", "1436.9");
			attr(rect0, "y", "24.6");
			attr(rect0, "width", "25.4");
			attr(rect0, "height", "39.4");
			attr(path0, "class", "st0 svelte-6j66jl");
			attr(path0, "d", "m625.8 69.3c-6.8 0-13.1 1.7-18.8 5.1-5.8 3.4-10.7 8.3-14.8 14.7s-7.3 14.4-9.6 23.8c-2.3 9.5-3.5 20.3-3.5 32.4s1.1 22.7 3.2 31.8 5.1 16.8 9.1 22.9c3.9 6.1 8.8 10.8 14.4 13.9 5.7 3.1 12.1 4.7 19.3 4.7 5.2 0 10.4-0.6 15.8-1.8s10.4-3 15.1-5.4v32.4c-4.8 2-9.9 3.7-15.4 4.8-5.5 1.2-11.2 1.8-17.2 1.8-11.6 0-21.7-2.5-30.5-7.4-8.8-5-16.1-12-22-21s-10.3-19.9-13.3-32.5-4.4-26.5-4.4-41.8c0-15.6 1.6-30.2 4.7-43.5 3.2-13.4 7.7-25 13.7-34.8s13.4-17.5 22.4-23.2c9-5.6 19.1-8.5 30.4-8.6 5.8 0 11.3 0.6 16.4 1.8 5.2 1.2 9.8 2.8 14 5v31.9c-5.4-2.6-10.5-4.3-15.2-5.4s-9.3-1.6-13.8-1.6z");
			attr(path1, "class", "st0 svelte-6j66jl");
			attr(path1, "d", "m772.9 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7 2.2 9.6 3.4 20.2 3.4 31.9zm-25.1 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path2, "class", "st0 svelte-6j66jl");
			attr(path2, "d", "m816.6 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path3, "class", "st0 svelte-6j66jl");
			attr(path3, "d", "m954.1 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(path4, "class", "st0 svelte-6j66jl");
			attr(path4, "d", "m1059.4 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.6v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(path5, "class", "st0 svelte-6j66jl");
			attr(path5, "d", "m1137.1 126.8h-2c-7.4 0-13.9 1.7-19.6 5-5.6 3.3-10 8.4-13 15.3v99.5h-24.2v-148.6h20l2.2 20.7h0.4c2.9-7.6 6.8-13.5 11.8-17.9 5-4.3 11-6.5 18-6.5 2.5 0 4.6 0.2 6.3 0.6v31.9z");
			attr(path6, "class", "st0 svelte-6j66jl");
			attr(path6, "d", "m1195.1 250.4c-9.9 0-18.2-2.5-24.7-7.6s-11.5-11.9-14.8-20.5c-1.8-4.6-3.1-9.7-3.9-15.2-0.9-5.5-1.3-11.7-1.3-18.4v-90.7h24.2v86.9c0 5 0.2 9.3 0.7 13 0.5 3.6 1.2 6.8 2.1 9.4 1.6 4.5 3.9 7.8 6.9 10s6.6 3.3 10.7 3.3c4.4 0 8.1-1.2 11.2-3.7s5.4-6.2 7-11.2c1.6-4.8 2.3-11.5 2.3-20.1v-87.6h24.2v90.8c0 12.1-1.4 22.2-4.2 30.5-1.6 4.7-3.6 9-6.1 12.8s-5.4 7.1-8.8 9.8-7.2 4.8-11.4 6.3c-4.1 1.5-8.9 2.2-14.1 2.2z");
			attr(path7, "class", "st0 svelte-6j66jl");
			attr(path7, "d", "m1336.6 243.3c-3.1 1.9-6.8 3.6-11.2 5s-9.1 2.1-14 2.1c-7.1 0-13.8-1.5-20-4.6s-11.6-7.7-16.2-14c-4.6-6.2-8.3-14.1-10.9-23.7-2.7-9.6-4-20.7-4-33.5 0-14.3 1.5-26.6 4.6-36.8s7-18.5 11.9-24.9 10.3-11.1 16.4-14.1 12.1-4.5 18-4.5c4.4 0 8.7 0.6 12.8 1.8s7.8 2.8 11.1 4.8v29.6c-3-1.9-6.2-3.5-9.5-4.7-3.4-1.2-7-1.8-10.9-1.8s-7.6 0.9-11.1 2.7-6.7 4.6-9.4 8.5-4.9 9-6.5 15.4-2.4 14.1-2.4 23.1c0 6.5 0.6 12.7 1.8 18.5s3 10.7 5.4 14.8c2.3 4.1 5.3 7.4 9 9.9 3.6 2.5 7.9 3.8 12.9 3.8 4.4 0 8.4-0.7 12-2s7-3 10.2-4.9v29.5z");
			attr(path8, "class", "st0 svelte-6j66jl");
			attr(path8, "d", "m1418 246.4c-2.7 1.2-6 2.2-9.8 2.9s-7.3 1.1-10.6 1.1c-8.3 0-15.1-2-20.4-6.1-5.3-4-9-9.8-11.2-17.4-1.6-5.4-2.3-12.8-2.3-22.1v-77h-18.5v-29.8h18.5v-41.5h24.2v41.5h28.6v29.9h-28.5v72.2c0 5.7 0.6 10 1.7 12.7 2 4.7 6.1 7.1 12.2 7.1 2.8 0 5.6-0.3 8.3-1 2.8-0.7 5.4-1.5 7.8-2.5v30z");
			attr(rect1, "class", "st0 svelte-6j66jl");
			attr(rect1, "x", "1437.5");
			attr(rect1, "y", "98");
			attr(rect1, "width", "24.2");
			attr(rect1, "height", "148.6");
			attr(path9, "class", "st0 svelte-6j66jl");
			attr(path9, "d", "m1583.2 172.4c0 11.7-1.2 22.3-3.5 31.9s-5.6 17.8-10 24.7c-4.3 6.8-9.5 12.1-15.7 15.9-6.1 3.7-13 5.6-20.5 5.6-7.8 0-14.7-1.9-20.9-5.6s-11.4-9-15.7-15.9c-4.3-6.8-7.6-15.1-9.9-24.7s-3.4-20.2-3.4-31.9 1.2-22.3 3.5-31.9 5.6-17.8 10-24.7c4.3-6.8 9.5-12.1 15.7-15.9 6.1-3.7 13-5.6 20.5-5.6 7.8 0 14.7 1.9 20.9 5.6s11.4 9 15.7 15.9c4.3 6.8 7.6 15.1 9.9 24.7s3.4 20.2 3.4 31.9zm-25 0c0-7.9-0.6-14.8-1.8-20.9-1.2-6-2.9-11.1-5.1-15.2s-4.8-7.2-7.9-9.2-6.4-3.1-10-3.1c-3.5 0-6.8 1-9.9 3.1-3 2-5.6 5.1-7.8 9.2s-3.9 9.1-5.1 15.2c-1.2 6-1.8 13-1.8 20.9s0.6 14.8 1.8 20.9c1.2 6 2.9 11.1 5.2 15.1 2.2 4 4.8 7.1 7.9 9.2 3 2.1 6.3 3.1 10 3.1 3.6 0 6.9-1 9.9-3.1s5.6-5.2 7.8-9.2 3.9-9.1 5.1-15.1c1.1-6.1 1.7-13.1 1.7-20.9z");
			attr(path10, "class", "st0 svelte-6j66jl");
			attr(path10, "d", "m1626.9 118.7h0.4c1.4-3.1 3.2-6.1 5.4-9 2.2-3 4.7-5.6 7.5-7.8s5.9-4.1 9.2-5.4c3.4-1.4 7-2.1 10.8-2.1 3.6 0 7.1 0.6 10.5 1.8s6.4 3.1 9.2 5.7 5.3 6 7.4 10.1 3.8 9.1 5.1 14.8c0.7 3.2 1.1 6.6 1.4 10.3 0.2 3.7 0.4 8 0.4 13v96.4h-24.2v-90.8c0-4-0.1-7.4-0.3-10.3s-0.6-5.4-1.1-7.5c-1.2-4.7-3.1-8.1-5.6-10.1s-5.5-3.1-9-3.1c-4.7 0-9.2 1.7-13.5 5s-8.2 8.2-11.5 14.5v102.3h-24.2v-148.5h20l2.1 20.7z");
			attr(path11, "class", "st0 svelte-6j66jl");
			attr(path11, "d", "m1764.4 203.5c0-3.2-0.6-5.8-1.8-7.8s-2.8-3.8-4.7-5.1c-2-1.4-4.2-2.6-6.8-3.6s-5.2-2-8-3.1c-3.5-1.4-6.9-3.1-10.2-5s-6.1-4.4-8.6-7.4c-2.5-3.1-4.5-6.9-5.9-11.6-1.5-4.6-2.2-10.3-2.2-17.1 0-8.3 1-15.5 3-21.5 2-6.1 4.6-11.1 8-15.1s7.3-6.9 11.7-8.9c4.5-1.9 9.2-2.9 14.1-2.9 6.1 0 11.7 0.7 17.1 2.2 5.3 1.5 10.1 3.4 14.4 5.7v29.6c-2.2-1.1-4.6-2.2-7.1-3.1-2.5-1-5-1.8-7.6-2.5s-5.1-1.3-7.6-1.8-4.9-0.7-7.1-0.7c-2.9 0-5.3 0.4-7.2 1.2-2 0.8-3.6 1.9-4.8 3.3s-2.1 3-2.7 4.8c-0.5 1.8-0.8 3.7-0.8 5.6 0 3.4 0.6 6.1 1.8 8.3 1.2 2.1 2.8 3.9 5 5.2 2.1 1.3 4.3 2.4 6.6 3.3s4.6 1.7 6.7 2.5c3.4 1.2 6.8 2.7 10.2 4.4s6.5 4.2 9.2 7.3 5 7.2 6.7 12.1c1.7 5 2.6 11.3 2.6 18.9 0 8.4-1.1 15.7-3.2 21.9s-5.1 11.4-8.8 15.6-8.3 7.2-13.6 9.2-11.1 3-17.4 3-11.9-0.7-16.9-2.2-9.1-3.3-12.4-5.6v-29.3c5.3 3 10.2 5 14.7 6.1s8.7 1.6 12.6 1.6c3 0 5.8-0.3 8.4-1s4.8-1.7 6.7-3.1 3.4-3.2 4.4-5.4c1-2.3 1.5-4.9 1.5-8z");
			attr(svg, "viewBox", "0 0 1790 322");
			attr(svg, "xml:space", "preserve");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "class", "svelte-6j66jl");
			attr(li0, "class", "svelte-6j66jl");
			attr(li1, "class", "svelte-6j66jl");
			attr(a0, "href", a0_href_value = "tel:" + /*phone*/ ctx[2].split(' ').join(''));
			attr(a0, "class", "svelte-6j66jl");
			attr(li2, "class", "svelte-6j66jl");
			attr(a1, "href", a1_href_value = "tel:" + /*phone2*/ ctx[4].split(' ').join(''));
			attr(a1, "class", "svelte-6j66jl");
			attr(li3, "class", "svelte-6j66jl");
			attr(div0, "class", "svelte-6j66jl");
			attr(h31, "class", "svelte-6j66jl");
			attr(ul1, "id", "services");
			attr(div1, "class", "svelte-6j66jl");
			attr(h32, "class", "svelte-6j66jl");
			attr(input, "type", "email");
			attr(input, "placeholder", "???? email ??????");
			attr(input, "class", "svelte-6j66jl");
			attr(button, "class", "button svelte-6j66jl");
			attr(div2, "class", "svelte-6j66jl");
			attr(div3, "class", "section-container svelte-6j66jl");
			attr(div4, "class", "copyright svelte-6j66jl");
			attr(footer, "class", "svelte-6j66jl");
			attr(div5, "class", "component");
			attr(div6, "class", "section has-component");
			attr(div6, "id", "cxxvx");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, div5);
			append_hydration(div5, footer);
			append_hydration(footer, div3);
			append_hydration(div3, div0);
			append_hydration(div0, h30);
			append_hydration(h30, t0);
			append_hydration(div0, t1);
			append_hydration(div0, svg);
			append_hydration(svg, polygon0);
			append_hydration(svg, polyline0);
			append_hydration(svg, polyline1);
			append_hydration(svg, polyline2);
			append_hydration(svg, polygon1);
			append_hydration(svg, rect0);
			append_hydration(svg, path0);
			append_hydration(svg, path1);
			append_hydration(svg, path2);
			append_hydration(svg, path3);
			append_hydration(svg, path4);
			append_hydration(svg, path5);
			append_hydration(svg, path6);
			append_hydration(svg, path7);
			append_hydration(svg, path8);
			append_hydration(svg, rect1);
			append_hydration(svg, path9);
			append_hydration(svg, path10);
			append_hydration(svg, path11);
			append_hydration(div0, t2);
			append_hydration(div0, ul0);
			append_hydration(ul0, li0);
			mount_component(icon0, li0, null);
			append_hydration(li0, t3);
			append_hydration(ul0, t4);
			append_hydration(ul0, li1);
			mount_component(icon1, li1, null);
			append_hydration(li1, t5);
			append_hydration(ul0, t6);
			append_hydration(ul0, li2);
			mount_component(icon2, li2, null);
			append_hydration(li2, a0);
			append_hydration(a0, t7);
			append_hydration(ul0, t8);
			append_hydration(ul0, li3);
			mount_component(icon3, li3, null);
			append_hydration(li3, a1);
			append_hydration(a1, t9);
			append_hydration(div3, t10);
			append_hydration(div3, div1);
			append_hydration(div1, h31);
			append_hydration(h31, t11);
			append_hydration(div1, t12);
			append_hydration(div1, ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(ul1, null);
			}

			append_hydration(div3, t13);
			append_hydration(div3, div2);
			append_hydration(div2, h32);
			append_hydration(h32, t14);
			append_hydration(div2, t15);
			append_hydration(div2, p);
			append_hydration(p, t16);
			append_hydration(div2, t17);
			append_hydration(div2, input);
			set_input_value(input, /*subscriber_email*/ ctx[6]);
			append_hydration(div2, t18);
			append_hydration(div2, button);
			append_hydration(button, t19);
			append_hydration(footer, t20);
			append_hydration(footer, div4);
			append_hydration(div4, t21);
			append_hydration(div4, t22);
			append_hydration(div4, t23);
			append_hydration(div4, t24);
			current = true;

			if (!mounted) {
				dispose = [
					listen(input, "input", /*input_input_handler*/ ctx[24]),
					listen(button, "click", /*subscribe*/ ctx[7])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty[0] & /*company*/ 1) set_data(t3, /*company*/ ctx[0]);
			if (!current || dirty[0] & /*address*/ 2) set_data(t5, /*address*/ ctx[1]);
			if (!current || dirty[0] & /*phone*/ 4) set_data(t7, /*phone*/ ctx[2]);

			if (!current || dirty[0] & /*phone*/ 4 && a0_href_value !== (a0_href_value = "tel:" + /*phone*/ ctx[2].split(' ').join(''))) {
				attr(a0, "href", a0_href_value);
			}

			if (!current || dirty[0] & /*phone2*/ 16) set_data(t9, /*phone2*/ ctx[4]);

			if (!current || dirty[0] & /*phone2*/ 16 && a1_href_value !== (a1_href_value = "tel:" + /*phone2*/ ctx[4].split(' ').join(''))) {
				attr(a1, "href", a1_href_value);
			}

			if (dirty[0] & /*nav*/ 8) {
				each_value = /*nav*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$6(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$6(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty[0] & /*subscriber_email*/ 64 && input.value !== /*subscriber_email*/ ctx[6]) {
				set_input_value(input, /*subscriber_email*/ ctx[6]);
			}

			if (!current || dirty[0] & /*year*/ 32) set_data(t22, /*year*/ ctx[5]);
			if (!current || dirty[0] & /*company*/ 1) set_data(t24, /*company*/ ctx[0]);
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			transition_in(icon2.$$.fragment, local);
			transition_in(icon3.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			transition_out(icon2.$$.fragment, local);
			transition_out(icon3.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div6);
			destroy_component(icon0);
			destroy_component(icon1);
			destroy_component(icon2);
			destroy_component(icon3);
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { cplgk } = $$props;
	let { jsdoj } = $$props;
	let { pfjyn } = $$props;
	let { klxal } = $$props;
	let { gxlkm } = $$props;
	let { nmtxv } = $$props;
	let { vqimh } = $$props;
	let { mkegn } = $$props;
	let { zecgs } = $$props;
	let { cxxvx } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let year = new Date().getFullYear();
	if (year > 2022) year = '2022 - ' + year;
	let subscriber_email = '';

	const subscribe = () => {
		
	};

	function input_input_handler() {
		subscriber_email = this.value;
		$$invalidate(6, subscriber_email);
	}

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(0, company = $$props.company);
		if ('address' in $$props) $$invalidate(1, address = $$props.address);
		if ('phone' in $$props) $$invalidate(2, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(8, email = $$props.email);
		if ('social' in $$props) $$invalidate(9, social = $$props.social);
		if ('nav' in $$props) $$invalidate(3, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(10, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(11, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(4, phone2 = $$props.phone2);
		if ('cplgk' in $$props) $$invalidate(12, cplgk = $$props.cplgk);
		if ('jsdoj' in $$props) $$invalidate(13, jsdoj = $$props.jsdoj);
		if ('pfjyn' in $$props) $$invalidate(14, pfjyn = $$props.pfjyn);
		if ('klxal' in $$props) $$invalidate(15, klxal = $$props.klxal);
		if ('gxlkm' in $$props) $$invalidate(16, gxlkm = $$props.gxlkm);
		if ('nmtxv' in $$props) $$invalidate(17, nmtxv = $$props.nmtxv);
		if ('vqimh' in $$props) $$invalidate(18, vqimh = $$props.vqimh);
		if ('mkegn' in $$props) $$invalidate(19, mkegn = $$props.mkegn);
		if ('zecgs' in $$props) $$invalidate(20, zecgs = $$props.zecgs);
		if ('cxxvx' in $$props) $$invalidate(21, cxxvx = $$props.cxxvx);
		if ('seo_title' in $$props) $$invalidate(22, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(23, seo_description = $$props.seo_description);
	};

	return [
		company,
		address,
		phone,
		nav,
		phone2,
		year,
		subscriber_email,
		subscribe,
		email,
		social,
		cta,
		breadcrumbs,
		cplgk,
		jsdoj,
		pfjyn,
		klxal,
		gxlkm,
		nmtxv,
		vqimh,
		mkegn,
		zecgs,
		cxxvx,
		seo_title,
		seo_description,
		input_input_handler
	];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();

		init(
			this,
			options,
			instance$b,
			create_fragment$b,
			safe_not_equal,
			{
				company: 0,
				address: 1,
				phone: 2,
				email: 8,
				social: 9,
				nav: 3,
				cta: 10,
				breadcrumbs: 11,
				phone2: 4,
				cplgk: 12,
				jsdoj: 13,
				pfjyn: 14,
				klxal: 15,
				gxlkm: 16,
				nmtxv: 17,
				vqimh: 18,
				mkegn: 19,
				zecgs: 20,
				cxxvx: 21,
				seo_title: 22,
				seo_description: 23
			},
			null,
			[-1, -1]
		);
	}
}

/* generated by Svelte v3.55.0 */

function instance$c($$self, $$props, $$invalidate) {
	let { company } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { social } = $$props;
	let { nav } = $$props;
	let { cta } = $$props;
	let { breadcrumbs } = $$props;
	let { phone2 } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;

	$$self.$$set = $$props => {
		if ('company' in $$props) $$invalidate(0, company = $$props.company);
		if ('address' in $$props) $$invalidate(1, address = $$props.address);
		if ('phone' in $$props) $$invalidate(2, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(3, email = $$props.email);
		if ('social' in $$props) $$invalidate(4, social = $$props.social);
		if ('nav' in $$props) $$invalidate(5, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(6, cta = $$props.cta);
		if ('breadcrumbs' in $$props) $$invalidate(7, breadcrumbs = $$props.breadcrumbs);
		if ('phone2' in $$props) $$invalidate(8, phone2 = $$props.phone2);
		if ('seo_title' in $$props) $$invalidate(9, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(10, seo_description = $$props.seo_description);
	};

	return [
		company,
		address,
		phone,
		email,
		social,
		nav,
		cta,
		breadcrumbs,
		phone2,
		seo_title,
		seo_description
	];
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$c, null, safe_not_equal, {
			company: 0,
			address: 1,
			phone: 2,
			email: 3,
			social: 4,
			nav: 5,
			cta: 6,
			breadcrumbs: 7,
			phone2: 8,
			seo_title: 9,
			seo_description: 10
		});
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$c(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let t10;
	let component_11;
	let current;

	component_0 = new Component({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????."
			}
		});

	component_1 = new Component$1({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				video: "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
			}
		});

	component_2 = new Component$3({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????."
			}
		});

	component_3 = new Component$4({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????."
			}
		});

	component_4 = new Component$5({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				title: "???????????????? ????????????????????????????",
				text: "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
			}
		});

	component_5 = new Component$6({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				heading: "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
				people: [
					{
						"image": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
							"alt": "Mall",
							"size": 70
						},
						"name": "???????????????????????????? ??????????",
						"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
					},
					{
						"image": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
							"alt": "??????????",
							"size": 92
						},
						"name": "???????????? & ????????????????????????",
						"title": "??????????????????, ????????????, ????????????????????"
					},
					{
						"image": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
							"alt": "??????????????",
							"size": 79
						},
						"name": "???????????????????? ??????????",
						"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
					}
				],
				bg: {
					"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
					"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
					"alt": "??????????????????",
					"size": 10
				}
			}
		});

	component_6 = new Component$7({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				title: "?????????????? ?????? ?????? ???????????????? ??????",
				items: [
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
							"alt": "???????????? ???????????????? ???? ??????????????????????",
							"size": null
						}
					},
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
							"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
							"size": null
						}
					},
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
							"alt": "???????????? ???????????????? ???? ????????????????????????",
							"size": null
						}
					},
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
							"alt": "???????????????? ????????????",
							"size": null
						}
					},
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
							"alt": "?????????????????????? ????????????",
							"size": null
						}
					},
					{
						"img": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
							"alt": "???????????????? ????????????",
							"size": null
						}
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				title1: "???? ??????????????????????",
				items: [
					{
						"icon": "mdi:layers-search",
						"text": "????????????"
					},
					{
						"icon": "mdi:file-cad-box",
						"text": "????????????????????"
					},
					{
						"icon": "fa6-solid:helmet-safety",
						"text": "??????????????????"
					}
				],
				description: "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
				img: {
					"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
					"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
					"alt": "????????????????",
					"size": 23
				},
				title2: "????????????????????",
				offer: "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
			}
		});

	component_8 = new Component$9({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				bg: {
					"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
					"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
					"alt": "",
					"size": 29
				},
				title: "?????? ?????? ???????? ???????? ??????????????????",
				button: {
					"label": "?????????????? ????????????????",
					"url": "/epikoinonia"
				}
			}
		});

	component_9 = new Component$a({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????.",
				title: "???????????????????????????? ??????????????",
				clients: [
					{
						"logo": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
							"alt": "???????????? ???????????????????? ???????????????????? ????????????",
							"size": 4
						}
					},
					{
						"logo": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
							"alt": "Cosmote",
							"size": 2
						}
					},
					{
						"logo": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
							"alt": "???????????????? ???????????????? ??????",
							"size": 4
						}
					},
					{
						"logo": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
							"alt": "???????????????????????? ??????????????",
							"size": 3
						}
					},
					{
						"logo": {
							"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
							"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
							"alt": "",
							"size": 2
						}
					}
				]
			}
		});

	component_10 = new Component$b({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				cplgk: {},
				jsdoj: {
					"video": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/header.mp4"
				},
				pfjyn: {
					"title": "???????????????? ????????????????????????????",
					"text": "????????????????????, ???????????????? & ???????????????????????? ?????? ???? 1995"
				},
				klxal: {},
				gxlkm: {
					"heading": "???????????? ?????? ?????????????????? & ?????????????????????????????? ???????????? ???????????????? ?????? ????????????????????",
					"people": [
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/commercial.jpg",
								"alt": "Mall",
								"size": 70
							},
							"name": "???????????????????????????? ??????????",
							"title": "??????????????????????, ??????????????, ????????????????, ???????????????????? ??.??."
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/houses.jpg",
								"alt": "??????????",
								"size": 92
							},
							"name": "???????????? & ????????????????????????",
							"title": "??????????????????, ????????????, ????????????????????"
						},
						{
							"image": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/outdoor.jpg",
								"alt": "??????????????",
								"size": 79
							},
							"name": "???????????????????? ??????????",
							"title": "??????????????, ????????????????, ??????????, ???????????? ??.??."
						}
					],
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/services-banner.jpg",
						"alt": "??????????????????",
						"size": 10
					}
				},
				nmtxv: {
					"title": "?????????????? ?????? ?????? ???????????????? ??????",
					"items": [
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asfaltopano.jpg",
								"alt": "???????????? ???????????????? ???? ??????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/epoxeidiko-dapedo.jpg",
								"alt": "???????????????????? ???????????? ?????? Mr. KTEO",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/polyourethaniko.jpg",
								"alt": "???????????? ???????????????? ???? ????????????????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/stampoto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/viomixaniko-dapedo.jpg",
								"alt": "?????????????????????? ????????????",
								"size": null
							}
						},
						{
							"img": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/xtenisto-dapedo.jpg",
								"alt": "???????????????? ????????????",
								"size": null
							}
						}
					]
				},
				vqimh: {
					"title1": "???? ??????????????????????",
					"items": [
						{
							"icon": "mdi:layers-search",
							"text": "????????????"
						},
						{
							"icon": "mdi:file-cad-box",
							"text": "????????????????????"
						},
						{
							"icon": "fa6-solid:helmet-safety",
							"text": "??????????????????"
						}
					],
					"description": "<p>?????? ???? ???????????????? ???? ?????? ?????????????????????????? \"???? ?????????????? ???? ??????????\", ?????????? ???????????????????? ???????? ?????????????????????? ?????? ?????????? ?????? ?????? ?????????????????????? ?????? ???????????????? ???????????? ????????.</p>\n<p>????????????????, ???????????????? &amp; ?????????????????? ?????? ???? ?????????? ?????? ???? ??????????????????, ?????????? ?????? ??????????????????.</p>",
					"img": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/worker2.jpg",
						"alt": "????????????????",
						"size": 23
					},
					"title2": "????????????????????",
					"offer": "?????????????????????????? ???????????????????????? & ?????????????????????? \"????????????????????\" ???? ?????????????????????? ?????????? ???? ?????????????????????????? ??????????????????"
				},
				mkegn: {
					"bg": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/cta.jpg",
						"alt": "",
						"size": 29
					},
					"title": "?????? ?????? ???????? ???????? ??????????????????",
					"button": {
						"label": "?????????????? ????????????????",
						"url": "/epikoinonia"
					}
				},
				zecgs: {
					"title": "???????????????????????????? ??????????????",
					"clients": [
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/asklipieio.png",
								"alt": "???????????? ???????????????????? ???????????????????? ????????????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/nikas.png",
								"alt": "Cosmote",
								"size": 2
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/eko2.png",
								"alt": "???????????????? ???????????????? ??????",
								"size": 4
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/ifantis.png",
								"alt": "???????????????????????? ??????????????",
								"size": 3
							}
						},
						{
							"logo": {
								"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/my-constructions/assets/mrkteo.png",
								"alt": "",
								"size": 2
							}
						}
					]
				},
				cxxvx: {},
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????."
			}
		});

	component_11 = new Component$c({
			props: {
				company: "???????????????? ??.??.",
				address: "?????????????? 21??, 15344, ??????????????",
				phone: "6937 2790 97",
				email: "info@myconstructions.gr",
				social: [
					{
						"icon": "mdi:facebook",
						"link": "https://fb.com/mytkolliconstructions",
						"title": "?????????????????????? ?????? ?????? facebook"
					},
					{
						"icon": "mdi:google",
						"link": "https://g.page/r/CeRvtYi5x5gKEAI",
						"title": "???????????? ?????? ?????? google"
					}
				],
				nav: [
					{
						"link": { "label": "????????????", "url": "/" },
						"submenu": []
					},
					{
						"link": {
							"label": "??????????????????",
							"url": "/ypiresies"
						},
						"submenu": [
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/stampoto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????????????????? ????????????",
									"url": "/ypiresies/viomichaniko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ????????????",
									"url": "/ypiresies/epoxidiko-dapedo"
								}
							},
							{
								"sublink": {
									"label": "???????????????? ????????????",
									"url": "/ypiresies/chtenisto-dapedo"
								}
							},
							{
								"sublink": {
									"label": "?????????? ??????????????????????",
									"url": "/ypiresies/rampa-psarokokkali"
								}
							},
							{
								"sublink": {
									"label": "???????????????????? ???? ??????????????????????",
									"url": "/ypiresies/ygromonosi-me-asfaltopano"
								}
							},
							{
								"sublink": {
									"label": "???????????? ???? ???????????????????????????? ??????????",
									"url": "/ypiresies/monosi-me-polyourethaniko-yliko"
								}
							},
							{
								"sublink": {
									"label": "???????????????????????? ??????????????",
									"url": "/ypiresies/thermoprosopi-ktirion"
								}
							}
						]
					},
					{
						"link": { "label": "?? ??????????????", "url": "/etairia" },
						"submenu": []
					}
				],
				cta: [
					{
						"link": {
							"label": "??????????????????????",
							"url": "/epikoinonia"
						}
					}
				],
				breadcrumbs: [],
				phone2: "6937 2790 96",
				seo_title: "???????????????? ???????????????????????????? | ???????????????? - ???????????? - ????????????????????",
				seo_description: "???????????? ??????????????????, ??????????????????????, ????????????????????, ????????????????, ????????????. ????????????????????, ??????????????????????, ????????????????????????. ???????????????????? & ???????????????????????? ?????? ????????????."
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
			t10 = space();
			create_component(component_11.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
			t10 = claim_space(nodes);
			claim_component(component_11.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			insert_hydration(target, t10, anchor);
			mount_component(component_11, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			transition_in(component_11.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			transition_out(component_11.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
			if (detaching) detach(t10);
			destroy_component(component_11, detaching);
		}
	};
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$c, safe_not_equal, {});
	}
}

export default Component$d;
