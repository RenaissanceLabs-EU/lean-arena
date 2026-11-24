// Starts every figure on the page when it nears the viewport.
import { lazyMount } from '/viz/runtime.js';
document.querySelectorAll('.vz[data-viz]').forEach((h) => lazyMount(h, h.dataset.viz));
