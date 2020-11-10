'use strict';

var MathJax = {
    options: {
        skipHtmlTags: [
            'script', 'noscript', 'style', 'textarea',
            'annotation', 'annotation-xml'
        ]
    },
    startup: {
        pageReady: function () {
            mathjax_setup();
            return MathJax.startup.defaultPageReady();
        }
    }
};

function mathjax_setup() {
   var spans = document.querySelectorAll(".coq-mathjax .goal-conclusion .highlight, .coq-mathjax .goal-hyp .highlight");
   spans.forEach(function (e) {
       var text = e.innerText.replace(/ccForall\{(.*?)\}/g, function (_, quantified) {
           return "ccForall{" + quantified.trim().replace(/ +/g, " \\: ") + "}";
       });
       var node = document.createTextNode('\\[' + text + '\\]');
       e.parentNode.replaceChild(node, e);
   });
}

function rbt() {
    function draw(container, data) {
        container = d3.select(container);

        const node = container.append('span');
        node.node().className = "rbt-graph";

        const svg = node.append('svg');
        const inner = svg.append('g');

        const DIM = 7;
        var g = new dagreD3.graphlib.Graph().setGraph({rankdir: 'TB', edgesep: DIM, ranksep: DIM, nodesep: DIM});

        const EDGE_STYLES = { node: "stroke: #2e3436; stroke-width: 1.5; fill: none;", leaf: "visibility: hidden;" };
        const EDGE_PROPS = kind => ({ style: EDGE_STYLES[kind], curve: d3.curveBasis, arrowheadStyle: "fill: none;" });

        const NODE_STYLES = { Black: "fill: #2e3436", Red: "fill: #cc0000;" };
        const NODE_PROPS = color => ({ style: NODE_STYLES[color], shape: "circle", labelStyle: "fill: #eeeeec; font-size: 18px;", width: DIM, height: DIM });
        const INVISIBLE_NODE_PROPS = { style: "visibility: hidden;" };

        var gensym = 0;
        var dfs = tree => {
            const id = 'node' + (gensym++);

            if (tree.kind === "node") {
                var label = d3.select(document.createElementNS('http://www.w3.org/2000/svg', 'text'));
                label.append("tspan")
                    .attr('x', '0')
                    .attr('dy', '1em')
                    .text(tree.value);
                g.setNode(id, { label: label.node(), labelType: "svg", ...NODE_PROPS(tree.color) });;
                if (tree.left.kind == "node" || tree.right.kind == "node") {
                    const left = dfs(tree.left), right = dfs(tree.right);
                    g.setEdge(id, left, EDGE_PROPS(tree.left.kind));
                    g.setEdge(id, right, EDGE_PROPS(tree.right.kind));
                }
                return id;
            }

            g.setNode(id, { label: "", ...INVISIBLE_NODE_PROPS });;
            return id;
        }

        dfs(data.tree);

        // Set up zoom support
        var zoom = d3.zoom().on("zoom", function() {
            inner.attr("transform", d3.event.transform);
        });
        svg.call(zoom);

        // Create the renderer
        var render = new dagreD3.render();

        // Run the renderer. This is what draws the final graph.
        render(inner, g);

        // Scale the graph relative to the reference font size (16px)
        svg.attr('height', "3.5em");
        svg.attr("width", "4em");

        var { height, width } = svg.node().getBoundingClientRect();
        var scale = width / (16 * 4) * 0.45; // 16px * svg.attr('height')

        // const threshold = 0.5;
        // if (g.graph().height < threshold * height / scale) {
        //     svg.attr("height", threshold * height);
        // }

        const scaled_offset = (width - g.graph().width * scale) / 2;
        svg.call(zoom.transform, d3.zoomIdentity.translate(scaled_offset, 0).scale(scale));
    }

    function prettify_messages() {
        document.querySelectorAll(".coq-rbt .coq-message").forEach(msg => {
            try {
                const m = msg.innerText.match(/^(=\s*)([\s\S]*)(:[\s\S]*)$/);
                const data_str = m[2].replace(/;/g, ",").replace(/'/g, '"');
                const data = JSON.parse(data_str);

                const _msg = msg.cloneNode(false);
                msg.parentNode.replaceChild(_msg, msg);

                const wrapper = document.createElement("span");
                wrapper.className = "rbt-wrapper";

                if (Array.isArray(data)) {
                    _msg.appendChild(document.createTextNode(m[1] + "["));
                    _msg.appendChild(wrapper);
                    _msg.appendChild(document.createTextNode("]"));

                    const sequence = document.createElement("span");
                    sequence.className = "rbt-sequence";
                    wrapper.appendChild(sequence);

                    data.forEach(graph => draw(sequence, graph));
                } else {
                    _msg.appendChild(wrapper);
                    draw(wrapper, data);
                }

                _msg.appendChild(document.createElement("wbr"));
                const annot = document.createElement("span");
                annot.appendChild(document.createTextNode(m[3]));
                annot.className = "conway-annot";
                _msg.appendChild(annot);

            } catch (err) {
                console.log(err);
            }
        });
    }

    prettify_messages();
}

function life() {
    function draw(data) {
        const INNER_SIZE = 40;
        const EDGE_WIDTH = 1;

        const BLOCK_COUNT = data.length;
        const EDGE_COUNT = BLOCK_COUNT + 1;
        const OUTER_SIZE = INNER_SIZE + EDGE_WIDTH * EDGE_COUNT;
        const BLOCK_INNER_SIZE = INNER_SIZE / BLOCK_COUNT;
        const CELL_SIZE = BLOCK_INNER_SIZE * 0.8;
        const BLOCK_OUTER_SIZE = BLOCK_INNER_SIZE + EDGE_WIDTH;

        const CELL_FILL = { color: "black" };
        const EDGE_STROKE = { color: "#888a85", width: EDGE_WIDTH };

        var svg = SVG();
        svg.viewbox(0, 0, OUTER_SIZE, OUTER_SIZE);
        // svg.attr({ width: BLOCK_COUNT * 20 + EDGE_COUNT * EDGE_WIDTH,
        //            height:  BLOCK_COUNT * 20 + EDGE_COUNT * EDGE_WIDTH });
        svg.attr({ width: OUTER_SIZE,
                   height:  OUTER_SIZE });
        svg.rect(OUTER_SIZE, OUTER_SIZE).fill("white");

        for (var bid = 0; bid <= BLOCK_COUNT; bid++) {
            const offset = bid * BLOCK_OUTER_SIZE + EDGE_WIDTH / 2;
            var horizontal = svg.line(0, 0, OUTER_SIZE, 0).move(0, offset);
            var vertical = svg.line(0, 0, 0, OUTER_SIZE).move(offset, 0);
            horizontal.stroke(EDGE_STROKE);
            vertical.stroke(EDGE_STROKE);
        }

        for (var x = 0; x < BLOCK_COUNT; x++) {
            for (var y = 0; y < BLOCK_COUNT; y++) {
                if (data[y][x] == 1) {
                    const vx = x * BLOCK_OUTER_SIZE + EDGE_WIDTH + BLOCK_INNER_SIZE / 2;
                    const vy = y * BLOCK_OUTER_SIZE + EDGE_WIDTH + BLOCK_INNER_SIZE / 2;
                    svg.circle(CELL_SIZE).center(vx, vy).fill(CELL_FILL);
                }
            }
        }

        return svg;
    }

    function prettify_messages() {
        document.querySelectorAll(".coq-life .coq-message").forEach(msg => {
            try {
                const m = msg.innerText.match(/^(=\s*)([\s\S]*)(:[\s\S]*)$/);
                const data_str = m[2].replace(/;/g, ",");
                const data = JSON.parse(data_str);
                const svgs = data.map(draw);

                const wrapper = document.createElement("span");
                wrapper.className = "conway-wrapper";

                const sequence = document.createElement("span");
                sequence.className = "conway-sequence";
                svgs.forEach((svg, i) => {
                    const sp = document.createElement("span");
                    sp.className = "conway-snapshot";
                    sequence.appendChild(sp);
                    svg.addTo(sp);
                });
                wrapper.appendChild(sequence);

                const _msg = msg.cloneNode(false);
                _msg.appendChild(document.createTextNode(m[1] + "["));
                _msg.appendChild(wrapper);
                _msg.appendChild(document.createTextNode("]"));
                _msg.appendChild(document.createElement("wbr"));

                const annot = document.createElement("span");
                annot.appendChild(document.createTextNode(m[3]));
                annot.className = "conway-annot";
                _msg.appendChild(annot);

                msg.parentNode.replaceChild(_msg, msg);
            } catch (err) {
                console.log(err);
            }
        });
    }

    prettify_messages();
}

rbt();
life();
