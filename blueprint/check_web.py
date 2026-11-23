"""Check the published-site layout against the Blueprint's main theorem."""
import json
import re
import sys
from pathlib import Path

LABEL = "thm:reciprocal-full-gevrey-expansion"
DOCS_URL = "https://vinicius-pi.github.io/212-Mathematics/docs"
MODULE = "Mathematics212/ReciprocalGevreyExpansion.html"
DECLARATIONS = (
    "Mathematics212.reciprocal_sampled_summable",
    "Mathematics212.reciprocal_complex_remainder_identity",
    "Mathematics212.polynomial_reciprocal_gevrey_expansion",
)
USES = {
    "thm:reciprocal-absolute-remainder-series",
    "lem:reciprocal-all-radii-parameter",
    "thm:reciprocal-complex-profiles",
    "thm:reciprocal-profile-holomorphy",
}
REDUCED_EDGES = {
    "thm:reciprocal-absolute-remainder-series",
    "thm:reciprocal-profile-holomorphy",
}


def check_blueprint(blueprint):
    pages = [p.read_text(encoding="utf-8") for p in blueprint.glob("sect*.html")]
    anchor = f'id="{LABEL}">'
    (page,) = [page for page in pages if anchor in page]
    node = page.split(anchor, 1)[1].split('<div class="theorem_thmwrapper', 1)[0]
    heading = node.split('class="thm_header_hidden_extras"', 1)[0]
    assert "✓" in heading, "Main theorem is missing its formalization marker"
    links = re.findall(r'href="([^"]+)" class="lean_decl"', node)
    assert set(links) == {f"{DOCS_URL}/find/#doc/{name}" for name in DECLARATIONS}
    assert len(links) == len(DECLARATIONS)
    uses_panel = node.split("<h1>Uses</h1>", 1)[1].split("</ul>", 1)[0]
    assert set(re.findall(r'<a href="[^"]+#([^"]+)"', uses_panel)) == USES

    graph = (blueprint / "dep_graph_document.html").read_text(encoding="utf-8")
    edges = set(re.findall(r'"([^"]+)"\s*->\s*"' + re.escape(LABEL) + '"', graph))
    assert edges == REDUCED_EDGES, edges
    print(f"{LABEL}: formalized, three declaration links, four Uses, two reduced edges")


def check_api(docs):
    finder = (docs / "find/find.js").read_text(encoding="utf-8")
    assert 'view == "doc"' in finder and "result.docLink" in finder
    assert 'src="./find.js"' in (docs / "find/index.html").read_text(encoding="utf-8")
    index = json.loads((docs / "declarations/declaration-data.bmp").read_text(encoding="utf-8"))
    module_html = (docs / MODULE).read_text(encoding="utf-8")
    for name in DECLARATIONS:
        destination = index["declarations"][name]["docLink"].removeprefix("./")
        assert destination == f"{MODULE}#{name}", destination
        assert f'id="{name}"' in module_html, name
        print(f"{DOCS_URL}/find/#doc/{name} -> {DOCS_URL}/{destination}")


if __name__ == "__main__":
    site = Path(sys.argv[1])
    check_blueprint(site / "blueprint")
    check_api(site / "docs")
