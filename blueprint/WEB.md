# Formalization website

The **Publish formalization site** workflow builds the Lean API reference and the
Blueprint on a standard Ubuntu runner. It runs on changes under `lean/` on
`main` or when dispatched manually for a Blueprint-only change. GitHub Pages
must use GitHub Actions as its source. The deployment records its inputs in
`build-info.json`; the published API and Blueprint live under `docs/` and
`blueprint/`.

The Lean project remains under `lean/`. The workflow prepares the Mathlib
cache there, then runs the pinned upstream docgen-action build script from
that directory. Blueprint and Jekyll generation in the upstream action are
unused. The Blueprint build uses the commands below in a temporary copy of
`blueprint/src/`, retaining the adjacent `plastex.cfg`. Install BibTeX and the
AMS bibliography style (for example with Ubuntu's TeX Live packages) and use
Python 3 with the pinned packages shown in the workflow.

```sh
printf '%s\n' '\citation{*}' '\bibstyle{amsplain}' '\bibdata{references}' > web.aux
bibtex web
plastex --imager none --vector-imager none --plugins leanblueprint -c ../plastex.cfg web.tex
```

The site acceptance script, `python3 blueprint/check_web.py SITE_ROOT`, checks
the theorem marker, declaration links, declared Uses, reduced graph, and
the generated declaration index and anchors. The tracked print PDF is a
separate artifact.
