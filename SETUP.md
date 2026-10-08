# SETUP

Fill in the table before starting the project. Any other requirement for how the project is run may be added below it; every agent follows this file.

| | |
|---|---|
| Paper to formalize | The natural-language blueprint of `github.com/formal-arithmetic-geometry/weil-conjectures`, branch `master` at `967897d1c5e775be739997d7e847a9205fae1359`, copied to `literature/blueprint/master/` (2,943 files); the blueprint of branch `slopmaster2` at `1ad77be92cebdbd62febaca30a77fa594d1a23a5` is in `literature/blueprint/slopmaster2/`. The commits are in `literature/blueprint/COMMITS.txt`. |
| Lean project location | default `lean/` (not created: no Lean is written yet) |
| Mathlib version | default the latest stable release (the source repository uses `leanprover/lean4:v4.33.1`) |
| Maximum concurrent subagents | |
| Early review of the target statements by the human | default no |
| Reasoning effort of the agents | default `xhigh` for every agent |

## Facts of this project

- The DAG in `dag/nodes/` was not written by splitting from the target: it was imported from the blueprint on 2026-10-08 by `tools/import_blueprint.py`. The blueprint's proofs were written by agents, and every imported node records that.
- A Lean declaration recorded in a node is one of the source repository (the node says which branch), found by reading the source text; nothing was compiled, and this project has no `lean/` directory.
