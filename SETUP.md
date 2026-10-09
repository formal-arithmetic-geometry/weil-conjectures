# SETUP

Fill in the table before starting the project. Any other requirement for how the project is run may be added below it; every agent follows this file.

| | |
|---|---|
| Paper to formalize | The natural-language blueprint of `github.com/formal-arithmetic-geometry/weil-conjectures`, branch `master` at `967897d1c5e775be739997d7e847a9205fae1359`, copied to `literature/blueprint/master/` (2,943 files); the blueprint of branch `slopmaster2` at `1ad77be92cebdbd62febaca30a77fa594d1a23a5` is in `literature/blueprint/slopmaster2/`. The commits are in `literature/blueprint/COMMITS.txt`. |
| Lean project location | default `lean/` (not created: no Lean is written yet) |
| Mathlib version | default the latest stable release (the source repository uses `leanprover/lean4:v4.33.1`) |
| Maximum concurrent subagents | 10 |
| Early review of the target statements by the human | default no |
| Reasoning effort of the agents | default `xhigh` for every agent |

## Facts of this project

- The DAG in `dag/nodes/` was not written by splitting from the target: it was imported from the blueprint on 2026-10-08 by `tools/import_blueprint.py`. The blueprint's proofs were written by agents, and every imported node records that.
- A Lean declaration recorded in a node is one of the source repository (the node says which branch), found by reading the source text; nothing was compiled, and this project has no `lean/` directory.

## Requirements of the human (2026-10-09)

- **Sessions.** One session runs the project: it is the maintainer and the only lead, and gives items to at most 10 workers at a time, started as sub-agents with model `fable`.
- **Only stage 1 is open.** No Lean is written and nothing is built. The Lean of the source repository is read, never changed: branch `master` in `~/weil-conjectures`, branch `slopmaster2` in `~/weil-conjectures-slopmaster2`, both compiled. Mathlib for searching is in `~/weil-conjectures-slopmaster2/.lake/packages/mathlib`.
- **What is finished.** Each node has `lean_audit`, read from the compiled source repository (`tools/sorry_map.lean`, `tools/lean_status.py`, `dag/lean_audit.json`). A node whose state on `slopmaster2` is `closed` is finished for stage 1: its Lean exists and no `sorry` is reachable from it. It is not split further.
- **What is an item.** Every other node a target reaches (`sorry_here`, `rests_on_sorry`, `none`) is an item until every branch below it ends in a Mathlib leaf, with the search recorded, or in a `closed` node.
  - `rests_on_sorry`: each declaration in its `open` list is a statement the Lean has split off. One with no node gets a node, stated from its Lean statement and docstring, and is then an item itself.
  - `dag/lean_audit.json` lists every declaration with `sorry` on each branch; 575 of the 608 on `slopmaster2` are named by no node. Each belongs to an existing node or becomes one.
- **Do not trust how finely the blueprint is split.** An imported proof is material, not a finished split. A node counts as split only after a worker has checked it against `stages/1-dag.md`: every step names the nodes it uses or is judged elementary (`elementary` is `null` on 767 steps: nobody has judged them), and an argument a step hides becomes nodes of its own. The `import_flags` of a node say what the import already found doubtful.
- **Proofs follow the literature.** The documents are in `literature/` (`LIST.md`, `CITATIONS.tsv`, `stacks-tags-cited.tsv`, the Stacks project source in `stacks-project/`). A proof is written from the document, with the place. When a document is not there: put it in the Wanted table of `literature/LIST.md` and ask for it in `coord/HUMAN.md` first; only then write the proof yourself, marked as written by an agent.
- **The graph has 21 cycles** (`tools/check_dag.py --cycles`), from text citations that are pointers and not dependencies. They are removed first.
