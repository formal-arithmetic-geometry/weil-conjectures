# AGENTS.md

This directory is one project: formalizing a paper in Lean 4, over Mathlib, with many agents working at once. Read this file first, then the document of your role and the documents of the stages that are open, which `coord/STATE.md` names. The three stages are three kinds of work on a node, and they overlap: which stage a node is in follows from its own state, never from a calendar (`roles/maintainer.md` §6).

## 1. Who you are

Your first prompt says who you are and which role document is yours.

| You are | Started by | Read next |
|---|---|---|
| the maintainer | the launcher | [`roles/maintainer.md`](roles/maintainer.md) |
| the lead of a group | the launcher | [`roles/lead.md`](roles/lead.md) |
| a worker on one item | a lead, as a sub-agent | [`roles/worker.md`](roles/worker.md) |
| the lead of a group on another machine | the launcher on that machine, with the group name and the server login | [`roles/remote-lead.md`](roles/remote-lead.md), after `roles/lead.md` |
| the launcher of groups on another machine | the human on that machine, with the server login, a prefix and a number of groups | [`roles/remote-launcher.md`](roles/remote-launcher.md) |

A worker is started by its lead as a separate agent (in Claude Code, a sub-agent of the `Agent` tool) with the lead's brief as its whole prompt; in any other agent system, any separately started agent given that brief and its item is the worker. `SETUP.md` ("The machine") records what this run used and the equivalents.

The launcher is the agent the human talks to. It works outside this directory: it started the project, keeps the sessions running, and brings the questions in `coord/HUMAN.md` to the human. A launcher on another machine (`roles/remote-launcher.md`) starts the groups there and keeps them running; it does no work on the project itself.

A session that starts from this file alone reads, in this order: `SETUP.md` (the human's settings, the machine, the decisions of the run and their reasons), `GOAL.md` (the target), `coord/STATE.md` (where the run stands, what is in progress, the numbers), its role document, the open stage documents, `tools/README.md` (the scripts and the regeneration of what git does not hold), and `coord/ledger.md` when it needs the history of a change.

## 2. The project directory

This directory is the project, and a git repository of its own. Everything you read and write is in it.

```
AGENTS.md  roles/  stages/   the contract: how each role works, and what each stage produces
tools/                       scripts for the few operations that must be exact (tools/README.md)
SETUP.md                     the human's settings and requirements; every agent follows them
GOAL.md                      the goal of every agent: the targets and the completion criterion
literature/                  the papers and textbooks the proofs follow; LIST.md lists those obtained and those wanted, and how
                             to fetch them (only the lists, the citation tables and import-tools/ are in git)
dag/nodes/                   the DAG, one JSON file per node; dag/units/ and dag/chapters/ the blueprint's units and chapters
                             as records (stages/1-dag.md §6); dag/notes/ the remarks and section texts of the import
lean/                        the Lean project; group sandboxes in lean/.sandbox/<group>/
coord/                       what the agents and the human tell each other: STATE.md, HUMAN.md, ledger.md,
                             reports/<group>/ and returns/<group>.md (deliveries of groups on other machines),
                             targets-review.md, the queue, claims, changes, settings
local/                       what this machine builds for itself; not committed, except the compressed sorry maps
```

## 3. One library, many agents

All agents work on one Lean library and compile against it, so a wrong file in it stops everyone who imports it. Four rules keep it usable; the role documents say how each role carries them out.

- Agents compile single files only. Only the maintainer builds the library.
- A file enters the library by landing, which a lead does after reviewing it, never by copying.
- Every landing is verified by the maintainer's global build. When one fails it, the maintainer repairs the build or reverts the landing.
- What you compile against is the last green global build, plus what your own group has landed since.

The scripts in `tools/` carry this out; [`tools/README.md`](tools/README.md) says which does what. They are one implementation, written for one machine and one project, and the maintainer changes them when they do not fit this one. If a script refuses correct work, lets wrong work through or does not fit the project, report it (§6); do not work around it and do not edit it yourself.

## 4. The targets

The project is accepted when two things hold (`GOAL.md`):

1. **Lean comparator accepts it.** [Lean comparator](https://github.com/leanprover/comparator) checks the library against `lean/Challenge.lean`: every target is proved with exactly the statement written there, using no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
2. **`Challenge.lean` says what the paper says.** Every target statement, read together with the definitions it uses, means exactly what the statement in the paper means: no hypothesis added, none dropped, no conclusion weakened, no definition that differs from the paper's. The comparator cannot check this; it is checked by a review (`stages/2-statements.md` §4).

So the target statements change only on the human's instruction. A change to a definition that a target statement uses can change what the target means without changing its text: it reopens the second check for that target. Never weaken a statement to make it provable.

## 5. Standards

- A target is proved when `#print axioms` shows nothing beyond `propext`, `Classical.choice`, `Quot.sound`.
- No hollow definitions. A definition is hollow when its data is written as `sorry`: everything built on it then proves something about an unknown object. A definition may take its data from a theorem that is still `sorry` when the theorem determines the object up to the equality used downstream, as an inverse does from a bijection not yet proved or a universal property does for its unique object; only the proof is postponed. Data chosen from a mere existence theorem whose proof is `sorry` and whose statement does not determine the object is forbidden: write the object as a real construction and state its properties as theorems about that construction. A proof that a definition itself needs is stated as a named theorem of its own, which the definition refers to, not left inside it as `sorry`.
- Every `sorry` you leave is a named theorem with its source and a complete natural-language proof in its docstring, and a DAG node matching it, so that anyone can take it over from those two alone.
- Test a new statement on its edge cases before writing it. Mark one you believe false with `STATEMENT-DISPUTED: <reason>` and report it; a false lemma makes everything above it look proved.
- The number of `sorry`s is not a measure of progress.

## 6. When the process fails

The process of this project is what lets many agents work on one library. When you notice something going against it, a rule that does not fit, a tool that misbehaves, an agent working around the contract, handle it at once if it is yours to handle; otherwise report it upward: a worker to the agent that gave it the work, a lead to the maintainer, the maintainer in `coord/HUMAN.md`, which the launcher brings to the human.

## 7. Groups on other machines

The repository on the server (`~/weil-conjectures-sheaf`, branch `sheaf-dag`) is the one meeting point; GitHub only mirrors it. A group on another machine pulls the state from the server, claims on the server over ssh, works on its own clone and delivers each item as a branch `deliver/<group>/<item>` pushed to the server; the maintainer merges it (`roles/remote-lead.md`, `roles/maintainer.md` §7). The maintainer's duties and files stay with the maintainer, whatever the group.

