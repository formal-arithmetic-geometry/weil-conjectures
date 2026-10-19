# Q79 stage-1 report: sk-def-set

## Files written

- `dag/nodes/sec-poincare-duality/sk-def-set.json` — definition; no Mathlib match for the complete fixed setting.
- `dag/units/sk-def-set.json` — realized statement field set to `sk-def-set`.
- `citations.json` — empty because this definition has no proof steps.

## Attachments

None. `AlgebraicGeometry.PoincareDualitySetting` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/AlgebraicGeometry/PoincareDualitySetting.lean:75` is a sorry-free project declaration, but it packages only the geometric model and its smooth, separated, quasi-compact and geometrically connected instances. It does not state the coefficient stages or exceptional-adjoint clauses of this item, so it is not an attachment.

## WANTED

None.

## What was wrong in the imported node

The imported dependency list contained `sk-def-sf-operations`, downstream duality nodes, and unavailable identifiers such as `sk-thm-sf-ctf-stability`, `sk-rem-sf-fullcd-scope`, `sk-cor-trace`, and `sk-thm-derived-duality`. The operation definition depends on this setting, so retaining it created the imported cycle flagged by `import_flags`. I rewrote the statement to preserve the blueprint meaning while citing only existing upstream nodes: `sk-def-sf-setting`, `thm-sf-ambient-adjoint-class`, `sk-prop-sf-rf-shriek-preservation`, `thm-sf-ctf-stability`, and `sk-def-sf-admissible`. No mathematical hypothesis was added; the explicit exclusion of properness and of ambient admissibility remains.

## What I could not finish

Nothing. No new node was needed: the item is a definition assembled from existing notions and clauses.

## Review by Q79

I read the current item source `literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-def-set/_section.md`, the unit record, and the complete slopmaster2 source file `WeilConjectures/AlgebraicGeometry/PoincareDualitySetting.lean`. The source declaration at lines 75–82 was compared clause by clause and found strictly weaker than the DAG item, which is why I split rather than attached it. I also opened each retained statement dependency. `sk-def-sf-setting` supplies the finite-field and coefficient-stage datum; `thm-sf-ambient-adjoint-class` supplies the constructible exceptional adjoint; `sk-prop-sf-rf-shriek-preservation` and `thm-sf-ctf-stability` supply existence/preservation on the stated separated finite-type domain; and `sk-def-sf-admissible` is used only to record that the optional ambient datum is not assumed. There are no proof steps, so there are no step citations or quote obligations. I checked the edge cases represented by the definition: relative dimension `d=0`, a nonproper smooth separated finite-type model, and each of the four coefficient stages; none introduces a hidden properness or admissibility hypothesis. I ran both phrasings of the required LeanFinder, Loogle, grep, and LeanSearch searches; they found only component Mathlib predicates and no declaration for the complete setting. The server check reported `check_dag OK: no finding introduced by the sandbox or on its nodes`.

## Second reading by Q79

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-poincare-duality/sk-def-set/_section.md`, hypothesis by hypothesis; the finite-field and coefficient datum, smooth relative dimension, separated finite type, geometric connectedness, exceptional-adjoint qualification, and exclusion of properness are present.
- Item statement: checked against `AlgebraicGeometry.PoincareDualitySetting` at `WeilConjectures/AlgebraicGeometry/PoincareDualitySetting.lean:75–82`; that declaration supplies only the geometric model, so no Lean attachment is appropriate. Its documented compact-support/properness convention agrees with the item.
- Proof steps: none (the item is a definition), so there are no step dependencies or citation quotes to audit.
- New nodes: none; the complete fixed setting is the item itself, and the Mathlib/Lean searches recorded in the node found only component predicates or unrelated adjunctions.
- Dependency statements: opened `sk-def-sf-setting`, `sk-def-sf-operations`, `sk-prop-sf-existence`, `thm-sf-ambient-adjoint-class`, `sk-prop-sf-rf-shriek-preservation`, `thm-sf-ctf-stability`, and `sk-def-sf-admissible`; each supplies the coefficient, operation, existence, or preservation clause cited, with no downstream dependency retained.
- Edge cases: the statement permits dimension `d=0`, nonproper smooth separated models, and all four coefficient stages; no empty-scheme, field, or coefficient-stage case adds a hidden properness or admissibility assumption.
- Changes made: restored the source’s explicit `Ra_X^!` operation reference and the existing `sk-def-sf-operations` and `sk-prop-sf-existence` dependencies; retained the source’s properness and ambient-datum qualifications in self-contained prose without unavailable forward tags; removed the stray duplicate `dag/units-sk-def-set.json` file.
