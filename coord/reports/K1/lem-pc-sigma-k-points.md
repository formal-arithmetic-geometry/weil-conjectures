# Stage 1 report: lem-pc-sigma-k-points

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-sigma-k-points.json` (item; split, no new nodes)
- `citations.json` (one verbatim citation for the proof step)

## Attachments

None. No exact sorry-free declaration for this item was found in `WeilConjectures/`.

## WANTED

None.

## What was checked

The item source is the imported blueprint node `sk-def-picard-pic/lem-pc-sigma-k-points.md` (node order 807). I read the definitions of `picardFunctorNormalized` and its normalized presheaf in `WeilConjectures/AlgebraicGeometry/Picard/Defs.lean`; at `T = Spec(k)` the definition is the kernel of pullback along the base-changed section. I also read the existing node `lem-pc-pic-of-field`, whose statement supplies exactly the needed fact that every invertible module on `Spec(k)` is trivial.

The sole proof step specializes the normalized Picard definition to `T = Spec(k)`. The section is the given `sigma`, and its pullback map has target `Pic(Spec(k))`. By `lem-pc-pic-of-field` this target is trivial, so the map is zero and its kernel is all of `Pic(X)`; the resulting equality is the canonical inclusion/kernel identification. The citation quote in `citations.json` is copied verbatim from that node's statement. No additional non-elementary fact is used, and the remaining specialization and kernel calculation are elementary.

I searched the whole DAG and blueprint for an equivalent node and found none. The Lean source contains related rational-point and degree-zero results, but no declaration tagged or stating this general item without `sorry`. Required Mathlib searches were run: LeanFinder and Loogle returned only unrelated/general ring Picard declarations, grep found no match, and LeanSearch was unavailable (recorded as unavailable in the node).

## Review by K1

I checked the item statement against the blueprint source and the normalized Picard definitions, including the hypotheses that `k` is a field, `X` is a `k`-scheme, and `sigma` is a `k`-point. I opened `lem-pc-pic-of-field.json` and verified that its statement says precisely that the target Picard group is trivial; this is the only cited node used by step 1. The step's use of the kernel and the specialization to `Spec(k)` are elementary consequences of the definitions. I tested the edge case `X = Spec(k)` and the trivial line bundle: both sides are the singleton Picard group, and the argument still gives the canonical equality. No statement or dependency was changed, and no new node was created because the proof uses no fact beyond the existing field lemma.

## What was wrong or incomplete in the imported node

The imported node had `status: imported`, unset blueprint `from`/`same_as`, no search records, and no split report. These metadata gaps were repaired. Its proof and dependency on `lem-pc-pic-of-field` were mathematically adequate.

## What could not be finished

Nothing; the sandbox is ready for dry run.

## Second reading by K1

- Item statement: checked against blueprint node `lem-pc-sigma-k-points` (order 807), hypothesis by hypothesis; verdict: agrees for a field `k`, a `k`-scheme `X`, and `sigma \in X(k)`.
- Step 1: checked against the definition of `picardFunctorNormalized` and the statement of `lem-pc-pic-of-field`; verdict: specialization to `T = Spec(k)` and the kernel identification are elementary, while triviality of the target is exactly the cited node.
- Dependency citation: opened `lem-pc-pic-of-field.json`; verdict: the verbatim quote in `citations.json` matches its statement and supplies the only non-elementary fact used.
- Edge cases: checked `X = Spec(k)`, the trivial line bundle, and fields of arbitrary characteristic; verdict: both sides and the kernel calculation remain correct.
- Existing-node and blueprint search: searched the DAG and blueprint with `rg` and `tools/blueprint_refs.py search`; verdict: no duplicate or smaller existing node is available, and no blueprint statement subsumes this lemma.
- Mathlib/Lean search: reviewed the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results; verdict: no exact declaration, so this remains a split item.
- Form checks: the item has statement-only content, a boolean elementary field on its sole step, `proof_deps` equal to its cited use, and blueprint `from`/`same_as` metadata.

Changes made in this second reading: verified the imported item's `blueprint.from` remains `null` as required for a blueprint-imported node, and expanded this review section. No mathematical statement or proof dependency was changed.

## Repair of returned delivery

The maintainer's return identified three points. First, the normalized Picard definition is now listed in `stmt_deps`, `proof_deps`, and step 1 `uses`; the step explicitly uses its kernel description and records the canonical identifications $X_{\\operatorname{Spec} k}=X$ and $\\sigma_{\\operatorname{Spec} k}=\\sigma$. The maintainer separately removes the forward pointer from that definition's dependencies, so this citation does not form a cycle. `citations.json` now includes a verbatim quote from the definition node as well as the field Picard quote. Second, the proof no longer calls $\\sigma$ a closed immersion: it only observes that $\\sigma^*\\mathcal L$ is invertible on $\\operatorname{Spec}(k)$ and applies `lem-pc-pic-of-field`, which is valid for an arbitrary $k$-rational point. Third, the imported item's `blueprint.from` remains `null`, as required by the preflight for blueprint-imported nodes; the earlier report claim that it had been filled was corrected.
