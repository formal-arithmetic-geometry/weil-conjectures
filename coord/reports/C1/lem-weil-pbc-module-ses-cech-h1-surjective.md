# Stage 1 worker report: `lem-weil-pbc-module-ses-cech-h1-surjective`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-module-ses-cech-h1-surjective.json`: the existing draft splits the statement into six proof steps, with no new nodes. It also repairs a truncated `blueprint.from.place` and records `blueprint.same_as = []`.

## Source and dependencies

I read Stacks Cohomology of Sheaves, Tag 01EU, `lemma-ses-cech-h1`, in `literature/stacks-project/cohomology.tex:1593-1635`. Its ringed-space statement specializes to a scheme with its structure sheaf, with the same short exact sequence, cofinal family of open covers, vanishing Cech H1, and surjectivity on sections. The proof follows the source's local-lift, refinement, difference-cocycle, correction, and gluing argument.

1. `def-weil-pbc-exact-sequence` supplies monicity, epicity and the image-kernel equality; `def-weil-sheaf-of-modules-category` states that module-sheaf kernels are sectionwise. Thus each difference has a unique preimage in the kernel sheaf.
2. Epicity makes the module-sheaf cokernel zero. `def-weil-sheaf-of-modules-category` identifies it with the sheafification of sectionwise quotients, and `lem-weil-pbc-sheaf-cokernel-local-image` states that a section mapped to zero there has local lifts. `def-weil-pbc-sheafification` supplies the notation.
3. Cofinality refines that lift cover; restriction and naturality preserve the lifts. This is direct from the hypotheses and `def-weil-sheaf-of-modules-category`.
4. `def-weil-pbc-site-cech-complex` defines the degree-one cochains and alternating differential. On each triple intersection, the alternating sum of the differences is zero, so sectionwise injectivity gives a cocycle.
5. The same Cech definition gives H1 as cycles modulo boundaries. Its vanishing produces a zero-cochain; subtracting its image makes the local lifts agree on overlaps. The signs are `g_j-g_i` and `t_j-t_i` throughout.
6. The sheaf axioms in `def-weil-sheaf-of-modules-category` glue the compatible lifts and identify their image with the original section.

The cited local-image node belongs to the same unit, `sk-thm-p1`. Other cross-chapter citations are definitions or Mathlib leaves. No new result was needed. The original item was unsplit, and its `blueprint.from.place` had truncated text; the draft supplies the missing argument and a readable place. I searched the whole imported blueprint with `tools/blueprint_refs.py search` for `01EU`, `cech surjective`, and `vanishing Cech H1`; none stated this node exactly.

## Lean source search

I searched the read-only `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by concept and for the exact `(blueprint: lem-weil-pbc-module-ses-cech-h1-surjective)` tag. There is no exact declaration to attach. `TopCat.Presheaf.surjective_app_of_exactAt_cechComplex_one` at `WeilConjectures/Topology/Sheaves/CechCriterion.lean:231` is sorry-free according to `local/sorry_map_slopmaster2_full.jsonl.gz`, but assumes finite covers and abelian sheaves. The item permits arbitrary index sets of covers and concerns sheaves of modules, so this is a related theorem, not an exact attachment. No declaration with sorry was found for this node.

## Edge cases and checks

## Review by C1

I read Cohomology of Sheaves 01EU (`lemma-ses-cech-h1`) at `cohomology.tex:1593-1635`. Its ringed-space statement specializes to the item's scheme and O_X-modules with exactly the same short exactness, cofinal-cover vanishing and section-surjectivity hypotheses. Step 1 uses short exactness and the cited sheaf-of-modules definition, whose statement says kernels are sectionwise. Step 2 uses that definition's sheafified-cokernel clause and the separate local-image node to obtain local lifts. Step 3 refines the cover by cofinality and restriction naturality. Step 4 constructs differences and checks the alternating cocycle identity. Step 5 uses the Cech-complex node's cycles-mod-boundaries definition and correct signs to adjust lifts. Step 6 glues using the sheaf axioms. Each non-elementary fact comes from a cited statement, not a cited proof.

No new node or Mathlib leaf is introduced. The worker searched the current DAG and imported blueprint for 01EU and the cofinal Cech criterion; the finite-cover Lean analogue at `CechCriterion.lean:231` is narrower than the arbitrary-cover item and was correctly left unattached. I checked empty U, infinite index sets (products in the Cech complex), and zero kernel. The worker added the missing external report after my request. `review_split.py` passes; `check_dag.py` has no cycles and seven unrelated reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied.

For the empty open, the empty covering and the sheaf axiom give the unique zero section. The cocycle and correction steps also work for an arbitrary index set, including an infinite one, because the Cech terms are products. If the kernel sheaf is zero, the correction cochain is zero and the argument reduces to gluing local lifts. No extra compactness or finiteness assumption is used.

`python3 tools/review_split.py lem-weil-pbc-module-ses-cech-h1-surjective` passes with zero new nodes. `python3 tools/check_dag.py` reports zero cycles and seven unrelated existing reachability warnings. No WANTED source and no unfinished item work.
