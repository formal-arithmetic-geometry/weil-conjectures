## What changed

Replaced the sole sorry of `Sheaf.Paper.QCohInverseAffineOpenVanishing` with a complete
Lean proof from existing declarations. The signature and public imports are unchanged.
Added a fully proved private `open_cohomology_restrict_iso`: restrict an injective
module resolution, compare sections complexes naturally, and commute homology with
exact scalar forgetting. The main proof converts hacyc into ordinary higher direct
image vanishing using the unbounded single-object comparison. It proves ordinary
open restriction directly with the same resolution, sectionwise pushforward
comparison, and exact restriction. Quasi-coherence and affine vanishing give the
Leray degeneration hypothesis; the edge has zero target in the chosen positive
degree, and its isomorphism transfers zero to open module cohomology.

Added proof-only imports `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`,
`Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`,
`Sheaf.Topology.ModuleCohomologyTopComparison`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`.
Updated only proof, proof_deps, and proof_origin of
`new-qcoh-inverse-affine-open-vanishing` to describe the actual argument.

Checked the source statements online at Stacks Tags
[01E1](https://stacks.math.columbia.edu/tag/01E1),
[01F4 (2)](https://stacks.math.columbia.edu/tag/01F4),
[01XJ (1)](https://stacks.math.columbia.edu/tag/01XJ), and
[01XB](https://stacks.math.columbia.edu/tag/01XB).
The local literature files are absent on this machine. The restriction-comparison
construction follows the sectionwise comparison in the existing
DerivedDirectImageOpenRestriction proof, deriving it in natural-number degrees
with restricted injective resolutions instead of passing through derived
categories on both opens. No object is defined by an arbitrary existence witness.

The initial full proof and the revised direct-resolution proof both compiled with
lcompile.py. The final proof is checked by deliver3.py --no-push. All added import
edges passed import_direction.py. No new module, interface change, or adaptation.

## Proved and sorry left

Closed: `AlgebraicGeometry.qcoh_acyclic_inverse_affine_open_vanishing`
(node `new-qcoh-inverse-affine-open-vanishing`), 1 of 1 original holes.
No sorry remains in the item's module. No sorry was added anywhere; no split-off
statements. The private helper `open_cohomology_restrict_iso` is fully proved.
This is a proof from existing declarations, not a new decomposition. It continues
to rely on existing library results, including
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage` (01XJ (1),
the quasi-coherence clause of `lem-pc-finite-support-hi`) and the results reached
by `AlgebraicGeometry.exists_lerayEdge_isIso_of_vanishing`.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`

Removed proof-dependency edges to `lem-pc-restrict-derived-direct-image-open`,
`lem-weil-pbc-exact-functor-bounded-below`, and `lem-pc-affine-vanishing`.
The ordinary open-restriction comparison is proved directly, without the unbounded
restriction theorem. Affine vanishing is used through the established
`pqf-lem-affine-vanishing` module interface. `lem-sp-derived-functor-single-identification`
remains a dependency of the single-object comparison, with PlusSingle supplied by
the retained PlusCompatibility import. The definition node
`def-pc-derived-direct-image` remains a statement dependency and public import,
so its redundant proof dependency was removed. Some removed direct imports remain
transitively reachable (notably Affine.Cech and PlusSingle); this report claims
pruned direct edges and unnecessary proof work, not their removal from the global
import closure. No other node or module is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

The existing node's route is sound, but can be implemented without derived
categories on the opens: exact open restriction of an injective resolution gives
ordinary higher-direct-image restriction directly. The source theorem
`nonempty_sections_higherDirectImage_iso_H` needs separatedness, whereas this
item assumes only quasi-separatedness; it was not used. The source's unproved
`nonempty_higherDirectImage_iso_restrict` could be applied after pullback/restriction
conversion, but the final delivery proves that comparison itself.

The Lean record of `lem-pc-finite-support-hi` points to a uniform-support theorem
in Projective. That declaration does not expose clause (1), although the node
statement and proof explicitly include it. The exact usable existing declaration
is `Scheme.Modules.isQuasicoherent_higherDirectImage` in DirectImage.Sections,
with the required qcqs hypotheses. The delivery uses it and identifies it in the
updated proof; it does not change the dependency's interface or node.

The unit `sk-thm-picard-duality` has empty realized statement and step lists; this
below-unit comparison does not bypass a required realized unit node. The final
statement treats empty affine opens uniformly, requires positivity only for the
chosen degree p, and applies quasi-coherence and affine vanishing in all natural
higher-direct-image degrees, including zero.

## Second reading by S2

1. **Repository comparison:** Diffed the delivered module against `lean/Sheaf/Paper/QCohInverseAffineOpenVanishing.lean`. The public theorem signature and all existing declarations are byte-for-byte unchanged; only proof text, proof-only imports, and the private helper differ. Verdict: pass.

2. **Proof and axioms:** Compiled the module with `python3 /home/ubuntu/weil-launcher/lcompile.py lean/Sheaf/Paper/QCohInverseAffineOpenVanishing.lean`; compilation succeeds with no errors. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The helper constructs restricted injective resolutions explicitly, so no arbitrary existence witness is used. Verdict: pass.

3. **Statements and split-offs:** No statements were split off and no new nodes were added. The private comparison lemma is an internal isomorphism proved from the existing restriction and homology APIs, not a restatement of the target. Existing imported declarations were searched locally; no duplicate theorem was introduced. Verdict: pass.

4. **Pruning and route:** The revised proof uses direct restricted injective resolutions and removes the former direct imports for derived open restriction, Cech/projective arguments, PlusSingle, and exact-functor infrastructure. The proof still uses the affine-vanishing, top-cohomology comparison, quasi-coherence, and Leray declarations required by its route. The unit route is not bypassed; the unit has no realized statement or steps to preserve. Verdict: pass.

5. **DAG agreement:** The node records the direct restriction comparison, the single-object derived comparison, quasi-coherence and affine vanishing, and Leray edge route used by the Lean proof. Its theorem statement and source remain unchanged; only proof, proof dependencies, and proof origin describe the revised route. Verdict: pass.

Changed during second reading: appended this review only; no Lean proof or interface changes were necessary.
