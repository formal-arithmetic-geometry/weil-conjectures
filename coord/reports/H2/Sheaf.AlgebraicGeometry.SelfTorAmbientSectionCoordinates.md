## What changed

Replaced the sole sorry in
`AlgebraicGeometry.exists_selfTor_ambient_section_coordinates` by a complete Lean proof.
The signature, universes, visibility, and public imports of the existing theorem are unchanged.
The proof obtains affine tensor-complex homology coordinates for one localized comparison,
composes them with `ProjectiveResolution.isoLeftDerivedObj.toLinearEquiv`, identifies the
quotient maps by surjectivity, applies the proved algebraic tensor-lift homotopy, and cancels
the target projective homology isomorphism against its inverse. `Homotopy.homologyMap_eq`
gives naturality for every supplied augmented comparison, exactly with the original q.

Added `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy`, whose public theorem
`ModuleCat.quotient_tensor_resolution_lift_homotopy` is fully proved. Its private helpers
construct the projective comparison homotopy into an arbitrary exact augmented complex
and the semilinear tensor components explicitly. In particular, the argument does not
assume that restricted target resolution terms are projective. All data definitions have
complete proofs and real constructions.

Added `Sheaf.AlgebraicGeometry.SelfTorAmbientLocalizedComparisons` for the remaining
geometric computation, on tensor-complex homology rather than Tor, and only for one
localized comparison per basic inclusion. This separates the geometric construction from
the now-proved independence and Tor transport. Updated the original DAG node and added
two nodes corresponding to the new public declarations. The unit's realized lists are empty;
the original affine resolution/K-flat route stays below that unit.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_selfTor_ambient_section_coordinates`
(node `new-a3-self-tor-ambient-section-coordinates`): 1 of 1 original holes removed.

Proved without sorry: `ModuleCat.quotient_tensor_resolution_lift_homotopy`
(node `new-h2-quotient-tensor-resolution-lift-homotopy`). Its helper lemmas and
`quotientTensorLift` are also fully proved. The general ring-map statement needs no
flatness assumption and supplies an actual homotopy, in every degree.

Added and remaining: `AlgebraicGeometry.exists_selfTor_ambient_localized_comparisons`
(node `new-h2-self-tor-ambient-localized-comparisons`), with proof exactly `by sorry`.
This is the only sorry in the delivered files. It covers sheafification, the K-flat
computation, affine homology sections, and naturality for one localized lift. It does
not contain the arbitrary-lift comparison or algebraic Tor transport proved here.

This is a decomposition with net hole count 0 (one original hole closed, one lower
hole added), plus a complete proof of the algebraic comparison part. The original
theorem still depends on the remaining geometric hole, so it is not an axiom-free
completion of the target branch. All three delivery modules compile without warnings.
An explicit `#print axioms` check on the algebraic theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. The delivery dry run also checks the compiled declarations.

## No longer needed

Removed the four direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`,
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`,
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`, and
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`.
They now occur in the new geometric computation module, whose proof plan still needs
their nodes. They have therefore not been pruned from the target import closure.
The old proof dependencies `lem-sc-affine-quotient-resolution-sheafification`,
`lem-pc-bounded-above-flat-kflat`, `lem-pc-affine-derived-pullback-tensor-tilde`,
and `lem-pc-kflat-derived-tensor-comparison` are no longer direct dependencies of
the original node; all four remain dependencies of the new geometric node.
No existing node or module is claimed as globally unnecessary; genuine pruning: none.
The new algebraic module needs neither ModuleCat.Projective nor Monoidal.Tor imports;
these were removed after compilation. The new homology coordinate statement also needs
no Monoidal.Tor import. No public import of the existing item was removed.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The planned invocation of projective comparison
must be understood as projectivity of the source only: restriction of scalars need not
preserve projectives for an arbitrary ring map. The implemented induction uses exactness
of the restricted target and projectivity of P_j, and proves the needed semilinear tensor
homotopy directly. Mathlib's `ProjectiveResolution.liftHomotopy` requires a target
projective resolution, so it cannot simply be applied to the restricted resolution.

The Stacks sources were read at Tags 00LS(1)-(2), 08DX(2), and 06YG. All geometric
edge cases are unchanged: degree zero, top ideals, empty basic opens, and zero rings.
The algebraic proof uses neither nonzero rings nor positive degree. For top ideals the
quotient tensor source is zero; for zero target rings all target terms and equations are
handled by the same linear maps. The zero-degree homotopy is constructed separately
from the positive-degree induction, as required by the source.

## New nodes

`new-h2-quotient-tensor-resolution-lift-homotopy`: a proved purely algebraic comparison
for arbitrary ring maps and arbitrary projective resolutions. Its proof constructs the
homotopy by exact/projective lifting and tensors the components through the quotient map.
The node records the actual Mathlib searches and the projective comparison source.

`new-h2-self-tor-ambient-localized-comparisons`: the remaining sourced geometric
computation on tensor-complex homology, with one comparison witness per basic inclusion.
The proof plan uses the original geometric dependencies and projective resolution lifting;
its statement is strictly the geometric construction portion, before independence of lifts
and before Tor transport. Both new nodes retain the original chapter and unit, and the
blueprint ancestor `lem-sc-finite-duality`. No change record or forced adaptation is needed.


## Second reading by H2

1. Compared the existing module against the repository with `diff -u` and the
   declaration parser. Verdict: the existing signature is byte-for-byte unchanged;
   universes, visibility, definitions, docstring, and public imports are unchanged.
   Only its proof, declaration-local heartbeat allowance, and private proof imports
   changed. Both other modules are new; no existing consumer is adapted.
2. Compiled all three delivered modules in import order using `lcompile.py --all`:
   clean, without warnings (4.2, 4.5, and 16.6 seconds). Read the entire algebraic
   induction and tensor construction. The only remaining sorry is the whole proof
   of `AlgebraicGeometry.exists_selfTor_ambient_localized_comparisons`. No forbidden
   declaration or hollow definition occurs. Independent scratch `#print axioms`
   checks show only propext, Classical.choice and Quot.sound for the algebraic
   theorem, and those plus sorryAx for the geometric and original theorems.
   The original result is therefore a decomposition, not an axiom-free completion.
3. Read the new geometric statement, its docstring, its node, and the original
   geometric dependencies. Verdict: it is the sourced affine tensor-homology
   computation with one comparison lift, strictly omitting the now-proved
   independence of lifts and Tor transport. Checked degree zero, top ideals,
   identity basic inclusions, empty basic opens and zero rings: the construction
   uses ordinary quotient/localization maps and remains valid. The tensor-lift
   theorem works for arbitrary ring maps because only the source terms need to
   be projective; restriction of scalars preserves exactness. Its tensor map is
   explicitly constructed, with no data selected from the geometric sorry.
   Rechecked Stacks Tags 00LS(1)-(2), 08DX(2), and 06YG. Independent searches with
   `leanfinder` (affine sections of derived tensor homology), `loogle`
   (`"Homotopy", "Projective"`), `msearch.py grep` (derivedTensor_tilde and
   tensor homotopy), and `rg` on both Lean roots found supporting APIs but no
   duplicate geometric statement. Mathlib's liftHomotopy needs a projective
   target resolution, so it does not replace the exact-target induction here.
   Closing the geometric computation is not a short remaining algebraic step.
4. Read the proof from the original conclusion downward: quotient-map
   surjectivity identifies psi, the proved tensor homotopy equates homology maps,
   and inv_hom_id cancels precisely the Tor transport in the original q.
   Verdict: no missing hypothesis or weakened conclusion. The new public imports
   provide signature types/instances; proof-only imports are private. The four
   old proof-dependency nodes are relocated, not globally pruned, as now named
   explicitly above. The unit `sk-thm-picard-duality` has realized statement []
   and steps [[]]; no realized node or unit route is bypassed.
5. Compared all three node records with their Lean declarations and proofs.
   Verdict: recorded statements match verbatim, the existing node changes only
   proof, proof_deps and proof_origin, and both new nodes have the required source,
   searches, creation, blueprint, chapter, unit and Lean fields. The original
   node depends exactly on the two new results; the geometric node retains all
   four old dependencies and adds the projective lifting dependency. The
   algebraic node describes the implemented exact/projective lifting induction
   and tensor extension, with no unreported hole.

Second reading changed only this report: added the five review verdicts and
explicitly named the four relocated old proof-dependency nodes. No Lean or DAG
repair was necessary. One original hole is closed and one strictly lower geometric
hole is added; net holes closed is zero, and globally pruned modules are none.
