## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentTorusAbsorption`
states `AlgebraicGeometry.split_unipotent_torus_absorption` with one `sorry`.
It introduces no definitions and proves nothing. The original node statement and
proof are unchanged. Its statement dependencies gain the three already landed
notion nodes `def-sfb-solvable-group-structure`, `def-sfb-split-unipotent-series`,
and `def-sfb-tori-multiplicative-type`; their definitions are used directly.

Source read: Milne, Algebraic Groups (2017), Proposition 16.54 and proof, printed
p.344, in the local PDF (PDF page 356). This states that maximal split tori are
images of sections and that any two sections are conjugate under the rational
unipotent kernel. The source imposes no perfection assumption here. The theorem's
docstring records the node's six-step crossed-homomorphism proof, including the
Laurent coefficient calculation, rational lifting via split-unipotent torsors,
and the direction of the accumulated conjugation.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any field k is `{k : Type u} [Field k]`. There are no characteristic,
  infinitude, perfection, or algebraic-closedness hypotheses on k.
- The four objects are `Grp (Over (Spec (.of k)))`: actual group schemes over k,
  with their structural multiplication, inverse and identity maps.
- Affine and finite type U is `_hU : SolvableGroupStructure.IsAlgebraic U`,
  namely `IsAffine U.X.left`, `LocallyOfFiniteType U.X.hom` and
  `QuasiCompact U.X.hom`.
- Smoothness and a faithful finite dimensional representation, with all geometric
  points unipotent, are `_hunip : SolvableGroupStructure.IsUnipotent U`.
  Its exact definition includes `Smooth U.X.hom`, a closed immersion into
  `GeneralLinearGroup (ULift (Fin n)) k`, and for every algebraically closed
  field extension and point an exponent N>0 with `(r(x)-1)^N=0`.
- Geometric connectedness is `_hgeo : GeometricallyConnected U.X.hom`.
  The class tests connectedness after every field-valued base change.
- The finite descending split additive series is
  `_hsplit : ∃ m : ℕ, SplitUnipotentLength U m`. At each successor this uses
  closed normal inclusion, smooth connected terms, and the actual homomorphism
  to the recorded additive group representing the fppf quotient. The length-zero
  case is the trivial group. The node asks for geometrically connected terms;
  the existing definition's connected terms are equivalent: each group has its
  rational identity section, and a connected scheme over a field with a section
  is geometrically connected. This is also the upstream theorem
  `GeometricallyConnected.of_connectedSpace_of_section` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`, whose
  signature and proof were read. No geometric-connectedness clause is lost.
- D is split of arbitrary nonnegative rank by
  `_hD : ∃ r : ℕ, Nonempty (D ≅ MultiplicativeType.splitTorus k r)`.
  This is a group-scheme isomorphism, not only an underlying scheme isomorphism.
- The action is the actual k-scheme morphism `act : D.X ⊗ U.X ⟶ U.X`.
  `_hunit` renders `1 · x = x`; `_haction` renders `(de) · x = d · (e · x)`;
  `_haut` renders `d · (xy) = (d · x)(d · y)`. The action identity supplies the
  inverse action of d⁻¹, so these are group automorphisms, including preservation
  of identity and inverse, not merely multiplicative endomorphisms.
- H is the semidirect product in product-scheme coordinates:
  `e : H.X ≅ U.X ⊗ D.X` gives precisely its underlying product, and `_hmul`
  gives precisely `(u,d)(v,e)=(u(d · v),de)`. The equation holds for all points
  of every test scheme X. These are the defining data and law of the semidirect
  product, not an extra group-theoretic assumption. Quantifying over a product
  presentation permits the canonical product and every isomorphic presentation.
  The law fixes multiplication, hence also identity and inverse uniquely. There
  is no unspecified group law, arbitrary comparison map, or Nonempty choice.
- All identities are quantified over `X : Over (Spec (.of k))`. They are exactly
  scheme-morphism identities by Yoneda, equivalently the specified identities on
  commutative k-algebras. Thus this introduces no additional action hypothesis.
- Every closed split torus is `(i : T ⟶ H)` with
  `[IsClosedSubgroupScheme i.hom.hom]` and
  `_hT : ∃ s : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k s)`.
  The former includes the subgroup monomorphism and closed immersion; the
  bundled morphism i already preserves the group operations.
- The rational unipotent conjugator is
  `u : 𝟙_ (Over (Spec (.of k))) ⟶ U.X`, i.e. a k-point.
- Inclusion `uTu⁻¹ ⊆ {1} × D` is the conclusion's identity
  `(toUnit T.X ≫ lift u 1 ≫ e.inv) * i.hom.hom *
   (toUnit T.X ≫ lift u 1 ≫ e.inv)⁻¹ = lift 1 v.hom.hom ≫ e.inv`
  for some homomorphism `v : T ⟶ D`. On the left the constant pair (u,1)
  is transported to H by e.inv, and multiplication and inverse are H's group
  operations. On the right the U-coordinate is identically 1. Factorization
  through D is equivalent to the asserted subgroup-scheme containment, and v
  is necessarily the D-projection of the conjugated inclusion. It is a group
  morphism automatically, so requiring that type does not strengthen inclusion.
- Because this is an equality of k-scheme morphisms from T, evaluation on every
  commutative k-algebra, including rings with nilpotents, gives the exact scalar
  extension assertion. It is not only a statement about k-points or geometric points.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `CategoryTheory.GrpObj` and bundled `CategoryTheory.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Grp` (def-sc-group-scheme).
- `Smooth`, `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  (def-sbc-smooth-morphisms), inside `IsUnipotent` and the split series.
- `ConnectedSpace`, `Mathlib.Topology.Connected.Basic`
  (def-weil-connected-scheme), in the split series.
- `LocallyOfFiniteType`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  and `QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  (def-weil-finite-type-morphism), in `IsAlgebraic`.
- `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  (def-sc-group-scheme-subgroup).
- `StandardGroupSchemes.additive`, `additiveGroup`, `multiplicative`,
  `multiplicativeGroup`, `Sheaf.AlgebraicGeometry.StandardGroupSchemes`
  (def-sc-gm-ga), through the recorded split-series and split-torus definitions.
- `SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`, `IsFppfQuotient`,
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`
  (def-sfb-solvable-group-structure).
- `SplitUnipotentLength`,
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries`
  (def-sfb-split-unipotent-series).
- `MultiplicativeType.splitTorus`,
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`
  (def-sfb-tori-multiplicative-type).
- `GeometricallyConnected`, `Mathlib.AlgebraicGeometry.Geometrically.Connected`,
  supplies the explicit geometric-connectedness class used with the connected
  scheme notion. It is not redefined.

Statement dependencies are publicly imported, directly or through their owning
public dependency modules. The stated proof dependency
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry` is imported
without `public`. The fppf and quasi-compact/quasi-separated/finite-presentation
Mathlib proof dependencies have plain imports. The stable-series and affine
split-unipotent torsor-section proof nodes currently have no Lean records, so
there are no modules for those two proof-only imports yet; they remain in the DAG.

Edge cases checked before writing: m=0 gives U=1; rank r=0 gives D=1; rank s=0
gives T=1; n=0 is allowed in the faithful matrix representation, consistently
with the trivial group. The group identity ensures schemes in the split series
are nonempty. Fields of every positive characteristic and imperfect/finite fields
are included. The Laurent argument also includes the zero character and rank-zero
torus. Test algebras are not required reduced, fields, or flat over one another.
The universes are explicitly bound, with no automatic implicits. All objects live
in the common ambient scheme universe u; the all-scheme equations are morphism
identities and therefore persist under enlargement of test-algebra universes.

Searches actually run with msearch.py for Q107 and this item:

- LeanFinder: "Every split torus in a semidirect product of a split unipotent
  algebraic group and a split torus is conjugate into the torus by a rational point".
  Eight hits, including `SemidirectProduct.inr_splitting`, `GroupExtension.IsConj`,
  `SemidirectProduct.right_splitting`, and `SemidirectProduct.inl_aut`. Their
  abstract-group signatures do not state algebraic-group rational conjugacy.
- Loogle: `SemidirectProduct, IsConj`: zero hits.
- Mathlib grep: `SplitTorus|splitTorus|[Uu]nipotent`, subdirectory AlgebraicGeometry:
  zero hits.
- LeanSearch: "A closed split torus of a semidirect product of a split unipotent
  group and a split torus is conjugate into the second factor by a rational point
  of the unipotent group". Eight hits, again abstract-group extension/conjugacy
  definitions and elementary identities, with no matching theorem.
- rg over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for unipotence, split tori, split series and
  semidirect products located the three existing notion modules above. The
  exact theorem name and blueprint id did not occur in existing Lean modules.
  Searching for action definitions found particular distribution and character
  actions, not a competing group-scheme semidirect-product construction.
- rg for the item id in `lean/WeilConjectures` returned no matches.

Validation: scompile.py compiled both the sandbox module and its final library
module name cleanly (2026-10-24), with no errors or unexpected warnings. An initial
probe lacked `open scoped MonObj` for the standard group operation instances on
Hom; that was corrected before the successful compile. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED flag is needed.

## Second reading by Q107

This is the worker's second pass with the node and final module open; the dispatch
brief forbids starting another agent. Independent maintainer review follows delivery.
I rechecked that the multiplication in `_hmul` uses the D-coordinate of x acting
on the U-coordinate of y, followed by the product of D-coordinates; neither the
factor order nor the conjugation direction has been reversed. The conclusion uses
u*i*u⁻¹, whereas the proof accumulates w⁻¹, so its choice u=w_m⁻¹ is correct.
The torus witnesses are isomorphisms in Grp, closedness uses the recorded subgroup
class, and the geometric-connectedness requirement on series terms follows from
their rational identity sections. The three action laws have no circular conjugacy
hypothesis. The H presentation has an actual scheme isomorphism and the entire
semidirect law, so it does not replace that construction by an arbitrary map.
I also checked all three rank/length-zero cases and the all-algebra conclusion.
The only change found necessary during checking was opening Mathlib's MonObj
scope; no mathematical signature clause was changed or omitted.
