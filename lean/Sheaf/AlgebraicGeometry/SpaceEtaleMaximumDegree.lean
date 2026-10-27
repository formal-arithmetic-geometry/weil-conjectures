/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Field.Defs
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.FlatFpLqfBoundedStratification
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The maximum-degree open of an affine etale atlas

Source: Stacks Project, Decent Spaces, Tags 03JX (lemma-bounded-fibres) and 07S8
(lemma-quasi-compact-reasonable-stratification); Cohomology of Spaces, Tag 089J
(lemma-weak-chow), first paragraph and induction on the degree
(blueprint: lem-sfb-space-etale-maximum-degree).

The fibre sizes below are cardinals of the existing point spaces of the literal sheaf
pullbacks. A finite cardinal bound therefore also asserts finiteness of every fibre.
The base scheme is Spec Z, lifted to the universe of the schemes under consideration.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine surjective etale atlas of a separated finite-type space over Spec A is
finite type over Spec A and has a uniform finite bound on its geometric fibre sizes.
For the empty space the bound can be chosen zero and the atlas is empty.

Source: Stacks, Tags 03JX and 089J
(blueprint: lem-sfb-space-etale-maximum-degree).

Proof:
1. Apply the chartwise local-finite-type hypothesis to the atlas and the identity
chart of Spec A. The resulting map W -> Spec A is between affine schemes, hence affine
(lem-weil-pbc-morphism-affine-schemes-affine), hence quasi-compact
(lem-weil-pbc-affine-morphism-permanence). It is therefore finite type.
2. The affine base is separated over Spec Z and the given space is separated over it,
so the space is absolutely separated and hence quasi-separated
(lem-sfb-space-separated-fp-composition, lem-weil-pbc-affine-source-morphism-separated,
def-weil-closed-immersion, lem-weil-pbc-affine-morphism-permanence).
3. The quasi-compact affine atlas has uniformly bounded geometric fibres by
lem-sfb-space-qc-etale-fibre-bound. Their scheme structures and base changes are those of
lem-trf-space-representable-etale-scheme-tests. This gives the natural bound b.
4. If X is empty, the point map W -> X makes W empty
(lem-a1-space-point-open-calculus); all its geometric fibres are empty and b = 0 works.
-/
theorem affine_etale_atlas_finite_type_bounded
    (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (W : Over (Spec (.of (ULift.{u} ℤ))))
    (g : X.obj.obj ⟶ yoneda.obj
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))))
    (f : yoneda.obj W ⟶ X.obj.obj) (hW : IsAffine W.left)
    (hsep : MapToSchemeIsSeparated X
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) g)
    (hqc : MapIsQuasiCompact g)
    (hft : MapToSchemeIsLocally (@LocallyOfFiniteType) X
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) g)
    (he : IsEtale f) (hs : IsSurjective f) :
    LocallyOfFiniteType (yoneda.preimage (f ≫ g)).left ∧
    QuasiCompact (yoneda.preimage (f ≫ g)).left ∧
    ∃ b : ℕ,
      (∀ (a : PointRepresentative X.obj.obj), IsAlgClosed a.K →
        Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm a.value))) ≤ b) ∧
      (IsEmpty (Point X.obj.obj) → b = 0 ∧ IsEmpty W.left) := by
  sorry

/-- For a nonempty separated finite-type space over Spec A, an affine surjective etale
atlas has a least positive fibre bound. The maximum-degree locus is a nonempty open
subspace, and every etale scheme test over it is finite etale with direct-image algebra
finite locally free of that rank. The reduced closed complement has an affine surjective
etale atlas obtained by base change, all of whose geometric fibres have smaller size.

Source: Stacks, Tags 03JX, 07S8 and 089J
(blueprint: lem-sfb-space-etale-maximum-degree).

Proof:
1. Use the finite bound above and surjectivity on geometric fibres to choose the least
natural bound d. Since X is nonempty, d is positive, and minimality implies it is attained
(lem-sfb-space-qc-etale-fibre-bound, lem-a1-space-point-open-calculus).
2. The atlas is quasi-compact by lem-sfb-space-qcqs-permanence. Its relative diagonal
is a base change of the closed absolute diagonal of the affine W, so it is separated
(lem-weil-pbc-affine-source-morphism-separated, lem-weil-pbc-closed-immersion-base-change,
lem-trf-space-representable-etale-scheme-tests).
3. By lem-sfb-space-etale-closed-degree-loci the locus of degree at most d-1 is closed.
Its complement is precisely the degree-d locus and is nonempty. Construct its open
subfunctor on scheme tests by the complementary open of the reduced closed subspace
(lem-sfb-space-reduced-closed-support, def-a1-space-open-subspace).
4. On a scheme test V, etale fibres are disjoint unions of spectra of finite separable
residue extensions (lem-weil-pbc-etale-fibre-discrete-separable-points). Over an algebraic
closure each factor splits (lem-pc-separable-tensor-algebraic-closure), so geometric point
count equals the finite fibre-algebra dimension, and is independent of the geometric lift.
5. The test map is flat, locally finitely presented, separated, and locally quasi-finite
(def-weil-etale-morphism, lem-weil-pbc-unramified-quasi-finite-at-points). Apply
lem-weil-pbc-flat-fp-lqf-bounded-stratification: every point is in its degree-d stratum,
so its universal property applied to id_V makes the map finite locally free of degree d.
It remains etale. Finite-flat pushforward identifies its direct-image structure algebra
as finite locally free of rank d (lem-pc-finite-flat-pushforward-locally-free,
lem-weil-pbc-finite-flat-rank-iso).
6. Give the complement its reduced closed structure
(lem-sfb-space-reduced-closed-support). Its pullback to W is a closed immersion, hence
affine since W is affine (def-weil-closed-immersion). The other projection is surjective
etale by lem-trf-space-representable-etale-scheme-tests. Associativity of the sheaf fibre
product (lem-trf-space-fibre-products-etale-covers) identifies its geometric fibres with
the original fibres off the maximum locus, whose sizes are strictly less than d.
For d = 1 the complement is empty, and empty scheme tests are permitted throughout.
-/
theorem exists_affine_etale_atlas_maximum_degree
    (A : Type u) [CommRing A]
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (W : Over (Spec (.of (ULift.{u} ℤ))))
    (g : X.obj.obj ⟶ yoneda.obj
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))))
    (f : yoneda.obj W ⟶ X.obj.obj) (hW : IsAffine W.left)
    (hsep : MapToSchemeIsSeparated X
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) g)
    (hqc : MapIsQuasiCompact g)
    (hft : MapToSchemeIsLocally (@LocallyOfFiniteType) X
      (Over.mk (specULiftZIsTerminal.from (Spec (.of A)))) g)
    (he : IsEtale f) (hs : IsSurjective f) (hne : Nonempty (Point X.obj.obj)) :
    ∃ (d : ℕ) (U : OpenSubspace X),
      1 ≤ d ∧
      IsLeast {b : ℕ | ∀ (a : PointRepresentative X.obj.obj), IsAlgClosed a.K →
        Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm a.value))) ≤ b} d ∧
      (pointImage U.val.ι).Nonempty ∧
      pointImage U.val.ι = {x | ∃ (a : PointRepresentative X.obj.obj),
        IsAlgClosed a.K ∧ Quot.mk _ a = x ∧
        Cardinal.mk (Point (Limits.pullback f (yonedaEquiv.symm a.value))) = d} ∧
      (∀ (V : Over (Spec (.of (ULift.{u} ℤ))))
        (a : yoneda.obj V ⟶ U.val.toFunctor), IsEtale (a ≫ U.val.ι) →
        ∃ (E : Over (Spec (.of (ULift.{u} ℤ)))) (p : E ⟶ V)
          (q : yoneda.obj E ⟶ yoneda.obj W),
          IsPullback q (yoneda.map p) f (a ≫ U.val.ι) ∧
          IsFinite p.left ∧ Etale p.left ∧
          ((Scheme.Modules.pushforward p.left).obj (𝟙_ E.left.Modules)).IsFiniteLocallyFreeOfRank
            d) ∧
      ∃ C : ClosedSubspace X,
        IsReduced (C.val : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) ∧
        pointImage C.val.arrow.hom.hom = (pointImage U.val.ι)ᶜ ∧
        ∃ (WT : Over (Spec (.of (ULift.{u} ℤ)))) (p : WT ⟶ W)
          (q : yoneda.obj WT ⟶ (C.val : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))).obj.obj),
          IsPullback (yoneda.map p) q f C.val.arrow.hom.hom ∧
          IsAffine WT.left ∧ IsEtale q ∧ IsSurjective q ∧
          ∀ (a : PointRepresentative
            (C.val : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))).obj.obj), IsAlgClosed a.K →
            Cardinal.mk (Point (Limits.pullback q (yonedaEquiv.symm a.value))) < d := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
