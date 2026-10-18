/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization
import Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Closed inverse image preserves limits

Source: blueprint, pro-etale coefficients, `sk-prop-sf-open-closed-triangle`,
`det-sf-open-closed-pullback-limits` (blueprint: det-sf-open-closed-pullback-limits).

A sheaf of rings is a monoid object in abelian sheaves, and its module sheaves are
`CategoryTheory.Mod`. This includes noncommutative rings. The canonical inverse image
is the existing `Functor.mapMod` applied to the monoidal sheaf inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme.AffineProEt

/-- The henselian lift viewed over the original scheme through an affine open chart.
Source: blueprint `det-sf-open-closed-pullback-limits`, clause (1), using the lift of
`def-exc-closed-site-lift` (blueprint: det-sf-open-closed-pullback-limits). -/
def closedSiteLiftOver {X : Scheme.{u}} (A : Type u) [CommRing A] (I : Ideal A)
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (V : (Spec (.of (A ⧸ I))).AffineProEt) : X.ProEt :=
  ProEt.mk (((toProEt (Spec (.of A))).obj ((closedSiteLift A I).obj V)).hom ≫ a)

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme

/-- Closed inverse image is evaluation on henselian lifts at weakly contractible
closed-site basis objects, and is exact and preserves small limits and colimits.
The affine chart is specified by the cartesian square `(A/I, Z, A, X)`. The object
`i⁻¹(v(V))` is canonically `V`, by the closed-fibre property of the henselian lift.
Thus the displayed component of the inverse-image adjunction unit is precisely the
canonical map `F(v(V)) → (i^*F)(V)`, after that canonical identification. No arbitrary
isomorphism or comparison arrow is selected. The two finite-preservation assertions
express exactness in the abelian categories of module objects.

Source: blueprint `det-sf-open-closed-pullback-limits`, clauses (1) and (2);
Bhatt--Scholze, Proposition 4.2.8 (blueprint: det-sf-open-closed-pullback-limits).

Proof:
1. Apply set inverse image to the addition, zero, negation, multiplication, unit
   and scalar-action maps. Finite-product preservation carries all ring and module
   identities to the inverse-image objects, without requiring commutativity. This
   is the module-object inverse image below, and it is additive.
2. Over an affine open Spec A, its closed fibre is Spec(A/I) by
   `lem-weil-pbc-closed-immersion-affine-cover-criterion`. Use
   `lem-exc-closed-localization` and
   `lem-weil-pbc-affine-closed-inverse-image-evaluation` on underlying set sheaves.
   The canonical evaluation bijections commute with products by their projections
   and naturality, hence with addition and scalar action. They give the module
   isomorphism in (1). The evaluation theorem concerns F composed with v; it does
   not assert that sheafification preserves every presheaf's value at V.
3. Compute a small set-sheaf limit sectionwise using
   `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`. Evaluation at each weakly
   contractible affine identifies its inverse-image comparison with the limit of
   evaluations at v(V). Weakly contractible covers from
   `lem-weil-pbc-ind-etale-basis-wcontractible-cover`, and basis detection from
   `lem-weil-pbc-ind-etale-basis`, make the comparison invertible. Separatedness
   gives injectivity; lift locally, compare on covered overlaps, and glue for
   surjectivity. This includes the empty diagram and the empty scheme.
4. Globalize by `lem-weil-pbc-proetale-inverse-image-limits-zariski-local`.
   Module limits are created on underlying sheaves by
   `lem-weil-pbc-module-sheaves-limits-sectionwise`. The comparison is linear by
   naturality, and its bijective underlying map has a linear inverse. This gives
   all small module limits.
5. Lift the inverse/direct-image adjunction to module objects. Give direct image
   its B-action through the ring unit. Naturality of the unit at the action maps,
   and its compatibility with product projections, identify linearity on both
   sides of the set-sheaf adjunction. Equivalently use the existing monoidal
   `Adjunction.mapModAdjunction`; it retains both distributive laws.
6. Module colimits exist by `lem-weil-pbc-module-sheaves-colimits-forgetful`.
   The lifted adjunction preserves them by
   `lem-weil-pbc-left-adjoint-preserves-colimits`. Together with kernel preservation
   from step 4 and additivity from step 1, cokernel preservation proves exactness.
   These are precisely the finite-limit and finite-colimit assertions below.
-/
theorem closed_inverseImage_preserves_limits
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (_hU : IsCompact ((Set.range i)ᶜ))
    (B : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) [MonObj B] :
    (∀ (A : Type u) [CommRing A] (I : Ideal A)
      (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
      (z : Spec (.of (A ⧸ I)) ⟶ Z)
      (_hchart : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z a i)
      (V : (Spec (.of (A ⧸ I))).AffineProEt),
      (ProEt.topology Z).IsWeaklyContractible.{u + 1}
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
            (AffineProEt.closedSiteLiftOver A I a V)) →
      ∀ F : Mod (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) B,
        IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app
          F.X).hom.app (op (AffineProEt.closedSiteLiftOver A I a V)))) ∧
    PreservesFiniteLimits ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesFiniteColimits ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesLimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) ∧
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} i).mapMod B) := by
  sorry

end AlgebraicGeometry.Scheme
