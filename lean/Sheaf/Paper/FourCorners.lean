/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# The four finite-coefficient corners

Source: blueprint, proper base change, four corners; Stacks Project Tags 07A7 and 099M
(blueprint: def-weil-pbc-four-corners).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme


attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- Ordinary scalar extension, with objects and maps fixed by the tensor construction.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleRingExtension : proEtaleRingModules T R ⥤ proEtaleRingModules T S :=
  reductionChange T a

/-- The fixed scalar extension is additive. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-four-corners). -/
noncomputable instance proEtaleRingExtension_additive : (proEtaleRingExtension a).Additive :=
  reductionChangeAdditive T a

/-- Its universal left derived functor, including quotient-coefficient actions.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtension :
    DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory (proEtaleRingModules T S) :=
  reductionDerivedChange T a

/-- The universal derived counit comparing scalar extension with ordinary tensor.
Source: Stacks 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtensionCounit := reductionDerivedCounit T a

/-- The selected ordinary functor has the recorded tensor objects.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners).
Proof: this is the object-identification clause of the recorded derived-change-of-rings
existence theorem, specialized to its selected ordinary functor. -/
theorem proEtaleRingExtension_obj (M : proEtaleRingModules T R) :
    (proEtaleRingExtension a).obj M = SheafOfModules.changeOfRings a M := by
  sorry

/-- Reuse the published tensor-unit normalized ordinary scalar adjunction.
Source: Stacks 03D3, 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingExtensionAdjunction :
    proEtaleRingExtension a ⊣ proEtaleRingRestrictScalars a := pbcScalarAdjunction a

/-- Reuse the published universal-counit normalized derived scalar adjunction.
Source: Stacks 06YY, 0DVC (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingDerivedExtensionAdjunction :
    proEtaleRingDerivedExtension a ⊣ (proEtaleRingRestrictScalars a).mapDerivedCategory :=
  pbcDerivedScalarAdjunction a

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

/-- Reduction followed by finite pullback, in the inverse direction of chi, is the mate
of the canonical restriction/pullback identification. Its tensor-unit normalization fixes
the ordinary balancing map on K-flat representatives.
Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleReductionPullbackInv :
    proEtaleRingDerivedPullback f RV RU cR ⋙ proEtaleRingDerivedExtension aU ⟶
      proEtaleRingDerivedExtension aV ⋙ proEtaleRingDerivedPullback f SV SU cS :=
  (mateEquiv (proEtaleRingDerivedExtensionAdjunction aV)
    (proEtaleRingDerivedExtensionAdjunction aU)).symm
      (proEtaleRingRestrictionDerivedPullback f RV SV RU SU aV aU cR cS comm).inv

/-- The specified reduction/pullback mate is invertible in the quotient-coefficient
category itself. Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners).
Proof: choose a flat-term K-flat representative Q. Pullback preserves K-flatness and
flat terms, including for the identity-topos scalar-extension map. Hence all four derived
operations are computed by ordinary tensors on these representatives. The normalized
scalar and pullback adjunctions identify this mate with the balancing map
(u*Q) tensor SU → u_n*(Q tensor SV). Compatibility of the coefficient square makes this
SU-linear. Its inverse is the ordinary tensor reassociation. Both maps commute with
restriction and differentials, and localization preserves their inverse identities. -/
theorem proEtaleReductionPullbackInv_isIso :
    IsIso (proEtaleReductionPullbackInv f RV SV RU SU aV aU cR cS comm) := by
  sorry

/-- The coefficient-reduction comparison chi, in the displayed direction of the node.
Source: blueprint four corners; Stacks Tags 06YY and 0D6D
(blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleReductionPullbackIso :
    proEtaleRingDerivedExtension aV ⋙ proEtaleRingDerivedPullback f SV SU cS ≅
      proEtaleRingDerivedPullback f RV RU cR ⋙ proEtaleRingDerivedExtension aU :=
  (@asIso _ _ _ _ (proEtaleReductionPullbackInv f RV SV RU SU aV aU cR cS comm)
    (proEtaleReductionPullbackInv_isIso f RV SV RU SU aV aU cR cS comm)).symm

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Every level of the quotient ring tower is finite, including the zero quotient ring.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners).
Proof: level n is A/I^(n+1). The finite-quotient clause of the adic datum
gives its finiteness, including when the quotient is the zero ring. -/
theorem AdicCoefficientDatum.ringTower_finite (n : ℕᵒᵖ) : Finite (d.ringTower.obj n) := by
  sorry

attribute [instance] AdicCoefficientDatum.ringTower_finite

/-- The finite coefficient identification transported by the published constant comparison.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.finiteRingIso {U V : Scheme.{u}} (f : U ⟶ V)
    (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.finiteRing V n) ≅
      d.finiteRing U n :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcLevelConstantComparison V d n).symm ≪≫
    @asIso _ _ _ _ ((proEtaleConstantComparison f).app (d.ringTower.obj (op n)))
      ((proEtale_profinite_coefficient_inverse_image d.ringTower).1 U V f (op n)) ≪≫
    pbcLevelConstantComparison U d n

/-- The finite coefficient comparisons retain every quotient transition.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: the published constants-to-functions comparison commutes with quotient maps.
The constant inverse-image comparison is natural in the finite coefficient ring.
Combining their naturality squares with the limit cone equations gives this equation. -/
theorem AdicCoefficientDatum.integralRingComponent_naturality {U V : Scheme.{u}}
    (f : U ⟶ V) {m n : ℕᵒᵖ} (a : m ⟶ n) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V m.unop) ≫
        (d.finiteRingIso f m.unop).hom ≫ (reductionCoefficientSystem U d).map a =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V n.unop) ≫
        (d.finiteRingIso f n.unop).hom := by
  sorry

/-- The completed coefficient structure map is the actual limit lift of its projections.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.integralRingMap {U V : Scheme.{u}} (f : U ⟶ V) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V) ⟶
      d.completedRing U :=
  limit.lift (reductionCoefficientSystem U d)
    { pt := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V)
      π := { app n := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
                (d.projection V n.unop) ≫ (d.finiteRingIso f n.unop).hom
             naturality _ _ a := (Category.id_comp _).trans
               (d.integralRingComponent_naturality f a).symm } }

/-- The specified limit structure map is invertible by the profinite coefficient theorem.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: the published constant-system comparison identifies both coefficient limits
with the limits of finite constant quotients. Under these isomorphisms the displayed
limit lift has the projections of proEtaleProfiniteComparison, hence equals that map.
The profinite inverse-image theorem makes it invertible. No preservation of arbitrary
infinite limits is assumed. -/
theorem AdicCoefficientDatum.integralRingMap_isIso {U V : Scheme.{u}} (f : U ⟶ V) :
    IsIso (d.integralRingMap f) := by
  sorry

/-- The canonical profinite coefficient comparison in the published function presentation.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.integralRingIso {U V : Scheme.{u}} (f : U ⟶ V) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.completedRing V) ≅
      d.completedRing U :=
  @asIso _ _ _ _ (d.integralRingMap f) (d.integralRingMap_isIso f)

/-- The projection compatibility is exactly the projection clause of the canonical
profinite comparison. Source: blueprint four corners; Stacks Tag 098T
(blueprint: def-weil-pbc-four-corners).
Proof: specialize the projection identity of profinite-coefficient-inverse-image to the
quotient tower and its index n. The homs of asIso are the original comparisons. -/
theorem AdicCoefficientDatum.projection_comm {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    (d.integralRingIso f).hom ≫ d.projection U n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V n) ≫
        (d.finiteRingIso f n).hom := by
  sorry

/-- Ordinary integral derived pullback, without completion.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.pull {U V : Scheme.{u}} (f : U ⟶ V) :=
  proEtaleRingDerivedPullback f (d.completedRing V) (d.completedRing U) (d.integralRingIso f)

/-- Ordinary integral derived direct image in all modules.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.push {U V : Scheme.{u}} (f : U ⟶ V) :=
  proEtaleRingDerivedDirectImage f (d.completedRing V) (d.completedRing U) (d.integralRingIso f)

/-- Finite-coefficient derived pullback with its quotient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finitePull {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :=
  proEtaleRingDerivedPullback f (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso f n)

/-- Finite-coefficient derived direct image with its quotient action.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finitePush {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :=
  proEtaleRingDerivedDirectImage f (d.finiteRing V n) (d.finiteRing U n) (d.finiteRingIso f n)

/-- The canonical chi comparison with its original quotient coefficients retained.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.chi {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    d.reduction V n ⋙ d.finitePull f n ≅ d.pull f ⋙ d.reduction U n :=
  proEtaleReductionPullbackIso f (d.completedRing V) (d.finiteRing V n)
    (d.completedRing U) (d.finiteRing U n) (d.projection V n) (d.projection U n)
    (d.integralRingIso f) (d.finiteRingIso f n) (d.projection_comm f n)

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

include sq in
/-- Commutativity of integral coefficients around the square follows from the composite
coherence of the profinite comparison. Source: blueprint four corners; Stacks Tag 098T
(blueprint: def-weil-pbc-four-corners).
Proof: apply the composite-coherence clause to both paths and identify the composite
scheme morphisms using sq.w. Both maps are the canonical comparison for that morphism;
their inverse maps agree because both are isomorphisms. -/
theorem AdicCoefficientDatum.integral_coherent :
    HEq (proEtaleRingCompositeCoefficients g' f (d.completedRing Y) (d.completedRing X)
      (d.completedRing X') (d.integralRingIso f) (d.integralRingIso g'))
    (proEtaleRingCompositeCoefficients f' g (d.completedRing Y) (d.completedRing Y')
      (d.completedRing X') (d.integralRingIso g) (d.integralRingIso f')) := by
  sorry

include sq in
/-- The same composition identity for each finite coefficient level.
Source: blueprint four corners; Stacks Tag 098T (blueprint: def-weil-pbc-four-corners).
Proof: apply the finite-level composite-coherence clause of the profinite comparison
along both paths of sq; identify the scheme composites by sq.w. -/
theorem AdicCoefficientDatum.finite_coherent (n : ℕ) :
    HEq (proEtaleRingCompositeCoefficients g' f (d.finiteRing Y n) (d.finiteRing X n)
      (d.finiteRing X' n) (d.finiteRingIso f n) (d.finiteRingIso g' n))
    (proEtaleRingCompositeCoefficients f' g (d.finiteRing Y n) (d.finiteRing Y' n)
      (d.finiteRing X' n) (d.finiteRingIso g n) (d.finiteRingIso f' n)) := by
  sorry

/-- The canonical ambient exchange with integral completed coefficients.
Source: blueprint four corners; Stacks Tag 07A7 (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.integralExchange :=
  proEtaleAmbientRingedExchange sq (d.completedRing X) (d.completedRing Y)
    (d.completedRing X') (d.completedRing Y') (d.integralRingIso f) (d.integralRingIso g)
    (d.integralRingIso g') (d.integralRingIso f') (d.integral_coherent sq)

/-- The same canonical ambient exchange with the actual finite quotient coefficients.
Source: blueprint four corners; Stacks Tag 07A7 (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev AdicCoefficientDatum.finiteExchange (n : ℕ) :=
  proEtaleAmbientRingedExchange sq (d.finiteRing X n) (d.finiteRing Y n)
    (d.finiteRing X' n) (d.finiteRing Y' n) (d.finiteRingIso f n) (d.finiteRingIso g n)
    (d.finiteRingIso g' n) (d.finiteRingIso f' n) (d.finite_coherent sq n)

/-- Four corners at one positive finite level. Index n denotes the paper's n+1.
These use ordinary pullback of K, including when no completeness condition is needed to
form the objects. Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.fourCorners (K : d.derived X) (n : ℕ) :
    Fin 4 → DerivedCategory (proEtaleRingModules Y' (d.finiteRing Y' n)) :=
  ![(d.finitePull g n).obj ((d.reduction Y n).obj ((d.push f).obj K)),
    (d.finitePull g n).obj ((d.finitePush f n).obj ((d.reduction X n).obj K)),
    (d.reduction Y' n).obj ((d.push f').obj ((d.pull g').obj K)),
    (d.finitePush f' n).obj ((d.finitePull g' n).obj ((d.reduction X n).obj K))]

/-- The comparison delta is chi inverse at K, with quotient coefficients intact.
Source: blueprint four corners (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.delta (K : d.derived X) (n : ℕ) :
    (d.reduction X' n).obj ((d.pull g').obj K) ≅
      (d.finitePull g' n).obj ((d.reduction X n).obj K) :=
  (d.chi g' n).symm.app K

end AlgebraicGeometry.Scheme
