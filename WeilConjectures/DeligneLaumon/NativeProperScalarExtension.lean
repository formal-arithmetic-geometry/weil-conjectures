/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ScalarDirectImageMateCoherence
public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.SectionModuleOperationsData
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import WeilConjectures.DeligneLaumon.NativeProperScalarExtensionIntegralCase
import WeilConjectures.DeligneLaumon.NativeProperScalarExtensionFiniteCase

/-! # Native proper scalar extension and mate normalization

Source: blueprint latest, det-sp-integral-direct-image-tower (2), and
sec-six-functors-basics/sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md.
(blueprint: lem-dla1-native-proper-scalar-extension).

All categories here are the ordinary unbounded derived categories of internal modules
for the independently pulled-back condensed rings. Scalar change is the existing
K-flat balanced extension; direct image is the total derivation of module direct image.
The comparison is the existing specified counit mate, not a chosen isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u w v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The adjoint of `G f` followed by the mate of `τ⁻¹` is `τ⁻¹` followed by `H` of the
adjoint of `f`: expand both Hom bijections by their counits and use `mateEquiv_counit`
and naturality of `τ⁻¹`. -/
private lemma homEquiv_symm_map_comp_mateEquiv_app {A B A' B' : Type*} [Category* A]
    [Category* B] [Category* A'] [Category* B'] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} (adj' : L' ⊣ R') (G : A ⥤ A') (H : B ⥤ B')
    (τ : L ⋙ H ≅ G ⋙ L') {M : A} {N : B} (f : M ⟶ R.obj N) :
    (adj'.homEquiv _ _).symm
        (G.map f ≫ (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ τ.inv)).natTrans.app N) =
      τ.inv.app M ≫ H.map ((adj.homEquiv _ _).symm f) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    mateEquiv_counit, Functor.map_comp]
  exact τ.inv.naturality_assoc f _

/-- Proper scalar comparison for precisely integral rationalization and finite field
extension. Equality in the arrow category identifies the entire coefficient map,
including both endpoints, without replacing its induced scalar action.

Source: det-sp-integral-direct-image-tower (2); scalar-six direct-image proof,
localization, finite-free extensions and preservation
(blueprint: lem-dla1-native-proper-scalar-extension).

Proof:
1. A field is Noetherian. Finite type makes Z and Y Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Closed-subset minimality and
   lem-sfb-noetherian-space-compact-subsets make the required opens quasi-compact;
   p is qcqs. Characteristic zero remains allowed.
2. lem-sfb-internal-scalar-pullback-normalization identifies the balanced comparison
   with scalarDirectImageMate, the transpose of the actual scalar-changed counit.
3. For O_E to E, boundedness implies bounded below. Apply
   lem-sfb-localized-direct-image-comparison to this qcqs p.
4. For E to F, sk-prop-sfb-cartesian-coefficients makes F finite free over E.
   Apply lem-pur-finite-free-proper-scalar-comparison. The normalized internal/section
   scalar adjunction identifies its mate with the same scalarDirectImageMate;
   injectivity of the Hom bijection identifies the maps, independently of a basis.
5. Integral rationalization is exact by lem-weil-pbc-continuous-integral-scalar-exact
   and its left-adjoint property. Finite-free extension is exact. Both preserve
   cohomological bounds and finite scalar presentations on every stratum; torsion
   models are allowed to become zero.
6. lem-dla1-native-reduction-proper-direct-image gives integral proper preservation;
   lem-per-condensed-finite-extension-direct-image gives field preservation over
   every k with ell invertible. Apply step 5 on Z and on Y to obtain all four
   bounded-constructibility conclusions. There is no exceptional adjunction or
   absolute cohomological-dimension assumption.
-/
theorem nativeProperScalarExtension
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [PerfectField k]
    (hell : IsUnit (ell : k))
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (ha : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Arrow.mk a = Arrow.mk
          (CommMon.homMk
            (A := CommMon.mk (Profinite.padicIntegersRingObj ell E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E)))) ∨
      (∃ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        Arrow.mk a = Arrow.mk
          (CommMon.homMk
            (A := CommMon.mk (Profinite.continuousMapRingObj E.1))
            (B := CommMon.mk (Profinite.continuousMapRingObj F.1))
            (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell h)))))
    {Z Y : Scheme.{u}} (aZ : Z ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (p : Z ⟶ Y) [IsProper p] (hp : p ≫ aY = aZ)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
    (hK : constantModelBoundedConstructible Λ.X Z K) :
    IsIso ((scalarDirectImageMate a p).app K) ∧
      constantModelBoundedConstructible Λ'.X Z ((scalarSixChange a Z).obj K) ∧
      constantModelBoundedConstructible Λ.X Y
        ((RootCoordinateFace.lower Λ.X p).obj K) ∧
      constantModelBoundedConstructible Λ'.X Y
        ((scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X p).obj K)) ∧
      constantModelBoundedConstructible Λ'.X Y
        ((RootCoordinateFace.lower Λ'.X p).obj ((scalarSixChange a Z).obj K)) := by
  classical
  rcases ha with ha | ha
  · rcases ha with ⟨E, ha⟩
    have hleft := congrArg Arrow.left ha
    have hright := congrArg Arrow.right ha
    cases hleft
    cases hright
    have ha' : a = CommMon.homMk
        (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E)) := by
      exact Arrow.mk_injective _ _ ha
    cases ha'
    exact nativeProperScalarExtension_integral_case ell k hell E aZ aY p hp K hK
  · rcases ha with ⟨E, F, hEF, ha⟩
    have hleft := congrArg Arrow.left ha
    have hright := congrArg Arrow.right ha
    cases hleft
    cases hright
    have ha' : a = CommMon.homMk
        (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell hEF)) := by
      exact Arrow.mk_injective _ _ ha
    cases ha'
    exact nativeProperScalarExtension_finite_case ell k hell E F hEF aZ aY p hp K hK

/-- The specified proper scalar map retains the actual mate formula, both adjunction
identities, and transposition of every arrow. These equations hold on the ambient
categories, so they apply to all units and counits, not just constructible objects.

Source: scalar-six direct-image proof, Formal properties; node proof steps 2 and 9
(blueprint: lem-dla1-native-proper-scalar-extension).

Proof: expand the defining mate as the target unit followed by direct image of c
and of the scalar-changed source counit. Apply
lem-sfb-scalar-direct-image-mate-coherence for its two adjunction equations.
For an arrow v : N to Rp K, substitute gamma composed with T(v) in the target
Hom bijection. The counit equation and naturality of c identify the transpose
with c followed by T of the source transpose. The unit equation gives inverse
transposition. All units, counits and adjunctions are the recorded ones.
-/
theorem nativeProperScalarExtension_transposition
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z),
      (scalarDirectImageMate a p).app K =
        (RootCoordinateFace.adjunction Λ'.X p).unit.app
            ((scalarSixChange a Y).obj ((RootCoordinateFace.lower Λ.X p).obj K)) ≫
          (RootCoordinateFace.lower Λ'.X p).map
            ((scalarDirectImagePullbackData.theta a p).inv.app
                ((RootCoordinateFace.lower Λ.X p).obj K) ≫
              (scalarSixChange a Z).map
                ((RootCoordinateFace.adjunction Λ.X p).counit.app K))) ∧
    (∀ N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y),
      (scalarSixChange a Y).map ((RootCoordinateFace.adjunction Λ.X p).unit.app N) ≫
          (scalarDirectImageMate a p).app ((scalarSixPull Λ p).obj N) =
        (RootCoordinateFace.adjunction Λ'.X p).unit.app ((scalarSixChange a Y).obj N) ≫
          (RootCoordinateFace.lower Λ'.X p).map
            ((scalarDirectImagePullbackData.theta a p).inv.app N)) ∧
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z),
      (scalarSixPull Λ' p).map ((scalarDirectImageMate a p).app K) ≫
          (RootCoordinateFace.adjunction Λ'.X p).counit.app ((scalarSixChange a Z).obj K) =
        (scalarDirectImagePullbackData.theta a p).inv.app
            ((RootCoordinateFace.lower Λ.X p).obj K) ≫
          (scalarSixChange a Z).map ((RootCoordinateFace.adjunction Λ.X p).counit.app K)) ∧
    (∀ (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
      (v : N ⟶ (RootCoordinateFace.lower Λ.X p).obj K),
      ((RootCoordinateFace.adjunction Λ'.X p).homEquiv _ _).symm
          ((scalarSixChange a Y).map v ≫ (scalarDirectImageMate a p).app K) =
        (scalarDirectImagePullbackData.theta a p).inv.app N ≫
          (scalarSixChange a Z).map
            (((RootCoordinateFace.adjunction Λ.X p).homEquiv _ _).symm v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K
    exact ((RootCoordinateFace.adjunction Λ'.X p).eq_unit_comp_map_iff
      ((scalarDirectImagePullbackData.theta a p).inv.app
          ((RootCoordinateFace.lower Λ.X p).obj K) ≫
        (scalarSixChange a Z).map
          ((RootCoordinateFace.adjunction Λ.X p).counit.app K))
      ((scalarDirectImageMate a p).app K)).2
      ((scalarDirectImageMateCoherence a p (𝟙 Y)).2.2.2.1 K)
  · intro N
    exact (scalarDirectImageMateCoherence a p (𝟙 Y)).2.2.1 N
  · intro K
    exact (scalarDirectImageMateCoherence a p (𝟙 Y)).2.2.2.1 K
  · intro N K v
    exact homEquiv_symm_map_comp_mateEquiv_app
      (RootCoordinateFace.adjunction Λ.X p)
      (RootCoordinateFace.adjunction Λ'.X p)
      (scalarSixChange a Y) (scalarSixChange a Z)
      (scalarDirectImagePullbackData.theta a p) v

/-- Composition and coefficient-tower equations for the actual comparisons.
They include composition on either side by a scheme isomorphism and its inverse;
the coefficient-tower equation also applies to integral quotient maps and transitions.

Source: scalar-six direct-image proof, Formal properties; node proof steps 7--8
(blueprint: lem-dla1-native-proper-scalar-extension).

Proof: invert the normalized pullback composition and scalar-tower squares and
apply mate pasting, as in lem-sfb-scalar-direct-image-mate-coherence. The derived
compositors are the adjunction conjugates and the scalar compositor is the balanced
tensor associator. This proves the equations before any evaluation. Specializing
composition to a scheme isomorphism and its inverse transports them through those
isomorphisms. Specializing successive coefficient change to the two paths of an
integral quotient square gives quotient compatibility, including all transitions.
No finite quotient of E is being treated as nonzero.
-/
theorem nativeProperScalarExtension_pasting
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y W : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ W) :
    (∀ K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z),
      (scalarDirectImageMate a (p ≫ q)).app K ≫
          (RootCoordinateFace.lowerComp Λ'.X p q).hom.app ((scalarSixChange a Z).obj K) =
        (scalarSixChange a W).map ((RootCoordinateFace.lowerComp Λ.X p q).hom.app K) ≫
          (scalarDirectImageMate a q).app ((RootCoordinateFace.lower Λ.X p).obj K) ≫
          (RootCoordinateFace.lower Λ'.X q).map ((scalarDirectImageMate a p).app K)) ∧
    (∀ (Λ'' : ScalarSixRing.{u}) (b : Λ' ⟶ Λ'')
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z)),
      (scalarSixTower a b Y).hom.app ((RootCoordinateFace.lower Λ.X p).obj K) ≫
          (scalarDirectImageMate (a ≫ b) p).app K =
        (scalarSixChange b Y).map ((scalarDirectImageMate a p).app K) ≫
          (scalarDirectImageMate b p).app ((scalarSixChange a Z).obj K) ≫
          (RootCoordinateFace.lower Λ''.X p).map ((scalarSixTower a b Z).hom.app K)) := by
  have h := scalarDirectImageMateCoherence a p q
  exact ⟨h.2.1, h.2.2.2.2⟩


/-- The identity direct-image comparison fixed by the actual derived adjunction,
using the ordinary identity pullback. It introduces no choice of adjunction.
Source: scalar-six direct-image proof, identity specialization; Stacks 07A6
(blueprint: lem-dla1-native-proper-scalar-extension). -/
def nativeProperScalarLowerId (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    RootCoordinateFace.lower Λ.X (𝟙 X) ≅
      𝟭 (DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :=
  (conjugateIsoEquiv Adjunction.id (RootCoordinateFace.adjunction Λ.X (𝟙 X))
    (Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
      Functor.mapDerivedCategoryIdIso _)).symm

/-- Transposing an identity-compatible restriction square preserves its unitors. -/
private lemma nativeScalarPullId
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {R : D ⥤ C} (adj : S ⊣ R)
    {F : C ⥤ C} {F' : D ⥤ D} (e : F ≅ 𝟭 C) (e' : F' ≅ 𝟭 D)
    (q : R ⋙ F ⟶ F' ⋙ R)
    (hq : ∀ N, q.app N ≫ R.map (e'.hom.app N) = e.hom.app (R.obj N)) (K : C) :
    ((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ q)).natTrans.app K ≫
        e'.hom.app (S.obj K) = S.map (e.hom.app K) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R.map_comp,
    ← Category.assoc]
  have hu := unit_mateEquiv_symm adj adj (TwoSquare.mk _ _ _ _ q) K
  change F.map (adj.unit.app K) ≫ q.app (S.obj K) =
    adj.unit.app (F.obj K) ≫ R.map
      (((mateEquiv adj adj).symm (TwoSquare.mk _ _ _ _ q)).natTrans.app K) at hu
  rw [← hu, Category.assoc, hq]
  simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map, Functor.comp_obj] using
    (e.hom.naturality (adj.unit.app K)).trans
      (adj.unit.naturality (e.hom.app K))

/-- A mate between identity adjunctions respects their conjugate right unitors. -/
private lemma nativeScalarMateId
    {C D : Type*} [Category C] [Category D]
    {A AR : C ⥤ C} {B BR : D ⥤ D} (adjA : A ⊣ AR) (adjB : B ⊣ BR)
    (S : C ⥤ D) (a : A ≅ 𝟭 C) (b : B ≅ 𝟭 D)
    (χ : S ⋙ B ⟶ A ⋙ S)
    (hχ : ∀ K, χ.app K ≫ S.map (a.hom.app K) = b.hom.app (S.obj K)) (K : C) :
    (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ χ)).app K ≫
        (conjugateEquiv adjB Adjunction.id b.inv).app (S.obj K) =
      S.map ((conjugateEquiv adjA Adjunction.id a.inv).app K) := by
  let r := conjugateEquiv adjB Adjunction.id b.inv
  have hm : (mateEquiv adjA adjB (TwoSquare.mk _ _ _ _ χ)).app K =
      adjB.unit.app (S.obj (AR.obj K)) ≫ BR.map (χ.app (AR.obj K)) ≫
        BR.map (S.map (adjA.counit.app K)) := by
    simp [mateEquiv]
  have hu := unit_conjugateEquiv adjB Adjunction.id b.inv (S.obj (AR.obj K))
  change adjB.unit.app _ ≫ r.app _ = 𝟙 _ ≫ b.inv.app _ at hu
  rw [Category.id_comp] at hu
  have hx := hχ (AR.obj K)
  have hx' : b.inv.app (S.obj (AR.obj K)) ≫ χ.app (AR.obj K) =
      S.map (a.inv.app (AR.obj K)) := by
    apply (cancel_mono (S.map (a.hom.app (AR.obj K)))).1
    rw [Category.assoc, hx, Iso.inv_hom_id_app]
    rw [← S.map_comp, Iso.inv_hom_id_app, S.map_id]
    rfl
  have hn : BR.map (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) ≫
      r.app (S.obj K) = r.app (B.obj (S.obj (AR.obj K))) ≫
        (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) := by
    simpa only [Functor.comp_obj, Functor.id_obj, Functor.id_map] using
      r.naturality (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K))
  calc
    _ = (adjB.unit.app (S.obj (AR.obj K)) ≫
        BR.map (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K))) ≫
          r.app (S.obj K) := by rw [hm, BR.map_comp]
    _ = (adjB.unit.app (S.obj (AR.obj K)) ≫ r.app (B.obj (S.obj (AR.obj K)))) ≫
        (χ.app (AR.obj K) ≫ S.map (adjA.counit.app K)) := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ adjB.unit.app (S.obj (AR.obj K)) ≫ z) hn
    _ = (b.inv.app (S.obj (AR.obj K)) ≫ χ.app (AR.obj K)) ≫
        S.map (adjA.counit.app K) := by rw [hu, Category.assoc]
    _ = S.map (a.inv.app (AR.obj K)) ≫ S.map (adjA.counit.app K) := by rw [hx']
    _ = _ := by rw [← S.map_comp, conjugateEquiv_adjunction_id]

/-- Restriction commutes with the ordinary geometric identity unitors: transpose
through the ordinary pull/push adjunctions, where the square is identity on sheaves. -/
private lemma nativeRestrictionPullId
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (N : ModuleRingedComparison.internalModules Λ'.X X) :
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).inv.app N ≫
        (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).map
          ((upperStarId Λ'.X X).hom.app N) =
      (upperStarId Λ.X X).hom.app
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).obj N) := by
  let R : ModuleRingedComparison.internalModules Λ'.X X ⥤
      ModuleRingedComparison.internalModules Λ.X X :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  have h : (TwoSquare.mk R (𝟙 X)^*⟦Λ'.X⟧ (𝟙 X)^*⟦Λ.X⟧ R
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).inv).whiskerLeft
        (upperStarId Λ'.X X).hom =
      (TwoSquare.vId R).whiskerRight (upperStarId Λ.X X).hom := by
    apply (mateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ.X (𝟙 X))).injective
    rw [mateEquiv_conjugateEquiv_vcomp Adjunction.id Adjunction.id
        (upperStarLowerStarAdjunction Λ.X (𝟙 X)),
      conjugateEquiv_mateEquiv_vcomp Adjunction.id
        (upperStarLowerStarAdjunction Λ'.X (𝟙 X))
        (upperStarLowerStarAdjunction Λ.X (𝟙 X)), comapUpperStarIso_mate]
    simp only [← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarId,
      Iso.symm_hom, TwoSquare.vId, mateEquiv_id_id_unitors]
    apply TwoSquare.ext
    intro M
    dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    change R.map ((lowerStarId Λ'.X X).inv.app M) ≫
        (comapLowerStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).hom.app M =
      (lowerStarId Λ.X X).inv.app (R.obj M)
    apply Mod.hom_ext
    change ((lowerStarId Λ'.X X).inv.app M).hom ≫
        ((comapLowerStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).hom.app M).hom =
      ((lowerStarId Λ.X X).inv.app (R.obj M)).hom
    dsimp only [comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom]
    erw [Category.comp_id]
    rfl
  have hN := congrArg (fun z ↦ z.natTrans.app N) h
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vId,
    TwoSquare.natTrans, TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app] at hN
  change (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).inv.app N ≫
      R.map ((upperStarId Λ'.X X).hom.app N) =
    (upperStarId Λ.X X).hom.app (R.obj N) ≫ 𝟙 _ at hN
  exact hN.trans (Category.comp_id _)

/-- The geometric identity comparison becomes the identity under the specified
adjunction-normalized identity identifications.
Source: scalar-six direct-image proof, Formal properties; node proof step 7
(blueprint: lem-dla1-native-proper-scalar-extension).

Proof: the ordinary restriction/pullback square respects identity unitors:
transpose it using comapUpperStarIso_mate and conjugateIsoEquiv_upperStarId,
then check the identity of underlying sheaf maps. The derived-square identity
lemma carries this equation to the ordinary unbounded derived categories.
The scalar-adjunction unit formula transposes it into identity compatibility
of theta. Transpose theta inverse through the geometric adjunctions. Naturality
and unit_conjugateEquiv identify the resulting right unitors with the exact
conjugates defining nativeProperScalarLowerId; their inverse laws finish.
-/
theorem nativeProperScalarExtension_identity
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u})
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarDirectImageMate a (𝟙 X)).app K ≫
        (nativeProperScalarLowerId Λ' X).hom.app ((scalarSixChange a X).obj K) =
      (scalarSixChange a X).map ((nativeProperScalarLowerId Λ X).hom.app K) := by
  let e := Functor.mapDerivedCategoryNatIso (upperStarId Λ.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let e' := Functor.mapDerivedCategoryNatIso (upperStarId Λ'.X X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let R : DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X) ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Λ.X X) :=
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory
  let adj : scalarSixChange a X ⊣ R := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  have hr (N : DerivedCategory (ModuleRingedComparison.internalModules Λ'.X X)) :
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).inv.app N ≫
          R.map (e'.hom.app N) = e.hom.app (R.obj N) := by
    have h := Functor.mapDerivedCategorySquareIso_hom_app_id
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).symm
      (upperStarId Λ'.X X) (upperStarId Λ.X X) (nativeRestrictionPullId a X) N
    simpa only [R, e, e', derivedComapUpperStarIso, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.symm_inv, ← Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using h
  have ht (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
      (scalarDirectImagePullbackData.theta a (𝟙 X)).hom.app M ≫
          e'.hom.app ((scalarSixChange a X).obj M) =
        (scalarSixChange a X).map (e.hom.app M) := by
    rw [scalarDirectImagePullbackData.thetaNormalization]
    exact nativeScalarPullId adj e e'
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom (𝟙 X)).inv hr M
  have hti (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
      (scalarDirectImagePullbackData.theta a (𝟙 X)).inv.app M ≫
          (scalarSixChange a X).map (e.hom.app M) =
        e'.hom.app ((scalarSixChange a X).obj M) := by
    rw [← ht M, Iso.inv_hom_id_app_assoc]
  exact nativeScalarMateId
    (RootCoordinateFace.adjunction Λ.X (𝟙 X))
    (RootCoordinateFace.adjunction Λ'.X (𝟙 X)) (scalarSixChange a X) e e'
    (scalarDirectImagePullbackData.theta a (𝟙 X)).inv hti K

/-- Evaluation preserving the counits and a pullback square preserves its mate.
The proof transposes once and then uses naturality and the mate counit equation. -/
private theorem nativeEvaluationMate
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}
    {P₁ : D₁ ⥤ D₂} {Q₁ : D₂ ⥤ D₁} {P₂ : D₃ ⥤ D₄} {Q₂ : D₄ ⥤ D₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (level₁ : P₁ ⊣ Q₁) (level₂ : P₂ ⊣ Q₂)
    {E₁ : C₁ ⥤ D₁} {F₁ : C₂ ⥤ D₂} {E₂ : C₃ ⥤ D₃} {F₂ : C₄ ⥤ D₄}
    (l₁ : L₁ ⋙ F₁ ≅ E₁ ⋙ P₁) (r₁ : R₁ ⋙ E₁ ≅ F₁ ⋙ Q₁)
    (l₂ : L₂ ⋙ F₂ ≅ E₂ ⋙ P₂) (r₂ : R₂ ⋙ E₂ ≅ F₂ ⋙ Q₂)
    (counit₁ : ∀ K, P₁.map (r₁.hom.app K) ≫ level₁.counit.app (F₁.obj K) =
      l₁.inv.app (R₁.obj K) ≫ F₁.map (adj₁.counit.app K))
    (counit₂ : ∀ K, P₂.map (r₂.hom.app K) ≫ level₂.counit.app (F₂.obj K) =
      l₂.inv.app (R₂.obj K) ≫ F₂.map (adj₂.counit.app K))
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {g : D₁ ⥤ D₃} {h : D₂ ⥤ D₄}
    (changeY : G ⋙ E₂ ≅ E₁ ⋙ g) (changeZ : H ⋙ F₂ ≅ F₁ ⋙ h)
    (c : TwoSquare G L₁ L₂ H) (d : TwoSquare g P₁ P₂ h)
    (hc : ∀ N, F₂.map (c.natTrans.app N) ≫ changeZ.hom.app (L₁.obj N) ≫
      h.map (l₁.hom.app N) = l₂.hom.app (G.obj N) ≫
        P₂.map (changeY.hom.app N) ≫ d.natTrans.app (E₁.obj N)) (K : C₂) :
    E₂.map ((mateEquiv adj₁ adj₂ c).natTrans.app K) ≫ r₂.hom.app (H.obj K) ≫
        Q₂.map (changeZ.hom.app K) =
      changeY.hom.app (R₁.obj K) ≫ g.map (r₁.hom.app K) ≫
        (mateEquiv level₁ level₂ d).natTrans.app (F₁.obj K) := by
  apply (level₂.homEquiv _ _).symm.injective
  change P₂.map _ ≫ level₂.counit.app _ = P₂.map _ ≫ level₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (l₂.hom.app (G.obj (R₁.obj K)))).1
  have hleft := l₂.hom.naturality ((mateEquiv adj₁ adj₂ c).natTrans.app K)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft]
  have hcounit := level₂.counit.naturality (changeZ.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  rw [hcounit]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (counit₂ (H.obj K))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp_assoc, mateEquiv_counit]
  rw [F₂.map_comp, Category.assoc]
  have hchange := changeZ.hom.naturality (adj₁.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hchange
  rw [hchange]
  rw [mateEquiv_counit]
  have htheta := d.natTrans.naturality (r₁.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at htheta
  rw [reassoc_of% htheta]
  rw [← reassoc_of% (hc (R₁.obj K))]
  rw [← h.map_comp, counit₁]
  rw [← h.map_comp, Iso.hom_inv_id_app_assoc]

/-- Finite evaluation of the specified scalar mate word, with the actual evaluation
comparisons of strict systems. The four unit/counit normalizations are exactly
those supplied by `SemilinearDerivedSectionsData.geometric`; scalar evaluation is
supplied by its coefficient-extension data. This is a statement about constructed
words, without assuming evaluation is faithful on derived morphisms.

Source: scalar-six direct-image proof, Formal properties; node proof step 8;
Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-dla1-native-proper-scalar-extension).

Proof: prove the evaluation equation for arbitrary categories and adjunctions,
then specialize. Transpose through the target geometric adjunction and precompose
with the invertible l₂ component. Naturality of l₂ and the counit, followed by
counit₂ and mateEquiv_counit, rewrites the evaluated mate. Naturality of changeZ
and theta inverse, hc, and counit₁ identify the two transposed words. Cancel l₁
with its inverse. The unit-normalization assumptions stay in the statement,
although the counit normalizations suffice for this proof. The argument applies
uniformly to the specified finite quotient evaluations, including zero reductions.
-/
theorem nativeProperScalarExtension_finiteEvaluation
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {C₁ C₂ C₃ C₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    (E₁ : C₁ ⥤ DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    (F₁ : C₂ ⥤ DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z))
    (E₂ : C₃ ⥤ DerivedCategory (ModuleRingedComparison.internalModules Λ'.X Y))
    (F₂ : C₄ ⥤ DerivedCategory (ModuleRingedComparison.internalModules Λ'.X Z))
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ R₁)
    {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃} (adj₂ : L₂ ⊣ R₂)
    (l₁ : L₁ ⋙ F₁ ≅ E₁ ⋙ scalarSixPull Λ p)
    (r₁ : R₁ ⋙ E₁ ≅ F₁ ⋙ RootCoordinateFace.lower Λ.X p)
    (l₂ : L₂ ⋙ F₂ ≅ E₂ ⋙ scalarSixPull Λ' p)
    (r₂ : R₂ ⋙ E₂ ≅ F₂ ⋙ RootCoordinateFace.lower Λ'.X p)
    (unit₁ : ∀ N : C₁,
      E₁.map (adj₁.unit.app N) ≫ r₁.hom.app (L₁.obj N) ≫
          (RootCoordinateFace.lower Λ.X p).map (l₁.hom.app N) =
        (RootCoordinateFace.adjunction Λ.X p).unit.app (E₁.obj N))
    (counit₁ : ∀ K : C₂,
      (scalarSixPull Λ p).map (r₁.hom.app K) ≫
          (RootCoordinateFace.adjunction Λ.X p).counit.app (F₁.obj K) =
        l₁.inv.app (R₁.obj K) ≫ F₁.map (adj₁.counit.app K))
    (unit₂ : ∀ N : C₃,
      E₂.map (adj₂.unit.app N) ≫ r₂.hom.app (L₂.obj N) ≫
          (RootCoordinateFace.lower Λ'.X p).map (l₂.hom.app N) =
        (RootCoordinateFace.adjunction Λ'.X p).unit.app (E₂.obj N))
    (counit₂ : ∀ K : C₄,
      (scalarSixPull Λ' p).map (r₂.hom.app K) ≫
          (RootCoordinateFace.adjunction Λ'.X p).counit.app (F₂.obj K) =
        l₂.inv.app (R₂.obj K) ≫ F₂.map (adj₂.counit.app K))
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
    (changeY : G ⋙ E₂ ≅ E₁ ⋙ scalarSixChange a Y)
    (changeZ : H ⋙ F₂ ≅ F₁ ⋙ scalarSixChange a Z)
    (c : TwoSquare G L₁ L₂ H)
    (hc : ∀ N : C₁,
      F₂.map (c.app N) ≫ changeZ.hom.app (L₁.obj N) ≫
          (scalarSixChange a Z).map (l₁.hom.app N) =
        l₂.hom.app (G.obj N) ≫ (scalarSixPull Λ' p).map (changeY.hom.app N) ≫
          (scalarDirectImagePullbackData.theta a p).inv.app (E₁.obj N))
    (K : C₂) :
    E₂.map ((mateEquiv adj₁ adj₂ c).app K) ≫ r₂.hom.app (H.obj K) ≫
        (RootCoordinateFace.lower Λ'.X p).map (changeZ.hom.app K) =
      changeY.hom.app (R₁.obj K) ≫ (scalarSixChange a Y).map (r₁.hom.app K) ≫
        (scalarDirectImageMate a p).app (F₁.obj K) := by
  have _ := unit₁
  have _ := unit₂
  exact nativeEvaluationMate adj₁ adj₂
    (RootCoordinateFace.adjunction Λ.X p) (RootCoordinateFace.adjunction Λ'.X p)
    l₁ r₁ l₂ r₂ counit₁ counit₂ changeY changeZ c
    (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a p).inv) hc K

end AlgebraicGeometry.ProEtale.CondensedRing
