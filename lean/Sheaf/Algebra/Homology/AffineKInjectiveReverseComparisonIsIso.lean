/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.LeftExactHomologyComparison
import Sheaf.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-! # Invertibility of the affine K-injective cycle-class comparison

Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-kinjective-reverse-comparison-isIso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The reverse cycle-class comparison is invertible for an affine K-injective complex
with quasi-coherent cohomology. This concerns a single homology morphism; no descended
natural transformation, natural isomorphism, or uniqueness assertion is assumed.
Source: Stacks Project, Tag 0AVW, affine cohomology display; Tag 06Z0, affine derived
equivalence; Tag 01I9, pushforward of associated module sheaves.
(blueprint: lem-pc-affine-kinjective-reverse-comparison-isIso).

Proof: The affine derived equivalence represents Q(I) by Q(J), where J is obtained
by applying tilde termwise to a complex C of A-modules. K-injectivity of I lifts this
representative isomorphism to a homotopy class J -> I, and fullness of the homotopy
quotient gives a chain map s representing it. The localization/homotopy comparison
shows Q(s) is the chosen isomorphism, so s is a quasi-isomorphism. Every term of J is
quasi-coherent. The affine resolution theorem therefore makes P(s) a quasi-isomorphism.

Construct the ordinary isomorphism res_phi followed by tilde_B -> tilde_A followed
by P from tilde/global-sections unit, pushforward/global-sections comparison and
tilde/global-sections counit. The unit is invertible, and the counit is invertible
on the pushforward of an associated sheaf by the affine localization calculation.
Thus tilde_A followed by P preserves homology, as does tilde_A. The exact-functor
normalization of the reverse comparison identifies its composite with the inverse
homology isomorphism for tilde_A followed by P with P of the inverse homology
isomorphism for tilde_A. Both are invertible, so the reverse comparison at J is too.
Finally its naturality square for s has invertible top, left and bottom arrows:
the top is the comparison at J, and the other two come from s and P(s). Cancellation
proves invertibility of the specified reverse comparison at I. No arbitrary morphism
between the cohomology objects is substituted for that comparison. This works for
unbounded complexes, every integer degree, and zero rings; I need not have injective
terms. -/
theorem affineKInjective_leftExactHomologyComparison_isIso
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    [PreservesFiniteLimits
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)]
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    [I.IsKInjective]
    (hI : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj I)) :
    IsIso ((I.sc i).leftExactHomologyComparison
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)) := by
  let X := Spec (.of A)
  let P := RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let T : ModuleCat.{u} A ⥤ SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
    tilde.functor (.of A)
  let TB : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) := tilde.functor (.of B)
  let : T.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : T.PreservesZeroMorphisms := affineBaseChangeTilde_preservesZero A
  let : TB.PreservesZeroMorphisms := affineBaseChangeTilde_preservesZero B
  let : T.PreservesHomology := tilde_preservesHomology A
  let : TB.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits TB := Functor.preservesFiniteLimits_of_preservesHomology TB
  let : PreservesFiniteColimits TB := Functor.preservesFiniteColimits_of_preservesHomology TB
  let S := moduleSpecΓFunctor (R := .of A)
  let ν : ModuleCat.restrictScalars φ ⟶ T ⋙ P ⋙ moduleSpecΓFunctor (R := .of B) :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (tilde.toTildeΓNatIso (R := .of A)).hom
        (ModuleCat.restrictScalars φ) ≫
      (Functor.associator T S (ModuleCat.restrictScalars φ)).hom ≫
      Functor.whiskerLeft T
        (Scheme.Modules.pushforwardSpecMapCompΓIso (CommRingCat.ofHom φ)).inv
  let σ : ModuleCat.restrictScalars φ ⋙ TB ⟶ T ⋙ P :=
    { app := fun N ↦ TB.map (ν.app N) ≫
        Scheme.Modules.fromTildeΓ (R := .of B) (P.obj (T.obj N))
      naturality := by
        intro N N' a
        dsimp only [Functor.comp_map]
        rw [← Functor.map_comp_assoc, ν.naturality, Functor.map_comp, Category.assoc]
        exact congrArg (fun f ↦ TB.map (ν.app N) ≫ f)
          ((Scheme.Modules.fromTildeΓNatTrans (R := .of B)).naturality (P.map (T.map a))) }
  have : IsIso ν := by dsimp only [ν]; infer_instance
  have : IsIso σ := by
    apply (NatTrans.isIso_iff_isIso_app σ).2
    intro N
    have : (T.obj N).IsQuasicoherent := by
      change (tilde (R := .of A) N).IsQuasicoherent
      infer_instance
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) (T.obj N)) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) _
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of B) (P.obj (T.obj N))) :=
      isIso_fromTildeΓ_pushforward (CommRingCat.ofHom φ) _
    dsimp only [σ]
    infer_instance
  let : PreservesFiniteLimits (T ⋙ P) := preservesFiniteLimits_of_natIso (asIso σ)
  let : PreservesFiniteColimits (T ⋙ P) := preservesFiniteColimits_of_natIso (asIso σ)
  let : (T ⋙ P).PreservesZeroMorphisms := inferInstance
  let : (T ⋙ P).PreservesHomology := inferInstance
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let M : schemeDerivedQCohCategory X := ⟨_, hI⟩
  obtain ⟨E, ⟨e⟩, _, _⟩ := exists_affineQCohDerivedEquivalence_core A
  let C := DerivedCategory.Q.objPreimage (E.inverse.obj M)
  let J := (T.mapHomologicalComplex (.up ℤ)).obj C
  let t : DerivedCategory.Q.obj J ≅ DerivedCategory.Q.obj I :=
    (e.app C).symm ≪≫ (schemeDerivedQCohProperty X).ι.mapIso
      (E.functor.mapIso (DerivedCategory.Q.objObjPreimageIso (E.inverse.obj M)) ≪≫
        E.counitIso.app M)
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  obtain ⟨s', hs'⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj J) I).surjective
    ((DerivedCategory.quotientCompQhIso _).hom.app J ≫ t.hom ≫
      (DerivedCategory.quotientCompQhIso _).inv.app I)
  obtain ⟨s, rfl⟩ := q.map_surjective s'
  have hs : DerivedCategory.Q.map s = t.hom := by
    have hn := (DerivedCategory.quotientCompQhIso _).hom.naturality s
    dsimp only [Functor.comp_map] at hn
    rw [hs'] at hn
    dsimp only [X] at hn
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hn
    exact ((cancel_epi ((DerivedCategory.quotientCompQhIso _).hom.app J)).mp hn).symm
  have : QuasiIso s := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp
    rw [hs]
    infer_instance
  have hJ (n : ℤ) : (J.X n).IsQuasicoherent := by
    change (tilde (R := .of A) (C.X n)).IsQuasicoherent
    infer_instance
  have : QuasiIso ((P.mapHomologicalComplex (.up ℤ)).map s) :=
    affinePushforward_resolution_quasiIso _ J I hJ s
  have hc := (C.sc i).leftExactHomologyComparison_map T P
  have hi' : IsIso (((C.sc i).map T).leftExactHomologyComparison P) := by
    have : IsIso (((C.sc i).mapHomologyIso (T ⋙ P)).inv ≫
        ((C.sc i).map T).leftExactHomologyComparison P) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_left ((C.sc i).mapHomologyIso (T ⋙ P)).inv _
  have hi : IsIso ((J.sc i).leftExactHomologyComparison P) := hi'
  have hn := ShortComplex.leftExactHomologyComparison_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map s) P
  have : IsIso (P.map (HomologicalComplex.homologyMap s i)) := by infer_instance
  have : IsIso (HomologicalComplex.homologyMap
      ((P.mapHomologicalComplex (.up ℤ)).map s) i ≫
        (I.sc i).leftExactHomologyComparison P) := by
    change IsIso (ShortComplex.homologyMap
      (P.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map s)) ≫ _)
    rw [hn]
    change IsIso ((J.sc i).leftExactHomologyComparison P ≫
      P.map (HomologicalComplex.homologyMap s i))
    infer_instance
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap ((P.mapHomologicalComplex (.up ℤ)).map s) i) _
end AlgebraicGeometry
