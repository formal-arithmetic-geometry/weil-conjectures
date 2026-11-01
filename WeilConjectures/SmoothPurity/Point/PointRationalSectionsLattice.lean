/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.AdicCompletion.Topology
public import WeilConjectures.Algebra.Homology.Derived.DerivedCompleteModuleFinite
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexCohomologySplitting
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
public import WeilConjectures.RingTheory.FiniteModuleComplete

/-! # Finite free integral lattices for the point sections functor

Source: step 10 of the point-fibre argument, the bounded zero-differential lattice.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private noncomputable def lattice_homologyIso {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hd : ∀ i j, P.d i j = 0) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (DerivedCategory.Q.obj P) ≅ P.X i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app P ≪≫
    (P.isoHomologyπ (i - 1) i (by simp) (hd _ _)).symm ≪≫
    P.iCyclesIso i (i + 1) (by simp) (hd _ _)

private noncomputable def lattice_tensorPiIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (Fin n → R)) ≅
      ModuleCat.of S (Fin n → S) := by
  letI : Algebra R S := f.toAlgebra
  exact ((TensorProduct.piRight R S S (fun _ : Fin n ↦ R)).trans
    (LinearEquiv.piCongrRight fun _ ↦ TensorProduct.AlgebraTensorModule.rid R S S)).toModuleIso

/-- Every bounded finite-dimensional field complex is the rational fibre of an
integral constructible complex.
Source: blueprint finite-coefficient-point, the rational essential-surjectivity
argument in step 10; vector-space basis and cohomology decomposition.
(blueprint: lem-weil-point-rational-sections-lattice).

Proof: choose finite bases of the finitely many nonzero cohomology spaces of V.
Lift their vectors to cycles in a representative complex. This gives a
quasi-isomorphism from the bounded zero-differential complex with E^d_i in degree i
to that representative. The identical ranks define a bounded finite free O_E
complex P. Since O_E is complete, P is derived complete. It therefore belongs to
pointFgComplete; use the inverse of the integral equivalence to obtain K with
integral section complex isomorphic to P. The integral-to-field tensor carries
P to the displayed E-complex. The canonical size-descent counit identifies that
scalar extension with pointIntegralRationalFibre(K), giving the required isomorphism.
For V = 0 use the empty complex. This constructs objects only and makes no claim
about rational Hom groups. -/
theorem pointRationalSectionsLattice
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (hi : (pointIntegralFibre D l hl E).IsEquivalence)
    (V : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ∃ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      Nonempty ((pointIntegralRationalFibre D l hl E).obj K ≅ V) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let R := ULift.{u + 1, u} O
  let S := ULift.{u + 1, u} E
  let J : Ideal O := Ideal.span {Padic.coefficientExtensionUniformizer l E}
  let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  let : IsNoetherianRing R := isNoetherianRing_of_ringEquiv O ULift.ringEquiv.symm
  let : IsAdicComplete J O := AdicCompletion.of_bijective_iff.mp
    (((Padic.finite_module_adic_complete_and_hom.{u, u, u} l E).1 O).2.1)
  have hR : IsAdicComplete I R := by
    have ht := (IsAdicComplete.congr_ringEquiv J
      (ULift.ringEquiv.symm : O ≃+* R)).mpr (inferInstance : IsAdicComplete J O)
    dsimp only [J] at ht
    rw [Ideal.map_span, Set.image_singleton] at ht
    convert! ht using 1
  let W := (pointFibreSizeLift E).obj V
  obtain ⟨H, a, b, hd, hH, hge, hle, hfd, ⟨eH⟩⟩ :=
    ((DerivedCategory.field_complex_cohomology_splitting S).2.2.2.1 W.obj W.property).1
  let n (i : ℤ) := Module.finrank S (H.X i)
  let P : CochainComplex (ModuleCat.{u + 1} R) ℤ :=
    { X := fun i ↦ ModuleCat.of R (Fin (n i) → R), d := fun _ _ ↦ 0 }
  let eP (i : ℤ) := lattice_homologyIso P (fun _ _ ↦ rfl) i
  have hfinite (i : ℤ) : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
        (DerivedCategory.Q.obj P)) :=
    (Module.Finite.equiv_iff (eP i).toLinearEquiv).mpr inferInstance
  have hP : DerivedCategory.pointFgComplete R I (DerivedCategory.Q.obj P) := by
    obtain ⟨s, hs⟩ := W.property.1
    refine ⟨⟨s, ?_⟩, hfinite,
      lattice_complete_of_homology.{u + 1, u + 1, u + 1} I
        (DerivedCategory.Q.obj P) (fun i ↦ ?_)⟩
    · intro i hi
      have hz : IsZero (H.X i) := (hs i hi).of_iso (hH i).some
      let := ModuleCat.subsingleton_of_isZero hz
      have hn : n i = 0 := Module.finrank_zero_of_subsingleton
      have : IsEmpty (Fin (n i)) := hn ▸ inferInstanceAs (IsEmpty (Fin 0))
      exact (ModuleCat.isZero_of_subsingleton (P.X i)).of_iso (eP i)
    · let := hfinite i
      exact finite_module_complete_over_complete_noetherian R I _
  let T := ModuleCat.extendScalars (pointIntegralToField l E)
  have hterms (i : ℤ) : Nonempty (T.obj (P.X i) ≅ H.X i) := by
    let := hfd i
    exact ⟨lattice_tensorPiIso (pointIntegralToField l E) (n i) ≪≫
      (Module.finBasis S (H.X i)).equivFun.symm.toModuleIso⟩
  let ePH : (T.mapHomologicalComplex (.up ℤ)).obj P ≅ H :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ (hterms i).some) (by
      intro i j hij
      change (hterms i).some.hom ≫ H.d i j = T.map 0 ≫ (hterms j).some.hom
      rw [hd, T.map_zero, comp_zero, zero_comp])
  let A : (DerivedCategory.pointFgComplete R I).FullSubcategory :=
    ⟨DerivedCategory.Q.obj P, hP⟩
  let K := (pointIntegralFibre D l hl E).objPreimage A
  let eK : ((pointIntegralFibre D l hl E).obj K).obj ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.pointFgComplete R I).ι.mapIso
      ((pointIntegralFibre D l hl E).objObjPreimageIso A)
  let eRat : (pointFibreRationalAmbient D l E).obj K.obj ≅ W.obj :=
    T.mapDerivedCategory.mapIso eK ≪≫ T.mapDerivedCategoryFactors.app P ≪≫
      DerivedCategory.Q.mapIso ePH ≪≫ eH.symm
  have : (pointFibreSizeLift E).IsEquivalence := pointFibreSizeLift_equivalence E
  refine ⟨K, ⟨?_⟩⟩
  exact (pointFibreSizeDescent E).mapIso (ObjectProperty.isoMk _ eRat) ≪≫
    (pointFibreSizeLift E).asEquivalence.unitIso.symm.app V

end WeilConjectures
