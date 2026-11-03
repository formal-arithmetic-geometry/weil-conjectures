/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation

/-! # Scalar homology and exact realization for admissible coefficients

Source: blueprint latest, scalar-six-ctf proof (2), Local models.
(blueprint: lem-sfb-admissible-scalar-homology-data).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.MonoidalCategory

attribute [local instance] constantScalarSheaf_laxBraided
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  Mod.extendScalars scalarCoefficientHom finiteConstantScalarExtension
  Functor.mapDerivedCategory Functor.mapDerivedCategoryHomologyFunctorIso

-- An equivalence to ordinary modules detects finite scalar presentations, once
-- coordinates on the finite free objects have been fixed.
private theorem finitePresentation_of_coordinates
    (R : Ab.{u + 1}) [MonObj R]
    (K : Type (u + 1)) [CommRing K]
    (F : Mod Ab.{u + 1} R ⥤ ModuleCat.{u + 1} K) [F.IsEquivalence]
    (b : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≃ₗ[K] (Fin n → K))
    (P : Mod Ab.{u + 1} R) [Module.FinitePresentation K (F.obj P)] :
    Mod.IsFinitelyPresented R P := by
  classical
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' K (F.obj P)
  let a : F.obj (Mod.finiteFree R m) ⟶ F.obj (Mod.finiteFree R n) :=
    ModuleCat.ofHom ((b n).symm.toLinearMap.comp (g.comp (b m).toLinearMap))
  let d := F.preimage a
  let q : F.obj (Mod.finiteFree R n) ⟶ F.obj P :=
    ModuleCat.ofHom (f.comp (b n).toLinearMap)
  have hsurj : Function.Surjective q := hf.comp (b n).surjective
  have hexact : Function.Exact (F.map d).hom q.hom := by
    rw [Functor.map_preimage]
    intro x
    change f (b n x) = 0 ↔ _
    rw [hg]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(b m).symm y, ?_⟩
      change (b n).symm (g (b m ((b m).symm y))) = x
      rw [LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]
    · rintro ⟨y, hy⟩
      refine ⟨b m y, ?_⟩
      change (b n).symm (g (b m y)) = x at hy
      exact (b n).symm_apply_eq.mp hy
  let h := ModuleCat.isColimitCokernelCofork (F.map d) q hexact hsurj
  exact ⟨n, m, d, ⟨F.preimageIso
    (h.coconePointUniqueUpToIso (cokernelIsCokernel (F.map d)) ≪≫
      (PreservesCokernel.iso F d).symm)⟩⟩

private theorem scalarHomology_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [CommRing K] [IsNoetherianRing K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ)
    (hp : ∀ q : ℤ, ∃ n : ℕ,
      Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) (q : ℤ) :
    Mod.IsFinitelyPresented (scalarRingObj Λ) (C.homology q) := by
  classical
  let R := scalarRingObj Λ
  let F := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : F.IsEquivalence := by dsimp only [F]; infer_instance
  have : F.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [F]
    infer_instance
  let r : (Mod.comap φ).obj (Mod.regular R) ≅ Mod.regular (AddCommGrpCat.of K) :=
    (Mod.comapCongr (by simp : inv (inv φ) = φ)).symm.app _ ≪≫
      Mod.regularIsoOfIsIso (inv φ)
  let b₀ : F.obj (Mod.regular R) ≃ₗ[K] K :=
    ((internalToModule K).mapIso r).toLinearEquiv.trans (internalRegularCoordinates K)
  let b (n : ℕ) := ringFreeCoordinates (Mod.regular R) F b₀ n
  obtain ⟨n, ⟨t⟩⟩ := hp q
  have : Module.Finite K (F.obj (Mod.finiteFree R n)) :=
    Module.Finite.of_injective (b n).toLinearMap (b n).injective
  have : Module.Finite K (F.obj (C.X q)) :=
    Module.Finite.of_injective (F.map t.i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite K (F.obj (C.cycles q)) :=
    Module.Finite.of_injective (F.map (C.iCycles q)).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite K (F.obj (C.homology q)) :=
    Module.Finite.of_surjective (F.map (C.homologyπ q)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have : Module.FinitePresentation K (F.obj (C.homology q)) :=
    Module.finitePresentation_of_finite K _
  exact finitePresentation_of_coordinates R K F b (C.homology q)

private theorem continuousHomology_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A]
    (e : Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ)
    (hp : ∀ q : ℤ, ∃ n : ℕ,
      Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) (q : ℤ) :
    Mod.IsFinitelyPresented (scalarRingObj Λ) (C.homology q) := by
  have : IsNoetherianRing (ULift.{u + 1} A) :=
    isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let j := scalarSections.mapMon.mapIso e
  exact scalarHomology_finitelyPresented Λ (ULift.{u + 1} A)
    (continuousScalarHom A ≫ j.inv.hom) C hp q

private theorem admissibleHomology_finitelyPresented
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ)
    (hp : ∀ q : ℤ, ∃ n : ℕ,
      Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) (q : ℤ) :
    Mod.IsFinitelyPresented (scalarRingObj Λ) (C.homology q) := by
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    have : Finite A := hfin
    exact continuousHomology_finitelyPresented Λ A e C hp q
  · obtain ⟨e⟩ := h
    exact continuousHomology_finitelyPresented Λ ℤ_[ell] e C hp q
  · obtain ⟨e⟩ := h
    exact continuousHomology_finitelyPresented Λ ℚ_[ell] e C hp q
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact continuousHomology_finitelyPresented Λ E e C hp q
  · obtain ⟨E, ⟨e⟩⟩ := h
    let := PadicAlgCl.normedFieldOfAlgebra ell E
    let : IsTopologicalRing (PadicAlgCl.integers ell E) :=
      PadicAlgCl.isTopologicalRing_integers ell E
    exact continuousHomology_finitelyPresented Λ (PadicAlgCl.integers ell E) e C hp q
  · obtain ⟨e⟩ := h
    let j := scalarSections.mapMon.mapIso e
    exact scalarHomology_finitelyPresented Λ (ULift.{u + 1} (PadicAlgCl ell))
      (qbarScalarHom ell ≫ j.inv.hom) C hp q

private theorem scalarFieldExtension_leftExact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : Type (u + 1)) [Field K]
    (φ : AddCommGrpCat.of K ⟶ scalarRingObj Λ) [IsMonHom φ] [IsIso φ]
    (X : Scheme.{u}) : PreservesFiniteLimits (finiteConstantScalarExtension Λ X) := by
  let F := Mod.comap φ ⋙ internalToModule K
  have : (Mod.comap φ).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  have : F.IsEquivalence := by dsimp only [F]; infer_instance
  have : F.Additive := by
    have : (internalToModule K).Additive := ⟨by intros; rfl⟩
    dsimp only [F]
    infer_instance
  have : F.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let E := finiteConstantScalarExtension Λ X
  have : E.Additive := scalarExtension_additive Λ X
  let G := F.asEquivalence.inverse ⋙ E
  have : PreservesFiniteLimits G := by
    have hs (S : ShortComplex (ModuleCat.{u + 1} K)) (hS : S.ShortExact) :
        (S.map G).ShortExact := (hS.splittingOfProjective.map G).shortExact
    have hex : PreservesFiniteLimits G ∧ PreservesFiniteColimits G :=
      ((Functor.exact_tfae G).out 0 3).mp hs
    exact hex.1
  let e : E ≅ F ⋙ G :=
    (Functor.leftUnitor E).symm ≪≫
      Functor.isoWhiskerRight F.asEquivalence.unitIso E ≪≫ Functor.associator _ _ _
  exact preservesFiniteLimits_of_natIso e.symm

private theorem finiteCounit_leftExact
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] :
    PreservesFiniteLimits (Mod.extendScalars
      (scalarCounit.{u} (Profinite.continuousMapRingObj A))) := by
  let J := coherentTopology Profinite.{u}
  let C := constantSheaf J Ab.{u + 1}
  let adj := constantSheafAdj J Ab.{u + 1} Profinite.isTerminalPUnit
  let R := Profinite.continuousMapRingObj.{u} A
  let h := continuousScalarHom.{u} A
  let f := C.map h
  let ε := scalarCounit R
  let p := Profinite.constantToContinuousAb.{u} A
  have he : f ≫ ε =
      ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ R).symm p := by
    change (adj.homEquiv _ _).symm h = _
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    dsimp only [adj, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    erw [Equiv.trans_apply, Equiv.apply_symm_apply]
    change h = 𝟙 _ ≫ p.app (Opposite.op (Profinite.of PUnit.{u + 1}))
    rw [Category.id_comp]
    rfl
  have hp : J.W (A := Ab.{u + 1}) p := J.W_of_isLocallyBijective p
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map p) := (J.W_iff p).mp hp
  have : IsIso (f ≫ ε) := by
    rw [he, Adjunction.homEquiv_counit]
    infer_instance
  have : IsIso ε := by
    have he' : ε = inv f ≫ (f ≫ ε) := by simp
    rw [he']
    infer_instance
  have := extension_equivalence ε
  infer_instance

private theorem admissibleScalarExtension_leftExact
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (X : Scheme.{u}) : PreservesFiniteLimits (finiteConstantScalarExtension Λ X) := by
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    have : Finite A := hfin
    exact scalarExtension_leftExact Λ
      (counitExtension_transport Λ _ e (finiteCounit_leftExact A)) X
  · obtain ⟨e⟩ := h
    exact scalarExtension_leftExact Λ
      (counitExtension_transport Λ _ e (counitExtension_leftExact ℤ_[ell])) X
  · obtain ⟨e⟩ := h
    exact scalarExtension_leftExact Λ
      (counitExtension_transport Λ _ e (counitExtension_leftExact ℚ_[ell])) X
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact scalarExtension_leftExact Λ
      (counitExtension_transport Λ _ e (counitExtension_leftExact E)) X
  · obtain ⟨E, ⟨e⟩⟩ := h
    let := PadicAlgCl.normedFieldOfAlgebra ell E
    let : IsTopologicalRing (PadicAlgCl.integers ell E) :=
      PadicAlgCl.isTopologicalRing_integers ell E
    exact scalarExtension_leftExact Λ
      (counitExtension_transport Λ _ e
        (counitExtension_leftExact (PadicAlgCl.integers ell E))) X
  · obtain ⟨e⟩ := h
    let j := scalarSections.mapMon.mapIso e
    exact scalarFieldExtension_leftExact Λ (ULift.{u + 1} (PadicAlgCl ell))
      (qbarScalarHom ell ≫ j.inv.hom) X

/-- Scalar homology of complexes with finite-projective terms is finitely presented,
and scalar realization is left exact, for every admissible condensed coefficient.
No boundedness or finiteness hypothesis on the scheme is needed.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md (2), Local models.
(blueprint: lem-sfb-admissible-scalar-homology-data).

Proof in words:
1. For a continuous coefficient ring, evaluation at the one-point profinite space is
   isomorphic to the scalar ring by constant functions. For the finite-subextension
   algebraic closure it is the algebraic-closure field: every element belongs to
   the finite extension it generates. Transport these ring isomorphisms through
   the admissibility isomorphism. The resulting scalar rings are Noetherian:
   finite rings, discrete valuation rings and fields exhaust the cases.
2. Use the exact equivalence from internal modules in abelian groups to ordinary
   modules over these rings. Finite-free objects retain their usual coordinates.
   A retract of a finite free object is finite. The cycles inject into the finite
   term of the complex, so they are finite over a Noetherian ring; homology is their
   quotient and is finite, hence finitely presented. A finite ordinary presentation
   transports through the equivalence to a cokernel of finite free internal modules.
3. For a finite discrete ring the constant-sheaf counit is invertible. For the
   integral and continuous field cases, the constant-to-continuous extension is
   exact: continuous functions are torsion-free over the discrete valuation ring
   (or field), hence flat. Constant sheafification and inverse image are exact.
   The existing point-extension comparison identifies their composite with scalar
   realization on any scheme. The counit square transports this conclusion through
   the given coefficient isomorphism. For the finite-subextension algebraic closure,
   every short exact scalar sequence splits; any additive realization preserves
   these splittings and is exact. This includes the zero ring and rank zero. -/
theorem admissibleScalarHomologyData
    (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ) :
    (∀ (C : CochainComplex (Mod Ab.{u + 1} (scalarRingObj Λ)) ℤ),
      (∀ q : ℤ, ∃ n : ℕ,
        Nonempty (Retract (C.X q) (Mod.finiteFree (scalarRingObj Λ) n))) →
      ∀ q : ℤ, Mod.IsFinitelyPresented (scalarRingObj Λ) (C.homology q)) ∧
    ∀ X : Scheme.{u}, PreservesFiniteLimits (finiteConstantScalarExtension Λ X) := by
  exact ⟨admissibleHomology_finitelyPresented ell Λ hΛ,
    admissibleScalarExtension_leftExact ell Λ hΛ⟩

end AlgebraicGeometry.ProEtale
