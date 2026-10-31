/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HenselianBoundaryLocalData
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Extension
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FieldGalois
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Basic

/-!
# Finite etale models for inertia invariants at a geometric boundary

Source: Stacks Project, Tags 0BSW and 0BNE.
(blueprint: lem-dl-a1-henselian-inertia-finite-etale-model).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory AlgebraicGeometry
open IsLocalRing
namespace AlgebraicGeometry.Scheme.FiniteEtale

private theorem residue_bijective_of_initial
    (R H : Type u) [CommRing R] [IsLocalRing R] [CommRing H] [HenselianLocalRing H]
    [Algebra R H] [IsLocalHom (algebraMap R H)]
    (hH : ∀ (T : Type u) [CommRing T] [HenselianLocalRing T]
      (g : R →+* T), IsLocalHom g →
      ∃! h : H →+* T, IsLocalHom h ∧ h.comp (algebraMap R H) = g) :
    Function.Bijective (ResidueField.map (algebraMap R H)) := by
  obtain ⟨f, ⟨hf, hcomp⟩, _⟩ := hH (ResidueField R) (IsLocalRing.residue R) inferInstance
  have : IsLocalHom f := hf
  let g := ResidueField.lift f
  let a := ResidueField.map (algebraMap R H)
  have hga (x : ResidueField R) : g (a x) = x := by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
    change f (algebraMap R H r) = IsLocalRing.residue R r
    exact DFunLike.congr_fun hcomp r
  refine ⟨a.injective, fun y ↦ ⟨g y, ?_⟩⟩
  apply g.injective
  exact hga (g y)

private theorem henselization_residue_algClosed
    (A H : Type u) [CommRing A] [IsLocalRing A]
    [IsAlgClosed (ResidueField A)] [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (maximalIdeal A)) H]
    (hH : Algebra.IsHenselizationAtPrime' A (maximalIdeal A) H) :
    IsAlgClosed (ResidueField H) := by
  let R := Localization.AtPrime (maximalIdeal A)
  have hu : (maximalIdeal A).primeCompl ≤ IsUnit.submonoid A := by
    intro x hx
    exact not_not.mp hx
  let e : A ≃+* R := (IsLocalization.atUnits A (maximalIdeal A).primeCompl hu).toRingEquiv
  have : IsAlgClosed (ResidueField R) :=
    IsAlgClosed.of_ringEquiv (ResidueField A) _ (ResidueField.mapEquiv e)
  have : IsLocalHom (algebraMap R H) := hH.1
  exact IsAlgClosed.of_ringEquiv (ResidueField R) _
    (RingEquiv.ofBijective _ (residue_bijective_of_initial R H hH.2))

private theorem residueAction_ker_eq_top
    {U C : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (b : AlgebraicGeometry.Spec (.of Ω) ⟶ U) (x : C)
    [IsAlgClosed (C.residueField x)]
    (B : AlgebraicGeometry.Scheme.FiniteEtale.HenselianBoundaryLocalData j b x) :
    B.residueAction.ker = ⊤ := by
  have : IsAlgClosed (ResidueField (C.presheaf.stalk x)) :=
    ‹IsAlgClosed (C.residueField x)›
  have : IsAlgClosed (ResidueField B.H) :=
    henselization_residue_algClosed (C.presheaf.stalk x) B.H B.isHenselization
  ext σ
  simp only [Subgroup.mem_top, iff_true, MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro z
  obtain ⟨r, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ResidueField B.H) (K := ResidueField (integralClosure B.H B.Ω))).2 z
  simp only [AlgEquiv.commutes]


open scoped FintypeCatDiscrete in
private theorem exists_pullback_iso_of_trivial_smul
    {U V : Scheme.{u}} [ConnectedSpace U] [ConnectedSpace V] (f : U ⟶ V)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)
    (GU GV : ProfiniteGrp.{u})
    [∀ P, MulAction GU ((fiber s).obj P)] [IsFundamentalGroup (fiber s) GU]
    [∀ Q, MulAction GV ((fiber (s ≫ f)).obj Q)]
    [IsFundamentalGroup (fiber (s ≫ f)) GV]
    (Z : U.FiniteEtale) (hZ : ∀ g : GU, ∀ x : (fiber s).obj Z, g • x = x) :
    ∃ Q : V.FiniteEtale, Nonempty ((pullback f).obj Q ≅ Z) := by
  let τ := pullbackFiberIso f s
  let ρ := fundamentalGroupMap τ GU GV
  let X := (fiber s).obj Z
  let act : MulAction GV X :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : ContinuousSMul GV X := ⟨continuous_snd⟩
  let Xc : ContAction FintypeCat.{u} GV :=
    ⟨Action.FintypeCat.ofMulAction GV X, by
      rw [Action.isContinuous_def]
      exact continuous_snd⟩
  let EV := equivalenceContAction (s ≫ f) GV
  let Q := EV.inverse.obj Xc
  let c := EV.counitIso.app Xc
  let φ : (fiber s).obj ((pullback f).obj Q) → X :=
    fun y ↦ c.hom.hom.hom (τ.hom.app Q y)
  have hφ : Function.Bijective φ :=
    (FintypeCat.equivEquivIso.symm
      ((ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso c)).bijective.comp
      (FintypeCat.equivEquivIso.symm (τ.app Q)).bijective
  have heq (g : GU) (y : (fiber s).obj ((pullback f).obj Q)) :
      φ (g • y) = g • φ y := by
    have hc := congrArg (fun k ↦ k.hom (τ.hom.app Q y)) (c.hom.hom.comm (ρ g))
    simp only [φ, ← fundamentalGroupMap_smul τ GU GV]
    exact hc.trans (hZ g _).symm
  let EU := equivalenceContAction s GU
  let I : EU.functor.obj ((pullback f).obj Q) ≅ EU.functor.obj Z :=
    ObjectProperty.isoMk _ (Action.mkIso
      (FintypeCat.equivEquivIso (Equiv.ofBijective φ hφ))
      fun g ↦ FintypeCat.hom_ext _ _ fun y ↦ heq g y)
  exact ⟨Q, ⟨EU.fullyFaithfulFunctor.preimageIso I⟩⟩

private theorem trivial_smul_of_galois_fixed
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (G : ProfiniteGrp.{u})
    [∀ P, MulAction G ((fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj P)]
    [IsFundamentalGroup (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))) G]
    (P : (Spec (.of K)).FiniteEtale)
    (hfixed : ∀ σ : Gal(Ω/K),
      ∀ z : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj P,
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left = z.left) :
    ∀ g : G, ∀ z : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj P,
      g • z = z := by
  obtain ⟨r, e, _, he, _⟩ :=
    field_fundamental_galois K Ω (separableClosure K Ω) G
  intro g z
  obtain ⟨σ, hσ⟩ := (e.surjective.comp r.surjective) g
  change e (r σ) = g at hσ
  rw [← hσ, he]
  have h := galoisToFundamentalGroup_smul (𝟙 (Spec (.of K))) (Iso.refl _) G σ P z
  change galoisToFundamentalGroup (𝟙 (Spec (.of K))) (Iso.refl _) G σ • z =
    (galoisToAut (𝟙 (Spec (.of K))) σ).hom.app P z at h
  rw [h]
  apply fiber_ext
  rw [galoisToAut_hom_app_left]
  exact hfixed σ z


private theorem exists_model_of_galois_fixed
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {V : Scheme.{u}} [ConnectedSpace V] (f : Spec (.of K) ⟶ V)
    (P : (Spec (.of K)).FiniteEtale)
    (hfixed : ∀ σ : Gal(Ω/K),
      ∀ z : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj P,
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left = z.left) :
    ∃ Q : V.FiniteEtale, Nonempty ((pullback f).obj Q ≅ P) := by
  let s := pointOfAlgebra Ω (𝟙 (Spec (.of K)))
  obtain ⟨GU, hGUact, hGU⟩ := exists_isFundamentalGroup s
  let := hGUact
  let := hGU
  obtain ⟨GV, hGVact, hGV⟩ := exists_isFundamentalGroup (s ≫ f)
  let := hGVact
  let := hGV
  exact exists_pullback_iso_of_trivial_smul f s GU GV P
    (trivial_smul_of_galois_fixed K Ω GU P hfixed)

/-- At a boundary point with algebraically closed residue field, a generic finite
etale cover fixed by residue inertia has a finite etale henselian model.

Source: Stacks Project, Tags 0BSW and 0BNE.
(blueprint: lem-dl-a1-henselian-inertia-finite-etale-model).

Proof: The initial henselian local algebra has the same residue field as the stalk:
its initial map to that field induces an inverse to the residue inclusion. The
residue closure is therefore also this algebraically closed field. Every residue
automorphism is the identity, so the recorded inertia kernel is the entire local
Galois group. The field fundamental-group comparison turns the hypothesis into a
trivial action on the finite geometric fibre. Regard that same finite set as a
trivial continuous action of the henselian scheme's fundamental group. Its finite
etale cover, under the Galois-category equivalence, pulls back to the given cover:
the counit gives a bijective equivariant fibre map, which the equivalence lifts to
an isomorphism. Empty and disconnected finite sets are included.
-/
theorem henselian_model_of_inertia_fixed
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (x : C) [IsAlgClosed (C.residueField x)]
    (B : HenselianBoundaryLocalData j b x)
    (P : (Spec (.of B.K)).FiniteEtale)
    (hfixed : ∀ σ ∈ B.residueAction.ker,
      ∀ z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap B.K B.Ω)))).obj P,
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left = z.left) :
    ∃ Q : (Spec (.of B.H)).FiniteEtale,
      Nonempty ((Scheme.FiniteEtale.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K)))).obj Q ≅
          P) := by
  have hker := residueAction_ker_eq_top j b x B
  apply exists_model_of_galois_fixed B.K B.Ω
    (Spec.map (CommRingCat.ofHom (algebraMap B.H B.K))) P
  intro σ z
  have hz := hfixed σ (by rw [hker]; trivial)
  simpa only [pointOfAlgebra, Category.comp_id] using hz z

end AlgebraicGeometry.Scheme.FiniteEtale
