module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine principal-open localization, retaining the action of the larger base ring.
Source: Stacks Project, Tags 01HR (affine principal-open sections) and 0BLH.
(blueprint: new-sbc-completed-affine-section-localization)

Proof: put B = Γ(E, ⊤), and let b be the image of φ(f) under the structural
map C → B. Naturality of basic opens identifies s⁻¹D(φ(f)) with E.basicOpen b.
Affineness of E identifies its section ring on this open with B[1/b], and
restriction with the localization map. Restrict this localization along
A → C → B: the image of the powers of f is the powers of b. The ring
localization, considered as a module localization, is thus a localization
of the restricted A-module B at f. Compare it with LocalizedModule using
IsLocalizedModule.linearEquiv. This comparison sends m/f^n to the restriction
of m divided by b^n. Multiplication by z in C commutes with restriction and
with division by b^n, so that this comparison has the displayed scalar
compatibility. Every localized element is a fraction, which proves the
identity for all elements. If f = 0 or the open is empty, both localization
and the section ring are zero and the same argument applies. -/
theorem exists_completed_affine_section_localization
    {A C : Type u} [CommRing A] [CommRing C]
    (φ : A →+* C) {E : Scheme.{u}} [IsAffine E] (s : E ⟶ Spec (.of C)) (f : A) :
    let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
    letI : Module C Γ(E, W) := Module.compHom _
      ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
        E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
    let N := ModuleCat.of C Γ(E, W)
    ∃ e : FormalGlueing.localize f (FormalGlueing.restrict φ (completedSectionModule s)) ≃ₗ[A]
        FormalGlueing.restrict φ N,
      ∀ (z : C) x,
        e ((FormalGlueing.localizedSModule φ f (completedSectionModule s)).smul z x) =
          z • (e x : N) := by
  classical
  dsimp only
  let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
  let B := Γ(E, ⊤)
  let χ : C →+* B := ((ΓSpecIso (.of C)).inv ≫ s.appTop).hom
  let ρ : B →+* Γ(E, W) := (E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  let ψ : C →+* Γ(E, W) := ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
    E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  let : Algebra A B := (χ.comp φ).toAlgebra
  let : Algebra B Γ(E, W) := ρ.toAlgebra
  let : Algebra A Γ(E, W) := (ψ.comp φ).toAlgebra
  have hcomp : ρ.comp (χ.comp φ) = ψ.comp φ := rfl
  have : IsScalarTower A B Γ(E, W) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hopen : W = E.basicOpen (χ (φ f)) := by
    change _ = E.basicOpen (s.appTop ((ΓSpecIso (.of C)).inv (φ f)))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  let : IsLocalization.Away (χ (φ f)) Γ(E, W) :=
    (isAffineOpen_top E).isLocalization_of_eq_basicOpen (χ (φ f)) (homOfLE le_top) hopen
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) Γ(E, W) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact inferInstanceAs (IsLocalization.Away (χ (φ f)) Γ(E, W))
  let e₀ : FormalGlueing.restrict φ (completedSectionModule s) ≃ₗ[A] B :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let d := (IsScalarTower.toAlgHom A B Γ(E, W)).toLinearMap.comp e₀.toLinearMap
  have : IsLocalizedModule (Submonoid.powers f) d :=
    IsLocalizedModule.of_linearEquiv_right _ _ e₀
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f)
      (FormalGlueing.restrict φ (completedSectionModule s))) d
  refine ⟨e, ?_⟩
  intro z x
  let M := FormalGlueing.restrict φ (completedSectionModule s)
  let a : M →ₗ[A] M :=
    { toFun := fun m ↦ (show M from χ z * (show B from m))
      map_add' := fun m n ↦ mul_add (χ z) (show B from m) (show B from n)
      map_smul' := fun r m ↦ by
        change χ z * (χ (φ r) * (show B from m)) =
          χ (φ r) * (χ z * (show B from m))
        exact mul_left_comm _ _ _ }
  let b : Γ(E, W) →ₗ[A] Γ(E, W) :=
    { toFun := fun n ↦ ψ z * n
      map_add' := mul_add (ψ z)
      map_smul' := fun r n ↦ by
        change ψ z * ((ψ (φ r)) * n) = ψ (φ r) * (ψ z * n)
        exact mul_left_comm _ _ _ }
  have hh : e.toLinearMap.comp (FormalGlueing.localMap f a) = b.comp e.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers f)
      (LocalizedModule.mkLinearMap _ M) (IsLocalizedModule.map_units d)
    ext m
    simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
    rw [show FormalGlueing.localMap f a (LocalizedModule.mk m 1) =
      LocalizedModule.mk (a m) 1 from IsLocalizedModule.map_LocalizedModules _ a m 1]
    change e (LocalizedModule.mk (a m) 1) = b (e (LocalizedModule.mk m 1))
    rw [show e (LocalizedModule.mk (a m) 1) = d (a m) from
      IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ d (a m)]
    rw [show e (LocalizedModule.mk m 1) = d m from
      IsLocalizedModule.linearEquiv_apply (Submonoid.powers f) _ d m]
    change ρ (χ z * (show B from m)) = ψ z * ρ (show B from m)
    rw [map_mul]
    rfl
  have haction : (FormalGlueing.localizedSModule φ f (completedSectionModule s)).smul z x =
      FormalGlueing.localMap f a x := by
    induction x using LocalizedModule.induction_on with
    | _ m t =>
      rw [(FormalGlueing.exists_localized_s_module φ f (completedSectionModule s)).choose_spec]
      change LocalizedModule.mk (a m) t = FormalGlueing.localMap f a (LocalizedModule.mk m t)
      exact (IsLocalizedModule.map_LocalizedModules _ a m t).symm
  rw [haction]
  exact LinearMap.congr_fun hh x

end AlgebraicGeometry.Scheme.CompletionGluingData
