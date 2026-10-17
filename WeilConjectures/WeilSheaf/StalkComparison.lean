/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPointsCount
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubobjectStalk
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Tools for comparing stalks of Weil sheaves along morphisms of geometric fibers

This file collects three general facts used to compare the stalks of a Weil sheaf with those of
its pullback along a morphism `j : Ȳ ⟶ X̄` of geometric fibers intertwining Frobenius
structures, where the two geometric fibers may live over different algebraic closures.

- `AlgebraicGeometry.ProEtale.globalSectionsTransport_comm_of_upperStar_of_comp`: transports of
  global sections along structure maps commute with the transport along a morphism `θ : j^* M ⟶ N`
  compatible with them, the squares being taken over different bases `P'` and `P`.
- `FrobeniusModule.hasEigenvalue_of_iSup_range_eq_top`: an eigenvalue of the Frobenius of a
  Frobenius module spanned by the images of equivariant maps is an eigenvalue of one of the
  sources; hence such a module is pure if the sources are
  (`FrobeniusModule.IsPureOfWeight.of_iSup_range_eq_top`).
- `AlgebraicGeometry.Scheme.Hom.mem_finitePoints_of_comp_geometricGaloisFrobenius_pow`: a
  geometric point fixed by `Frᵐ` up to `σᵐ`, `m ≥ 1`, lies over a point with finite residue field
  whose degree divides `m`.
-/

@[expose] public section

universe u' u v w

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Transports of global sections along structure maps `ψ_M : g_Y^* M ⟶ M` and
`ψ_N : g_X^* N ⟶ N` commute with the transports along a morphism `θ : j^* M ⟶ N` compatible
with them, for `g_X ≫ j = j ≫ g_Y`. The squares for `ψ_M` live over `P`, those for `ψ_N` over
`P'`, and the transports along `θ` over a morphism `Θ : P' ⟶ P` commuting with the
reparametrisations. -/
lemma globalSectionsTransport_comm_of_upperStar_of_comp {X Y P P' : Scheme.{u}} (j : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) (hc : gX ≫ j = j ≫ gY) {M : Sheaf (Scheme.ProEt.topology Y) A}
    {N : Sheaf (Scheme.ProEt.topology X) A} (ψM : (gY)^*[A].obj M ⟶ M)
    (ψN : (gX)^*[A].obj N ⟶ N) (θ : (j)^*[A].obj M ⟶ N)
    (hθ : (upperStarComp A gX j).hom.app M ≫ (gX)^*[A].map θ ≫ ψN =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A j gY).hom.app M ≫ (j)^*[A].map ψM ≫ θ)
    {Θ : P' ⟶ P} {t₁ t₂ : P ⟶ Y} {t₁' t₂' : P' ⟶ X} {τ : P ⟶ P} {τ' : P' ⟶ P'}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j) (hY : τ ≫ t₁ = t₂ ≫ gY)
    (hX : τ' ≫ t₁' = t₂' ≫ gX) (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    globalSectionsTransport A hY ψM ≫ globalSectionsTransport A h₂ θ =
      globalSectionsTransport A h₁ θ ≫ globalSectionsTransport A hX ψN := by
  have h₃ : (τ' ≫ Θ) ≫ t₁ = t₂' ≫ (gX ≫ j) := by
    rw [Category.assoc, h₁, ← Category.assoc, hX, Category.assoc]
  have h₄ : (Θ ≫ τ) ≫ t₁ = t₂' ≫ (j ≫ gY) := by
    rw [Category.assoc, hY, ← Category.assoc, h₂, Category.assoc]
  rw [globalSectionsTransport_comp A hY h₂ h₄, globalSectionsTransport_comp A h₁ hX h₃,
    globalSectionsTransport_congr A h₃ hc _ _ hθ, globalSectionsTransport_congr_left A _ hΘ]

/-- The transport of global sections along a square `τ ≫ t = t' ≫ g` and the identity of
`g^* M` is natural in the sheaf `M`. -/
lemma globalSectionsTransport_id_naturality {P P' Y Y' : Scheme.{u}} {τ : P' ⟶ P} {t : P ⟶ Y}
    {t' : P' ⟶ Y'} {g : Y' ⟶ Y} (h : τ ≫ t = t' ≫ g) {M M' : Sheaf (Scheme.ProEt.topology Y) A}
    (u : M ⟶ M') :
    globalSectionsTransport A h (𝟙 ((g)^*[A].obj M)) ≫
        (Sheaf.Γ _ A).map ((t')^*[A].map ((g)^*[A].map u)) =
      (Sheaf.Γ _ A).map ((t)^*[A].map u) ≫ globalSectionsTransport A h (𝟙 ((g)^*[A].obj M')) := by
  have n₁ := (upperStarCompIso A h).hom.naturality u
  have n₂ := (globalSectionsToUpperStar A τ).naturality ((t)^*[A].map u)
  simp only [Functor.comp_map] at n₁ n₂
  simp only [globalSectionsTransport, CategoryTheory.Functor.map_id]
  erw [Category.comp_id, Category.comp_id]
  rw [Category.assoc, ← Functor.map_comp, ← n₁, Functor.map_comp,
    reassoc_of% n₂]

/-- The transport of global sections along a square `e ≫ t = t' ≫ g` with `e` an isomorphism and
an isomorphism `ψ` is an isomorphism. -/
lemma isIso_globalSectionsTransport {P P' Y Y' : Scheme.{u}} (e : P' ≅ P) {t : P ⟶ Y}
    {t' : P' ⟶ Y'} {g : Y' ⟶ Y} (h : e.hom ≫ t = t' ≫ g) {M : Sheaf (Scheme.ProEt.topology Y) A}
    {M' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (g)^*[A].obj M ⟶ M') [IsIso ψ] :
    IsIso (globalSectionsTransport A h ψ) := by
  rw [globalSectionsTransport_eq_of_iso A e h ψ]
  infer_instance

/-- If finitely many subsheaves `Q i` span an `ℓ`-adic sheaf `B` on `Y`, then for `j : Y' ⟶ Y`
and a geometric point `t` of `Y'`, the images of the stalks at `t` of the pullbacks `j^* Q i`
span the stalk of `j^* B`: the stalk of `j^*` at `t` is the stalk at `t ≫ j`. -/
lemma iSup_range_adicStalkMap_adicUpperStar_eq_top {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}}
    (j : Y' ⟶ Y) {Ω : Type u} [Field Ω] (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y')
    {B : AdicSheaf l Y} {M : ℕ} (Q : Fin M → Subobject B)
    (hQ : (Finset.univ : Finset (Fin M)).sup Q = ⊤) :
    ⨆ i, LinearMap.range (adicStalkMap t ((j)^*ᵃ[l].map (Q i).arrow)) = ⊤ := by
  let e (A : AdicSheaf l Y) := WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    ((upperStarComp (WeilCoefficients.{u} l) t j).app A.X))
  have hc {A A' : AdicSheaf l Y} (u : A ⟶ A') :
      (e A').toLinearMap ∘ₗ adicStalkMap (t ≫ j) u =
        adicStalkMap t ((j)^*ᵃ[l].map u) ∘ₗ (e A).toLinearMap := by
    have n := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map f)).hom)
      ((upperStarComp (WeilCoefficients.{u} l) t j).hom.naturality u.hom)
    simp only [Functor.map_comp, ModuleCat.hom_comp] at n
    exact n
  have key (i : Fin M) : LinearMap.range (adicStalkMap t ((j)^*ᵃ[l].map (Q i).arrow)) =
      (adicStalkSubspace (t ≫ j) (Q i)).map (e B).toLinearMap := by
    rw [adicStalkSubspace, ← LinearMap.range_comp, hc,
      LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  have htop : ⨆ i, adicStalkSubspace (t ≫ j) (Q i) = ⊤ := by
    rw [← adicStalkSubspace_top (t ≫ j) B, ← hQ, adicStalkSubspace_finset_sup]
    simp
  simp_rw [key, ← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]

end AlgebraicGeometry.ProEtale

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- If a Frobenius module `N` is spanned by the images of Frobenius-equivariant linear maps
`g i : M i ⟶ N`, every eigenvalue `α` of the Frobenius of `N` is an eigenvalue of the Frobenius
of some `M i`: otherwise `F - α` is bijective on every `M i`, so its image on `N` contains every
image of `g i`, hence is all of `N`, and `F - α` is injective on `N`. -/
theorem hasEigenvalue_of_iSup_range_eq_top {ι : Type*} {M : ι → FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{w, v} K} (g : ∀ i, (M i).carrier →ₗ[K] N.carrier)
    (hg : ∀ i x, g i ((M i).frobenius x) = N.frobenius (g i x))
    (hsup : ⨆ i, LinearMap.range (g i) = ⊤) {α : K} (hα : N.frobeniusEnd.HasEigenvalue α) :
    ∃ i, (M i).frobeniusEnd.HasEigenvalue α := by
  by_contra hM
  push Not at hM
  let T : Module.End K N.carrier := N.frobeniusEnd - α • LinearMap.id
  have hTi (i : ι) (z : (M i).carrier) :
      g i ((M i).frobeniusEnd z - α • z) = T (g i z) := by
    simp [T, frobeniusEnd, hg]
  have hsurj (i : ι) : Function.Surjective
      ((M i).frobeniusEnd - α • (LinearMap.id : Module.End K (M i).carrier)) := by
    refine LinearMap.injective_iff_surjective.mp fun a b hab ↦ ?_
    by_contra hne
    refine hM i (Module.End.hasEigenvalue_of_hasEigenvector (x := a - b) ?_)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, sub_ne_zero.2 hne⟩
    have h := sub_eq_zero.2 hab
    rw [← map_sub] at h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
    exact sub_eq_zero.1 h
  have hrange : LinearMap.range T = ⊤ := by
    refine eq_top_iff.2 (hsup ▸ iSup_le fun i ↦ ?_)
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj i x
    exact ⟨g i z, (hTi i z).symm.trans (by simp)⟩
  have hTinj : Function.Injective T :=
    LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.1 hrange)
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  refine hy.2 (hTinj ?_)
  simp [T, hy.1]

/-- A Frobenius module spanned by the images of Frobenius-equivariant linear maps from modules
pure of weight `w` is pure of weight `w`. -/
theorem IsPureOfWeight.of_iSup_range_eq_top {ι : Type*} {M : ι → FrobeniusModule.{u, v} K}
    {N : FrobeniusModule.{w, v} K} (g : ∀ i, (M i).carrier →ₗ[K] N.carrier)
    (hg : ∀ i x, g i ((M i).frobenius x) = N.frobenius (g i x))
    (hsup : ⨆ i, LinearMap.range (g i) = ⊤) {ι' : K →+* ℂ} {q : ℕ} {w' : ℝ}
    (h : ∀ i, (M i).IsPureOfWeight ι' q w') : N.IsPureOfWeight ι' q w' := fun α hα ↦ by
  obtain ⟨i, hi⟩ := hasEigenvalue_of_iSup_range_eq_top g hg hsup hα
  exact h i α hi

/-- A Frobenius module isomorphic to an `ι`-real one is `ι`-real. -/
theorem IsReal.of_equiv {ι' : K →+* ℂ} {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N)
    (h : N.IsReal ι') : M.IsReal ι' :=
  h.of_charpoly_eq_pow 1 (by rw [pow_one, e.charpoly_frobeniusEnd])

end FrobeniusModule

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A geometric point `s` of the geometric fiber with `s ≫ Frᵐ = σᵐ ≫ s`, `m ≥ 1`, lies over a
point `x` with finite residue field whose degree divides `m`: the embedding `κ(x) ↪ k̄` given by
`s` takes values in the elements fixed by the `m`-th power of the Frobenius. -/
theorem mem_finitePoints_of_comp_geometricGaloisFrobenius_pow {m : ℕ} (hm : m ≠ 0)
    {s : Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber}
    (hs : s ≫ (f.geometricGaloisFrobenius ^ m).hom = (specGeometricFrobenius k ^ m).hom ≫ s) :
    (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _) ∈ X.finitePoints ∧
      f.degreeOver ((s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint _)) ∣ m := by
  let := Fintype.ofFinite k
  set g := s ≫ f.geometricFiberProj
  let σm := (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)
  let ψ : AlgebraicClosure k →+* AlgebraicClosure k := σm.symm.toRingEquiv.toRingHom
  have hσ : σm.symm = FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m := by
    rw [← AlgEquiv.aut_inv]
    simp [σm, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow]
  have hψ (a : AlgebraicClosure k) : ψ a = a ^ (Nat.card k ^ m) := by
    change σm.symm a = _
    rw [hσ, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hfix : (specGeometricFrobenius k ^ m).hom ≫ g = g := by
    rw [← Category.assoc, ← hs, Category.assoc,
      geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  have hψfix : Spec.map (CommRingCat.ofHom ψ) ≫ g = g := by
    have hc : CommRingCat.ofHom σm.toRingEquiv.toRingHom ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      ext a
      exact σm.symm_apply_apply a
    conv_lhs => rw [← hfix]
    rw [specGeometricFrobenius_pow_hom, ← Category.assoc, ← Spec.map_comp, hc, Spec.map_id,
      Category.id_comp]
  let α := Spec.preimage (s ≫ f.geometricFiberToAlgebraicClosure)
  let : Algebra k (AlgebraicClosure k) :=
    (α.hom.comp (algebraMap k (AlgebraicClosure k))).toAlgebra
  have hmem : g ∈ f.fixedFieldPoints ψ := by
    refine ⟨?_, hψfix⟩
    have h := s ≫= f.geometricFiber_condition
    rw [← Category.assoc, ← Category.assoc,
      ← Spec.map_preimage (s ≫ f.geometricFiberToAlgebraicClosure)] at h
    refine h.trans ?_
    simp only [Scheme.specAlgebraicClosure, Over.mk_hom, ← Spec.map_comp]
    rfl
  have key := f.mem_finitePoints_of_mem_fixedFieldPoints hm ψ hψ hmem
  have hd : g.base default = g.base (IsLocalRing.closedPoint _) :=
    congrArg g.base (Subsingleton.elim _ _)
  rw [hd] at key
  exact key

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The linear map underlying a composite of morphisms of `ℚ̄_ℓ`-modules. -/
lemma _root_.AlgebraicGeometry.WeilCoefficients.toModuleCat_map_comp_hom
    {M N P : WeilCoefficients.{u} l} (f : M ⟶ N) (g : N ⟶ P) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom =
      ((WeilCoefficients.toModuleCat l).map g).hom ∘ₗ
        ((WeilCoefficients.toModuleCat l).map f).hom := by
  rw [Functor.map_comp]
  rfl

/-- An `ι`-real Weil sheaf is `ι`-real at every geometric point `s` with `s ≫ Frᵐ = σᵐ ≫ s`,
`m ≥ 1`: the point under `s` is a closed point `x` of degree dividing `m`, and the Frobenius of
`F_s` relative to `𝔽_{qᵐ}` has the characteristic polynomial of a power of `Fₓ`. -/
theorem IsReal.stalkAt {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} (h : F.IsReal ι)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {m : ℕ} (hm : m ≠ 0)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).IsReal ι := by
  obtain ⟨hx, hdvd⟩ := Scheme.Hom.mem_finitePoints_of_comp_geometricGaloisFrobenius_pow _ hm hs
  have hx₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (X ↘ Spec (CommRingCat.of k₀)) ⟨_, hx⟩
  exact (h ⟨_, hx⟩).of_charpoly_eq_pow _ (F.charpoly_frobeniusEnd_stalkAt_of_dvd _ s hx₁
    (hx₁ ▸ hx) hdvd (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      _ ⟨_, hx⟩) hs)

end AlgebraicGeometry.WeilSheaf
