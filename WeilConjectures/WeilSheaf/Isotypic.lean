/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SplitTorsor
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Isotypic components of pushforwards along split torsors of Weil sheaves

Let `π : W ⟶ Z` be an étale morphism of `k₀`-schemes and `τ_g`, `g ∈ G`, automorphisms of `W`
over `Z` and over `k₀`, forming a torsor under the finite abelian group `G` which is split by
the `τ_g` (`AlgebraicGeometry.ProEtale.IsTorsorSplit`). The group acts on the pushforward
`P = π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf by morphisms of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.torsorTranslation`), and for a character `χ` of `G` the
endomorphism `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` (`AlgebraicGeometry.ProEtaleWeilSheaf.torsorIdempotent`)
projects onto the `χ`-isotypic component.

The main result (`AlgebraicGeometry.ProEtaleWeilSheaf.exists_retraction_of_isotypic`) is the
Weil version of `AlgebraicGeometry.Etale.isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent`:
a morphism of pro-étale Weil sheaves `φ : M ⟶ P` on which `G` acts through `χ` and whose adjoint
`π^* M ⟶ ℚ̄_ℓ` is an isomorphism identifies `M` with the image of `e_χ`: there is a morphism of
pro-étale Weil sheaves `r : P ⟶ M` with `φ ≫ r = 𝟙` and `r ≫ φ = e_χ`. After pullback along the
cover `π` this is checked on the evaluations along the sections of the torsor, which are jointly
injective (`AlgebraicGeometry.ProEtale.torsorEval_hom_ext`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- Let `ev_i : F P ⟶ U` be a jointly monomorphic family, `φ : M ⟶ P` such that
`F φ ≫ ev_i = θ ≫ s_i` for an isomorphism `θ`, and `e : P ⟶ P` such that `F e ≫ ev_i = a ≫ s_i`
for some `a`. Then `F e` factors through `F φ`. -/
lemma Functor.map_eq_comp_of_jointlyMono {ι : Type*} {P M : C} {U : D}
    (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P) (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    F.map e = a ≫ CategoryTheory.inv θ ≫ F.map φ :=
  hev _ _ fun i ↦ by
    rw [he, Category.assoc, Category.assoc, hφ i, IsIso.inv_hom_id_assoc]

/-- In the situation of `CategoryTheory.Functor.map_eq_comp_of_jointlyMono`, with `C` abelian,
`F` faithful and additive and `s_{i₀} = 𝟙`, the morphism `φ` is a monomorphism and `e` factors
through it. -/
lemma Functor.mono_and_comp_cokernel_eq_zero_of_jointlyMono [Abelian C] [Preadditive D]
    [F.Additive] [F.Faithful] {ι : Type*} {P M : C} {U : D} (ev : ι → (F.obj P ⟶ U))
    (hev : ∀ {T : D} (a b : T ⟶ F.obj P), (∀ i, a ≫ ev i = b ≫ ev i) → a = b)
    (s : ι → (U ⟶ U)) (i₀ : ι) (hs : s i₀ = 𝟙 U) (e : P ⟶ P) (a : F.obj P ⟶ U) (φ : M ⟶ P)
    (θ : F.obj M ⟶ U) [IsIso θ]
    (he : ∀ i, F.map e ≫ ev i = a ≫ s i) (hφ : ∀ i, F.map φ ≫ ev i = θ ≫ s i) :
    Mono φ ∧ e ≫ cokernel.π φ = 0 := by
  have h := F.map_eq_comp_of_jointlyMono ev hev s e a φ θ he hφ
  refine ⟨?_, F.map_injective ?_⟩
  · have : Mono (F.map φ) := by
      have hsplit : F.map φ ≫ ev i₀ ≫ CategoryTheory.inv θ = 𝟙 _ := by
        rw [← Category.assoc, hφ, hs, Category.comp_id, IsIso.hom_inv_id]
      exact (IsSplitMono.mk' ⟨_, hsplit⟩).mono
    exact F.mono_of_mono_map this
  · rw [F.map_comp, h, Category.assoc, Category.assoc, ← F.map_comp, cokernel.condition,
      F.map_zero, Functor.map_zero, comp_zero, comp_zero]

end CategoryTheory

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The pullback commutes with multiplication by a scalar. -/
lemma AdicSheaf.adicUpperStar_map_smul {X Z : Scheme.{u}} (g : X ⟶ Z)
    (c : ULift.{u + 1} (PadicAlgCl l)) (M : AdicSheaf l Z) :
    (g)^*ᵃ[l].map (AdicSheaf.smul c M) = AdicSheaf.smul c ((g)^*ᵃ[l].obj M) := by
  apply ((adicUpperStarLowerStarAdjunction l g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← Functor.comp_map,
    ← (adicUpperStarLowerStarAdjunction l g).unit.naturality, Functor.id_map,
    AdicSheaf.adicLowerStar_map_smul]
  exact AdicSheaf.smul_comp c _

/-- A morphism of sheaves of `ℚ̄_ℓ,Z`-modules vanishes if its pullback along a quasi-compact
surjective weakly étale morphism does: its image vanishes, being detected on the pullback
(`AlgebraicGeometry.ProEtale.AdicSheaf.isZero_of_isZero_upperStar`). -/
lemma AdicSheaf.eq_zero_of_adicUpperStar_map_eq_zero {W Z : Scheme.{u}} (π : W ⟶ Z)
    [WeaklyEtale π] [QuasiCompact π] [Surjective π] {A B : AdicSheaf l Z} (h : A ⟶ B)
    (hh : (π)^*ᵃ[l].map h = 0) : h = 0 := by
  have hz : IsZero (Abelian.image h) := by
    refine AdicSheaf.isZero_of_isZero_upperStar (fun _ : PUnit.{u + 1} ↦ π) ?_ fun _ ↦ ?_
    · rw [Presieve.ofArrows_pUnit]
      exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
    · refine IsZero.of_iso ?_ (Abelian.PreservesImage.iso (π)^*ᵃ[l] h)
      have : Abelian.factorThruImage ((π)^*ᵃ[l].map h) = 0 := by
        rw [← cancel_mono (Abelian.image.ι _), Abelian.image.fac, zero_comp]
        exact hh
      exact IsZero.of_epi_eq_zero _ this
  rw [← Abelian.image.fac h, hz.eq_of_src (Abelian.image.ι h) 0, comp_zero]

/-- The pullback along a quasi-compact surjective weakly étale morphism is faithful. -/
lemma AdicSheaf.faithful_adicUpperStar {W Z : Scheme.{u}} (π : W ⟶ Z) [WeaklyEtale π]
    [QuasiCompact π] [Surjective π] : (π)^*ᵃ[l].Faithful where
  map_injective {A B} f g hfg := by
    rw [← sub_eq_zero]
    exact AdicSheaf.eq_zero_of_adicUpperStar_map_eq_zero π _
      (by rw [Functor.map_sub, hfg, sub_self])

end ProEtale


namespace ProEtale

variable {Z W Z' W' : Scheme.{u}} {π : W ⟶ Z} {G : Type u} [Finite G] {τ : G → (W ≅ W)}
  {hτ : ∀ g, (τ g).hom ≫ π = π}

/-- **Splittings are stable under base change.** If the automorphisms `τ_g` split `π`, then
their base changes `τ'_g` along `q : Z' ⟶ Z` split the base change `π' : W' ⟶ Z'` of `π`. -/
lemma IsTorsorSplit.of_isPullback (hsplit : IsTorsorSplit π τ hτ) {π' : W' ⟶ Z'} {p : W' ⟶ W}
    {q : Z' ⟶ Z} (sq : IsPullback p π' π q) (τ' : G → (W' ≅ W'))
    (hτ' : ∀ g, (τ' g).hom ≫ π' = π') (hp : ∀ g, (τ' g).hom ≫ p = p ≫ (τ g).hom) :
    IsTorsorSplit π' τ' hτ' := by
  have : IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := π) (g := π) (𝟙 W) (τ g).hom
    (by simp [hτ]) : ∐ (fun _ : G ↦ W) ⟶ pullback π π) := hsplit
  have h₁ := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp π (fun g ↦ (τ g).hom) hτ p
  have hP : IsPullback (pullback.fst π' π') (pullback.snd π' π' ≫ p) (p ≫ π) π := by
    have := (IsPullback.of_hasPullback π' π').flip.paste_horiz sq
    rw [← sq.w] at this
    exact this.flip
  suffices IsIso (Sigma.desc (fun g : G ↦ pullback.lift (f := π') (g := π') (𝟙 _) (τ' g).hom
      (by simp [hτ'])) ≫ hP.isoPullback.hom) from IsIso.of_isIso_comp_right _ hP.isoPullback.hom
  convert h₁ using 1
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  simp only [colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app]
  apply pullback.hom_ext
  · simp
  · simp [hp]

end ProEtale

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)}

/-- The base change `e × 𝟙 : X₀ ×_{Spec k} Spec k̄ ≅ Y₀ ×_{Spec k} Spec k̄` of an isomorphism
`e : X₀ ≅ Y₀` of schemes over `k`. -/
noncomputable def geometricFiberMapIso (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    f.geometricFiber ≅ g.geometricFiber where
  hom := geometricFiberMap e.hom h
  inv := geometricFiberMap e.inv (by rw [← h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.hom_inv_id]
    exact geometricFiberMap_id
  inv_hom_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.inv_hom_id]
    exact geometricFiberMap_id

@[simp]
lemma geometricFiberMapIso_hom (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    (geometricFiberMapIso e h).hom = geometricFiberMap e.hom h :=
  rfl

end Scheme.Hom


section Weil

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ`, as an endomorphism of a pro-étale Weil sheaf: the
Frobenius pullback, a pushforward, commutes with it. -/
noncomputable def ProEtaleWeilSheaf.smulEnd (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    A ⟶ A :=
  ObjectProperty.homMk ⟨ProEtale.AdicSheaf.smul (ULift.up b) A.carrier, by
    rw [ProEtale.AdicSheaf.adicLowerStar_map_smul, ProEtale.AdicSheaf.smul_comp]⟩

@[simp]
lemma ProEtaleWeilSheaf.smulEnd_hom_f (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.smulEnd b A).hom.f = ProEtale.AdicSheaf.smul (ULift.up b) A.carrier :=
  rfl

lemma ProEtaleWeilSheaf.smulEnd_comp (b : PadicAlgCl l) {A B : ProEtaleWeilSheaf k₀ l X}
    (f : A ⟶ B) : ProEtaleWeilSheaf.smulEnd b A ≫ f = f ≫ ProEtaleWeilSheaf.smulEnd b B :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_comp _ _))

lemma ProEtaleWeilSheaf.smulEnd_smulEnd (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd b A ≫ ProEtaleWeilSheaf.smulEnd c A =
      ProEtaleWeilSheaf.smulEnd (c * b) A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_smul _ _ _))

lemma ProEtaleWeilSheaf.smulEnd_one (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd 1 A = 𝟙 A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_one _))

lemma ProEtaleWeilSheaf.smulEnd_add (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd (b + c) A =
      ProEtaleWeilSheaf.smulEnd b A + ProEtaleWeilSheaf.smulEnd c A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
    change (ULift.up (b + c) : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ =
      (ULift.up b : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ +
        (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
    rw [← add_smul]
    rfl)))

lemma ProEtaleWeilSheaf.sum_smulEnd {ι : Type*} (s : Finset ι) (b : ι → PadicAlgCl l)
    (A : ProEtaleWeilSheaf k₀ l X) :
    ∑ i ∈ s, ProEtaleWeilSheaf.smulEnd (b i) A = ProEtaleWeilSheaf.smulEnd (∑ i ∈ s, b i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
      change 0 = (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
      rw [show (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) = 0 from rfl, zero_smul])))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ProEtaleWeilSheaf.smulEnd_add]

end Scalar

section Torsor

lemma _root_.AlgebraicGeometry.Scheme.Hom.geometricFiberMap_congr {k : Type u} [Field k]
    {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)} {φ ψ : X₀ ⟶ Y₀}
    (e : φ = ψ) (h : φ ≫ g = f) (h' : ψ ≫ g = f) :
    Scheme.Hom.geometricFiberMap φ h = Scheme.Hom.geometricFiberMap ψ h' := by
  subst e
  rfl

lemma ProEtaleWeilSheaf.adicConstant_str_hom_hom (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom.hom =
      (ProEtale.adicConstantSheafLowerStarIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm).hom :=
  rfl

variable {Z W : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] (π : W ⟶ Z) [π.IsOver (Spec (CommRingCat.of k₀))]
  {G : Type u} (τ : G → (W ≅ W)) [hτk : ∀ g, (τ g).hom.IsOver (Spec (CommRingCat.of k₀))]
  (hτ : ∀ g, (τ g).hom ≫ π = π)

variable (k₀) in
/-- The base change `τ̄_g` of the automorphism `τ_g` to the geometric fibre. -/
noncomputable abbrev geometricTorsorAut (g : G) :
    (W ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅ (W ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMapIso (τ g) (comp_over (τ g).hom _)

local notation "π̄" => Scheme.Hom.geometricFiberMap π (comp_over π (Spec (CommRingCat.of k₀)))

variable (k₀) in
lemma geometricTorsorAut_comp (hτ : ∀ g, (τ g).hom ≫ π = π) (g : G) :
    (geometricTorsorAut k₀ τ g).hom ≫ π̄ = π̄ := by
  rw [Scheme.Hom.geometricFiberMapIso_hom, ← Scheme.Hom.geometricFiberMap_comp]
  exact Scheme.Hom.geometricFiberMap_congr (hτ g) _ _

variable (k₀ l) in
/-- The pushforward `π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf. -/
noncomputable abbrev ProEtaleWeilSheaf.torsorPushforward : ProEtaleWeilSheaf k₀ l Z :=
  (ProEtaleWeilSheaf.lowerStar k₀ l π).obj (ProEtaleWeilSheaf.adicConstant k₀ l W)

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves: the exchange of `π̄_*` with the
Frobenius pushforwards followed by `π̄_*` of the Weil structure of `ℚ̄_ℓ`. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄ (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv π̄).symm).app
          (ProEtaleWeilSheaf.adicConstant k₀ l W).carrier.X ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm)).hom := by
  unfold ProEtaleWeilSheaf.torsorPushforward ProEtaleWeilSheaf.lowerStar
  rw [Endofunctor.IsoAlgebra.mapOfNatIso_obj_str, Iso.trans_hom, Mod.comp_hom',
    Functor.mapIso_hom, ProEtale.adicLowerStar_map_hom]
  erw [ProEtaleWeilSheaf.adicConstant_str_hom_hom]
  rw [ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.app_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', ProEtale.adicLowerStarComp_hom_app_hom, ProEtale.adicLowerStarComp_inv_app_hom,
    ProEtale.adicLowerStarCongr_hom_app_hom]
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄ (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv π̄).symm).app
          (ProEtale.adicConstantSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm)).hom :=
  ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' π

/-- The action of `τ_g` on `π_* ℚ̄_ℓ` commutes with its Weil structure: `τ_g` and `π` are
defined over `k₀`, hence commute with the geometric Frobenius. -/
lemma ProEtaleWeilSheaf.torsorTranslation_comm (g : G) :
    (WeilSheaf.frobeniusPullback k₀ l Z).map (ProEtale.torsorTranslation l π̄
        (geometricTorsorAut k₀ τ) (geometricTorsorAut_comp k₀ π τ hτ) g) ≫
        (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str =
      (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str ≫
        ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
          (geometricTorsorAut_comp k₀ π τ hτ) g := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    ProEtale.torsorTranslation_hom, ← Endofunctor.IsoAlgebra.str_hom,
    ProEtaleWeilSheaf.torsorPushforward_str_hom_hom]
  exact ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange l π̄
    (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (geometricTorsorAut k₀ τ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (geometricTorsorAut_comp k₀ π τ hτ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius _ _) _ rfl

/-- The action of `τ_g` on `π_* ℚ̄_ℓ`, pulling back sections along `τ_g`, as an endomorphism of
pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.torsorTranslation (g : G) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  ObjectProperty.homMk ⟨ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
    (geometricTorsorAut_comp k₀ π τ hτ) g, ProEtaleWeilSheaf.torsorTranslation_comm π τ hτ g⟩

@[simp]
lemma ProEtaleWeilSheaf.torsorTranslation_hom_f (g : G) :
    (ProEtaleWeilSheaf.torsorTranslation (l := l) π τ hτ g).hom.f =
      ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
        (geometricTorsorAut_comp k₀ π τ hτ) g :=
  rfl

variable [AddCommGroup G] [Finite G]

/-- The projector `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` of `π_* ℚ̄_ℓ` onto its `χ`-isotypic component. -/
noncomputable def ProEtaleWeilSheaf.torsorIdempotent (χ : AddChar G (PadicAlgCl l)) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  letI := Fintype.ofFinite G
  ∑ g : G, ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
    ProEtaleWeilSheaf.torsorTranslation π τ hτ g

/-- A morphism on which `G` acts through `χ` is fixed by the projector `e_χ`. -/
lemma ProEtaleWeilSheaf.comp_torsorIdempotent (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : ProEtaleWeilSheaf k₀ l Z}
    (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ : ∀ g, φ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ g) M ≫ φ) :
    φ ≫ ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ = φ := by
  let := Fintype.ofFinite G
  rw [ProEtaleWeilSheaf.torsorIdempotent, Preadditive.comp_sum]
  have (g : G) : φ ≫ ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
      ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹) M ≫ φ := by
    rw [← Category.assoc, ← ProEtaleWeilSheaf.smulEnd_comp, Category.assoc, hφ,
      ← Category.assoc, ProEtaleWeilSheaf.smulEnd_smulEnd, mul_left_comm,
      ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  simp_rw [this]
  rw [← Preadditive.sum_comp, ProEtaleWeilSheaf.sum_smulEnd, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀ hG,
    ProEtaleWeilSheaf.smulEnd_one, Category.id_comp]


/-- **Isotypic morphisms into the pushforward along a split torsor.** Let `φ : M ⟶ π_* ℚ̄_ℓ` be a
morphism of pro-étale Weil sheaves on which `G` acts through the character `χ`, whose adjoint
`π̄^* M ⟶ ℚ̄_ℓ` is an isomorphism. Then `φ` is split by a morphism `r` with `r ≫ φ = e_χ`: `M` is
the `χ`-isotypic component of `π_* ℚ̄_ℓ`. After pullback along `π̄`, the pullback of `e_χ` is the
averaging `∑_g |G|⁻¹ χ(-g) ev_g` of the evaluations along the sections of the torsor followed by
the inverse of the adjoint of `φ` and the pullback of `φ`, as one checks on the evaluations, which
are jointly injective. -/
theorem ProEtaleWeilSheaf.exists_retraction_of_isotypic [Etale π] [QuasiCompact π]
    [Surjective π] (hadd : ∀ g h, (τ (g + h)).hom = (τ g).hom ≫ (τ h).hom)
    (hsplit : ProEtale.IsTorsorSplit π τ hτ) (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : ProEtaleWeilSheaf k₀ l Z}
    (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ : ∀ g, φ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ g) M ≫ φ)
    (hθ : IsIso ((π̄)^*ᵃ[l].map φ.hom.f ≫
      (ProEtale.adicUpperStarLowerStarAdjunction l π̄).counit.app _)) :
    ∃ r : ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ M,
      φ ≫ r = 𝟙 M ∧ r ≫ φ = ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ := by
  let := Fintype.ofFinite G
  have : Etale π̄ := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) _ _
    ‹_›
  have : Surjective π̄ :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Surjective) _ _ ‹_›
  have : (π̄)^*ᵃ[l].Faithful := ProEtale.AdicSheaf.faithful_adicUpperStar π̄
  have hτ̄ := geometricTorsorAut_comp k₀ π τ hτ
  have hsplit' : ProEtale.IsTorsorSplit π̄ (geometricTorsorAut k₀ τ) hτ̄ :=
    hsplit.of_isPullback (Scheme.Hom.isPullback_geometricFiberMap π _).flip _ hτ̄
      fun g ↦ Scheme.Hom.geometricFiberMap_comp_geometricFiberProj _ _
  have hadd' (g h : G) : (geometricTorsorAut k₀ τ (g + h)).hom =
      (geometricTorsorAut k₀ τ g).hom ≫ (geometricTorsorAut k₀ τ h).hom := by
    simp only [Scheme.Hom.geometricFiberMapIso_hom]
    rw [← Scheme.Hom.geometricFiberMap_comp]
    exact Scheme.Hom.geometricFiberMap_congr (hadd g h) _ _
  let F := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z) ⋙ (π̄)^*ᵃ[l]
  let ev := ProEtale.torsorEval l π̄ (geometricTorsorAut k₀ τ) hτ̄
  let U := ProEtale.AdicSheaf.unit l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let c : G → PadicAlgCl l := fun g ↦ (Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)
  have hF (A : ProEtaleWeilSheaf k₀ l Z) (b : PadicAlgCl l) :
      F.map (ProEtaleWeilSheaf.smulEnd b A) = ProEtale.AdicSheaf.smul (ULift.up b) (F.obj A) :=
    ProEtale.AdicSheaf.adicUpperStar_map_smul _ _ _
  obtain ⟨hmono, hcok⟩ := F.mono_and_comp_cokernel_eq_zero_of_jointlyMono ev
    (fun a b h ↦ Mod.hom_ext _ _ (ProEtale.torsorEval_hom_ext _ _ _ hsplit' fun g ↦ by
      rw [← Mod.comp_hom', ← Mod.comp_hom', h g]))
    (fun g ↦ ProEtale.AdicSheaf.smul (ULift.up (χ g)) U) 0
    (by rw [AddChar.map_zero_eq_one]; exact ProEtale.AdicSheaf.smul_one U)
    (ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ)
    (∑ g : G, ProEtale.AdicSheaf.smul (ULift.up (c g)) _ ≫ ev g) φ _ (fun h ↦ ?_) (fun g ↦ ?_)
  · refine ⟨Abelian.monoLift φ _ hcok, ?_, Abelian.monoLift_comp _ _ _⟩
    rw [← cancel_mono φ, Category.assoc, Abelian.monoLift_comp, Category.id_comp,
      ProEtaleWeilSheaf.comp_torsorIdempotent π τ hτ χ hG φ hφ]
  · have e₁ : F.map (ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ) =
        ∑ g : G, ProEtale.AdicSheaf.smul (ULift.up (c g)) _ ≫
          (π̄)^*ᵃ[l].map (ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ) hτ̄ g) := by
      rw [ProEtaleWeilSheaf.torsorIdempotent, Functor.map_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [Functor.map_comp, hF]
      rfl
    rw [e₁, Preadditive.sum_comp, Preadditive.sum_comp]
    simp only [Category.assoc]
    simp_rw [ProEtale.upperStar_map_torsorTranslation_comp_torsorEval _ _ _ hadd']
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight h)]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [Equiv.coe_addRight]
    rw [← ProEtale.AdicSheaf.smul_comp, ← Category.assoc, ProEtale.AdicSheaf.smul_smul]
    have hχ : χ h * χ (-h) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    congr 2
    simp only [c, neg_add, AddChar.map_add_eq_mul]
    linear_combination (-((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g))) * hχ
  · change (π̄)^*ᵃ[l].map φ.hom.f ≫ (π̄)^*ᵃ[l].map _ ≫ _ = _
    rw [← Functor.map_comp_assoc]
    have := congrArg (fun f ↦ f.hom.f) (hφ g)
    simp only [Endofunctor.IsoAlgebra.comp_hom_f, ProEtaleWeilSheaf.smulEnd_hom_f,
      ProEtaleWeilSheaf.torsorTranslation_hom_f] at this
    rw [this, Functor.map_comp, ProEtale.AdicSheaf.adicUpperStar_map_smul, Category.assoc,
      ProEtale.AdicSheaf.smul_comp]

end Torsor

end Weil

end AlgebraicGeometry
