/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Finite étale covers over a smooth scheme over a normal base

Let `S` be an integral normal scheme with function field `K`, let `t : T ⟶ S` be smooth and let
`T_K ⟶ T` be the generic fibre of `t`. The relative normalization of `T` in `T_K` is `T` itself
(`AlgebraicGeometry.Scheme.isIso_fromNormalization_of_isPullback`): normalization commutes with
the smooth base change `t`, and the normalization of `S` in `Spec K` is `S` as `S` is normal.
By the universal property of the normalization, a morphism `T_K ⟶ Y` into an integral
`T`-scheme extends uniquely to `T`
(`AlgebraicGeometry.Scheme.exists_lift_of_isPullback_fromSpecFunctionField`,
`AlgebraicGeometry.Scheme.hom_ext_of_isPullback_fromSpecFunctionField`).

Consequently, in the situation of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`), a finite étale `C`-scheme `Y` restricting to a
Galois cover `Z` of the generic fibre `C_η` of a smooth `C ⟶ S` with geometrically connected
fibres is itself a Galois cover with the same group, compatibly with `Z`
(`AlgebraicGeometry.Scheme.GaloisCover.exists_of_isPullback_isFinite_etale`): the action
extends to `Y`, and it is simply transitive since it is so on a geometric fibre over `C_η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The relative normalization is invariant under precomposition with an isomorphism: if the
normalization of `Y` along `g` is trivial, so is the one along `e ≫ g` for an isomorphism `e`. -/
lemma Hom.isIso_fromNormalization_of_iso_comp {X X' Y : Scheme.{u}} (e : X' ≅ X) (g : X ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g] [IsIso g.fromNormalization] (f : X' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (hf : e.hom ≫ g = f) :
    IsIso f.fromNormalization := by
  subst hf
  let φ := (e.hom ≫ g).normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp)
  let ψ := g.normalizationDesc (e.inv ≫ (e.hom ≫ g).toNormalization)
    (e.hom ≫ g).fromNormalization (by simp)
  have h1 : φ ≫ ψ = 𝟙 _ := Hom.normalization.hom_ext _ _ _ (e.hom ≫ g).fromNormalization
    (by simp [φ, ψ]) (by simp [φ, ψ]) (by simp)
  have h2 : ψ ≫ φ = 𝟙 _ := Hom.normalization.hom_ext _ _ _ g.fromNormalization
    (by simp [φ, ψ]) (by simp [φ, ψ]) (by simp)
  have : IsIso φ := ⟨ψ, h1, h2⟩
  rw [← (e.hom ≫ g).normalizationDesc_comp (e.hom ≫ g.toNormalization) g.fromNormalization
    (by simp)]
  infer_instance

/-- The relative normalization of a quasi-separated integral normal scheme `S` in its generic
point `Spec K ⟶ S` is `S` itself. -/
lemma isIso_fromNormalization_fromSpecFunctionField {S : Scheme.{u}} [IsIntegral S]
    [QuasiSeparatedSpace S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) :
    IsIso S.fromSpecFunctionField.fromNormalization := by
  have := S.isIso_fromNormalization_restrict ⊤ fun x _ ↦ hS x
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun _ : Unit ↦ ⊤) (by simp)]
  exact fun _ ↦ this

/-- Let `S` be a quasi-separated integral normal scheme with function field `K` and `t : T ⟶ S`
a smooth morphism. The relative normalization of `T` in its generic fibre `f : T_K ⟶ T` is `T`
itself: normalization commutes with the smooth base change `t`
(`AlgebraicGeometry.Scheme.Hom.normalizationPullback`), and the normalization of `S` in
`Spec K` is trivial. -/
theorem isIso_fromNormalization_of_isPullback {S T Tη : Scheme.{u}} [IsIntegral S]
    [QuasiSeparatedSpace S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (t : T ⟶ S) [Smooth t] (q : Tη ⟶ Spec S.functionField) (f : Tη ⟶ T)
    (h : IsPullback q f S.fromSpecFunctionField t) [QuasiCompact f] [QuasiSeparated f] :
    IsIso f.fromNormalization := by
  have := isIso_fromNormalization_fromSpecFunctionField hS
  have : IsIso (pullback.snd S.fromSpecFunctionField t).fromNormalization := by
    rw [← S.fromSpecFunctionField.normalizationPullback_snd t]
    infer_instance
  exact Hom.isIso_fromNormalization_of_iso_comp h.isoPullback _ f h.isoPullback_hom_snd

/-- Let `S` be a quasi-separated integral normal scheme with function field `K`, `t : T ⟶ S`
smooth with generic fibre `f : T_K ⟶ T`, and `w : Y ⟶ C` an integral morphism. Every morphism
`s : T_K ⟶ Y` lying over a morphism `g : T ⟶ C` extends to a morphism `T ⟶ Y` over `g`. -/
theorem exists_lift_of_isPullback_fromSpecFunctionField {S T Tη : Scheme.{u}} [IsIntegral S]
    [QuasiSeparatedSpace S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (t : T ⟶ S) [Smooth t] (q : Tη ⟶ Spec S.functionField) (f : Tη ⟶ T)
    (h : IsPullback q f S.fromSpecFunctionField t) {C Y : Scheme.{u}} (g : T ⟶ C)
    (w : Y ⟶ C) [IsIntegralHom w] (s : Tη ⟶ Y) (hs : s ≫ w = f ≫ g) :
    ∃ φ : T ⟶ Y, φ ≫ w = g ∧ f ≫ φ = s := by
  have : QuasiCompact f := MorphismProperty.of_isPullback h inferInstance
  have : QuasiSeparated f := MorphismProperty.of_isPullback h inferInstance
  have := isIso_fromNormalization_of_isPullback hS t q f h
  let s' : Tη ⟶ pullback w g := pullback.lift s f hs
  let d := f.normalizationDesc s' (pullback.snd w g) (by simp [s'])
  refine ⟨inv f.fromNormalization ≫ d ≫ pullback.fst w g, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc d,
      f.normalizationDesc_comp, IsIso.inv_hom_id_assoc]
  · have : f ≫ inv f.fromNormalization = f.toNormalization := by
      rw [IsIso.comp_inv_eq, Hom.toNormalization_fromNormalization]
    rw [reassoc_of% this, f.toNormalization_normalizationDesc_assoc, pullback.lift_fst]

/-- Let `S` be a quasi-separated integral normal scheme with function field `K`, `t : T ⟶ S`
smooth with generic fibre `f : T_K ⟶ T`, and `w : Y ⟶ C` an integral morphism. Two morphisms
`T ⟶ Y` with the same composite to `C` which agree on `T_K` are equal. -/
theorem hom_ext_of_isPullback_fromSpecFunctionField {S T Tη : Scheme.{u}} [IsIntegral S]
    [QuasiSeparatedSpace S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (t : T ⟶ S) [Smooth t] (q : Tη ⟶ Spec S.functionField) (f : Tη ⟶ T)
    (h : IsPullback q f S.fromSpecFunctionField t) {C Y : Scheme.{u}} (w : Y ⟶ C)
    [IsIntegralHom w] (φ₁ φ₂ : T ⟶ Y) (hw : φ₁ ≫ w = φ₂ ≫ w) (hf : f ≫ φ₁ = f ≫ φ₂) :
    φ₁ = φ₂ := by
  have : QuasiCompact f := MorphismProperty.of_isPullback h inferInstance
  have : QuasiSeparated f := MorphismProperty.of_isPullback h inferInstance
  have := isIso_fromNormalization_of_isPullback hS t q f h
  let σ₁ : T ⟶ pullback w (φ₁ ≫ w) := pullback.lift φ₁ (𝟙 T) (by simp)
  let σ₂ : T ⟶ pullback w (φ₁ ≫ w) := pullback.lift φ₂ (𝟙 T) (by simp [hw])
  have key : f.fromNormalization ≫ σ₁ = f.fromNormalization ≫ σ₂ :=
    Hom.normalization.hom_ext _ _ _ (pullback.snd w (φ₁ ≫ w))
      (by
        rw [Hom.toNormalization_fromNormalization_assoc,
          Hom.toNormalization_fromNormalization_assoc]
        apply pullback.hom_ext <;> simp [σ₁, σ₂, hf])
      (by simp [σ₁]) (by simp [σ₂])
  have h12 : σ₁ = σ₂ := (cancel_epi f.fromNormalization).1 key
  simpa [σ₁, σ₂] using congrArg (· ≫ pullback.fst w (φ₁ ≫ w)) h12

namespace GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}}

/-- On points with values in a scheme with exactly one point, the group of a Galois cover acts
transitively on the fibres: `(y, x)` is a point of `P ×_Y P ≅ ∐_{g ∈ G} P`, and it factors
through one summand. -/
lemma exists_comp_smul_eq (Z : GaloisCover G Y) {X : Scheme.{u}} [Subsingleton X] [Nonempty X]
    (x y : X ⟶ Z.P) (h : x ≫ Z.π = y ≫ Z.π) : ∃ g, x ≫ Z.smul g = y := by
  have := Z.isIso_sigmaDesc
  let D := Sigma.desc fun g : G ↦
    pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P) (by simp [Z.smul_π])
  obtain ⟨g, l, hl⟩ :=
    exists_comp_sigmaι_eq_of_subsingleton (pullback.lift y x h.symm ≫ inv D)
  have h1 : l ≫ pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P)
      (by simp [Z.smul_π]) = pullback.lift y x h.symm := by
    rw [← Sigma.ι_desc (fun g : G ↦ pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P)
      (by simp [Z.smul_π])) g, ← Category.assoc, hl]
    simp [D]
  have hfst := congrArg (· ≫ pullback.fst Z.π Z.π) h1
  have hsnd := congrArg (· ≫ pullback.snd Z.π Z.π) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hfst hsnd
  exact ⟨g, hsnd ▸ hfst⟩

/-- On points with values in a nonempty scheme, the group of a Galois cover acts freely: the
summands of `∐_{g ∈ G} P ≅ P ×_Y P` are disjoint. -/
lemma eq_of_comp_smul_eq (Z : GaloisCover G Y) {X : Scheme.{u}} [Nonempty X]
    (x : X ⟶ Z.P) {g h : G} (hgh : x ≫ Z.smul g = x ≫ Z.smul h) : g = h := by
  have := Z.isIso_sigmaDesc
  have h2 : x ≫ Sigma.ι (fun _ : G ↦ Z.P) g = x ≫ Sigma.ι (fun _ : G ↦ Z.P) h := by
    rw [← cancel_mono (Sigma.desc fun g : G ↦
      pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P) (by simp [Z.smul_π]))]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, Sigma.ι_desc_assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id, hgh]
  obtain ⟨a⟩ := ‹Nonempty X›
  have h3 := congrArg (fun f ↦ f a) h2
  simp only [Scheme.Hom.comp_apply] at h3
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : G ↦ Z.P) g h _ _).mp h3)

open FiniteEtale in
/-- Part of the proof of blueprint `sbc-thm-spreading-finite-etale-galois`: a finite étale
extension of a Galois cover of the generic fibre is a Galois cover.

Let `S` be a quasi-separated integral normal scheme, `c : C ⟶ S` smooth with geometrically
connected fibres and generic fibre `j : C_η ⟶ C`, and `Z` a Galois cover of `C_η` with group
`G`. If `Z` is the restriction to `C_η` of a finite étale `p : Y ⟶ C`, that is, the square
formed by `ψ : Z.P ⟶ Y` over `j` is cartesian, then `Y` is a Galois cover of `C` with group `G`
for which `ψ` is equivariant. The action of `G` extends from `Z.P` to `Y` by
`AlgebraicGeometry.Scheme.exists_lift_of_isPullback_fromSpecFunctionField`, as `Y` is smooth
over `S`; it is simply transitive since `C` is connected and the action is simply transitive
on a geometric fibre over a point of `C_η`. -/
theorem exists_of_isPullback_isFinite_etale {S C : Scheme.{u}} [IsIntegral S]
    [QuasiSeparatedSpace S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j S.fromSpecFunctionField c) [Nonempty Cη]
    (Z : GaloisCover G Cη) {Y : Scheme.{u}} (p : Y ⟶ C) [IsFinite p] [Etale p] (ψ : Z.P ⟶ Y)
    (hψ : IsPullback ψ Z.π p j) :
    ∃ (T : GaloisCover G C) (ψ' : Z.P ⟶ T.P), IsPullback ψ' Z.π T.π j ∧
      ∀ g : G, Z.smul g ≫ ψ' = ψ' ≫ T.smul g := by
  have hY : IsPullback (Z.π ≫ q) ψ S.fromSpecFunctionField (p ≫ c) :=
    hψ.flip.paste_horiz hCη
  -- the action of `G` extends to `Y`
  have hex (g : G) := exists_lift_of_isPullback_fromSpecFunctionField hS (p ≫ c) (Z.π ≫ q) ψ
    hY p p (Z.smul g ≫ ψ) (by rw [Category.assoc, hψ.w, ← Category.assoc, Z.smul_π])
  choose smulY hsmulp hψsmul using hex
  have uniq := hom_ext_of_isPullback_fromSpecFunctionField hS (p ≫ c) (Z.π ≫ q) ψ hY p
  -- a geometric point of `C` over `C_η`
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace (f := c) c.isOpenMap
  obtain ⟨z⟩ := ‹Nonempty Cη›
  let Ω := AlgebraicClosure (Cη.residueField z)
  let s₀ : Spec (.of Ω) ⟶ Cη :=
    Spec.map (CommRingCat.ofHom (algebraMap (Cη.residueField z) Ω)) ≫ Cη.fromSpecResidueField z
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  -- the action is simply transitive on the geometric fibre at `s₀ ≫ j`
  have key (a b : Spec (.of Ω) ⟶ Y) (ha : a ≫ p = s₀ ≫ j) (hb : b ≫ p = s₀ ≫ j) :
      ∃! g, a ≫ smulY g = b := by
    obtain ⟨g, hg⟩ := Z.exists_comp_smul_eq (hψ.lift a s₀ ha) (hψ.lift b s₀ hb) (by simp)
    have hab : a ≫ smulY g = b := by
      rw [← hψ.lift_fst a s₀ ha, Category.assoc, hψsmul, ← Category.assoc, hg, hψ.lift_fst]
    refine ⟨g, hab, fun h hh ↦ ?_⟩
    beta_reduce at hh
    refine Z.eq_of_comp_smul_eq (hψ.lift a s₀ ha) (hψ.hom_ext ?_ ?_)
    · simp only [Category.assoc, ← hψsmul]
      rw [reassoc_of% (hψ.lift_fst a s₀ ha), reassoc_of% (hψ.lift_fst a s₀ ha), hh, hab]
    · simp [Z.smul_π]
  let P : C.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ p inferInstance, inferInstanceAs (IsFinite p)⟩
  let v (g : G) : P ⟶ P :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk (smulY g) (hsmulp g))
  have hv (x y : (fiber (s₀ ≫ j)).obj P) : ∃! g, (fiber (s₀ ≫ j)).map (v g) x = y := by
    obtain ⟨g, hg, hu⟩ := key x.left y.left (fiber_left_comp _ x) (fiber_left_comp _ y)
    exact ⟨g, fiber_ext _ hg, fun h hh ↦ hu h (congrArg (fun u ↦ u.left) hh)⟩
  have hσ := isIso_sigmaDesc_of_existsUnique (s₀ ≫ j) P v hv
  -- `Y ⟶ C` is surjective, its image being open, closed and nonempty
  have : Surjective p := by
    have := Z.surjective
    obtain ⟨w, -⟩ := Z.π.surjective z
    have hc : IsClopen (Set.range p) := ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
    exact ⟨Set.range_eq_univ.1 (hc.eq_univ ⟨_, ψ w, rfl⟩)⟩
  let T : GaloisCover G C :=
    { P := Y
      π := p
      smul := smulY
      smul_π := hsmulp
      one_smul := uniq _ _ (by simp [hsmulp]) (by rw [hψsmul, Z.one_smul]; simp)
      mul_smul g h := uniq _ _ (by simp [hsmulp]) (by
        rw [hψsmul, Z.mul_smul, ← Category.assoc ψ, hψsmul]
        simp only [Category.assoc, hψsmul])
      isIso_sigmaDesc := hσ }
  exact ⟨T, ψ, hψ, fun g ↦ (hψsmul g).symm⟩

end GaloisCover

end AlgebraicGeometry.Scheme
