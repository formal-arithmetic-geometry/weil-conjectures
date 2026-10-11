/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.CategoryTheory.Comma.Over.DescentRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Sites.SingletonCover
public import WeilConjectures.CategoryTheory.Sites.SingletonSheaf

/-!
# The canonical descent datum is defined at a finite level

Let `ks / k` be an algebraic field extension, let `F` be a presheaf on `k`-schemes and let `Js` be
a scheme of finite presentation over `ks` representing the restriction of `F` to `ks`-schemes.
Then `Js` carries the canonical descent datum relative to `Spec ks ⟶ Spec k`
(`CategoryTheory.Functor.RepresentableBy.overDescentDatum`). We show that the whole situation is
defined over a finite subextension `K` of `ks / k`:
`Js` is the base change of a `K`-scheme `J_K` whose projection `Js ⟶ J_K` is invariant under the
canonical transport along `ks / K`
(`AlgebraicGeometry.exists_le_isTransportInvariant`).

The invariance is an equality of two morphisms over the universal pair of points of
`Spec ks ×_{Spec K} Spec ks`; these fibre products form a cofiltered system with limit the
diagonal `Spec ks` (`AlgebraicGeometry.FiniteIntermediateField.isLimitDiagCone`), over which the
two morphisms agree since the transport along equal points is trivial, so they agree at a finite
stage (Stacks 01ZM, `AlgebraicGeometry.Scheme.exists_pullback_fst_comp_eq_of_isLimit`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k ks : Type u} [Field k] [Field ks] [Algebra k ks]

lemma specMap_algebraMap_comp_specMap_algebraMap_intermediateField
    (K : IntermediateField k ks) :
    Spec.map (CommRingCat.ofHom (algebraMap K ks)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable [Algebra.IsAlgebraic k ks] {F : (Over (Spec (.of k)))ᵒᵖ ⥤ Type w}
  {Js : Over (Spec (.of ks))}
  (rs : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap k ks)))).op ⋙ F).RepresentableBy Js)

open FiniteIntermediateField in
/-- **The projection to a finite-level model becomes invariant at a finite level.** Let `Js`
be of finite presentation over `ks`, and let `h : Js ⟶ Y` exhibit `Js` as the base change of a
scheme `Y` of finite presentation over a finite subextension `K₀`. Then for some finite
subextension `K ⊇ K₀`, `h` is invariant under the canonical transport of `rs` between points of
`Js` lying over the same point of `Spec K`. -/
theorem exists_le_isTransportInvariant [LocallyOfFinitePresentation Js.hom]
    [QuasiCompact Js.hom] [QuasiSeparated Js.hom] {K₀ : FiniteIntermediateField k ks}
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of K₀.1)) [LocallyOfFinitePresentation pY]
    [QuasiCompact pY] [QuasiSeparated pY] (h : Js.left ⟶ Y)
    (hh : IsPullback h Js.hom pY (Spec.map (CommRingCat.ofHom (algebraMap K₀.1 ks)))) :
    ∃ K : FiniteIntermediateField k ks, K₀ ≤ K ∧ ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Spec (.of ks))
      (hf : f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap K.1 ks)) =
        f₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap K.1 ks))) (a : Over.mk f₁ ⟶ Js),
      (rs.overTransport f₁ f₂ (by
          rw [← specMap_algebraMap_comp_specMap_algebraMap_intermediateField K.1, reassoc_of% hf])
        a).left ≫ h = a.left ≫ h := by
  let ps := Spec.map (CommRingCat.ofHom (algebraMap k ks))
  let ι₀ := Spec.map (CommRingCat.ofHom (algebraMap K₀.1 ks))
  have hι₀ : ι₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k K₀.1)) = ps :=
    specMap_algebraMap_comp_specMap_algebraMap_intermediateField K₀.1
  let pr₁ : diagObj K₀ ⟶ Spec (.of ks) := pullback.fst ι₀ ι₀
  let pr₂ : diagObj K₀ ⟶ Spec (.of ks) := pullback.snd ι₀ ι₀
  -- the universal point of `Js` over the first projection, and its transport
  let V := pullback Js.hom pr₁
  let pV : V ⟶ diagObj K₀ := pullback.snd Js.hom pr₁
  let aU : Over.mk (pV ≫ pr₁) ⟶ Js := Over.homMk (pullback.fst Js.hom pr₁) pullback.condition
  have hpair : (pV ≫ pr₁) ≫ ps = (pV ≫ pr₂) ≫ ps := by
    rw [← hι₀, Category.assoc, Category.assoc, pullback.condition_assoc]
  let tU := rs.overTransport (pV ≫ pr₁) (pV ≫ pr₂) hpair aU
  let W := pullback pY (pr₁ ≫ ι₀)
  let pW : W ⟶ diagObj K₀ := pullback.snd pY (pr₁ ≫ ι₀)
  let ψ : V ⟶ W := pullback.lift (tU.left ≫ h) pV (by
    rw [Category.assoc, hh.w, ← Category.assoc, Over.w tU]
    simp [pr₁, pr₂, ι₀, pullback.condition])
  let χ : V ⟶ W := pullback.lift (pullback.fst Js.hom pr₁ ≫ h) pV (by
    rw [Category.assoc, hh.w, pullback.condition_assoc])
  have hψ : ψ ≫ pW = pV := pullback.lift_snd _ _ _
  have hχ : χ ≫ pW = pV := pullback.lift_snd _ _ _
  -- over the diagonal the transport is trivial
  let Δ : Spec (.of ks) ⟶ diagObj K₀ := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hΔ : pullback.fst pV Δ ≫ ψ = pullback.fst pV Δ ≫ χ := by
    let g := pullback.fst pV Δ
    have hg (pr : diagObj K₀ ⟶ Spec (.of ks)) (hpr : Δ ≫ pr = 𝟙 _) :
        g ≫ pV ≫ pr = pullback.snd pV Δ := by
      rw [← Category.assoc, pullback.condition, Category.assoc, hpr, Category.comp_id]
    apply pullback.hom_ext
    · have e := rs.overTransport_homMk_comp g (pV ≫ pr₁) (pV ≫ pr₂) hpair aU
      have e' := congrArg CommaMorphism.left e
      simp only [Over.comp_left, Over.homMk_left] at e'
      simp only [Category.assoc, ψ, χ, pullback.lift_fst]
      rw [← Category.assoc, ← e']
      have heq : g ≫ pV ≫ pr₁ = g ≫ pV ≫ pr₂ :=
        (hg pr₁ (pullback.lift_fst _ _ _)).trans (hg pr₂ (pullback.lift_snd _ _ _)).symm
      simp only [rs.overTransport_left_of_eq _ heq, Over.comp_left, Over.homMk_left, aU,
        Category.assoc]
      rfl
    · simp [ψ, χ]
  obtain ⟨j, fj, hj⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit (isLimitDiagCone k ks)
    pV pW ψ χ hψ hχ hΔ
  refine ⟨j.unop, leOfHom fj.unop, fun {T} f₁ f₂ hf a ↦ ?_⟩
  -- a pair of points over `K` factors through the universal one
  let u : T ⟶ diagObj j.unop := pullback.lift f₁ f₂ hf
  let v₀ : T ⟶ V := pullback.lift a.left (u ≫ (diagDiagram k ks).map fj) (by
    simp [u, pr₁, ι₀, diagMap_fst, Over.w a])
  let v : T ⟶ pullback pV ((diagDiagram k ks).map fj) :=
    pullback.lift v₀ u (pullback.lift_snd _ _ _)
  have hv := congrArg (fun m ↦ v ≫ m ≫ pullback.fst pY (pr₁ ≫ ι₀)) hj
  simp only [ψ, χ, Category.assoc, pullback.lift_fst, v, pullback.lift_fst_assoc, v₀] at hv
  rw [← hv]
  have e := rs.overTransport_homMk_comp v₀ (pV ≫ pr₁) (pV ≫ pr₂) hpair aU
  have e' := congrArg CommaMorphism.left e
  simp only [Over.comp_left, Over.homMk_left] at e'
  rw [← reassoc_of% e']
  congr 1
  refine rs.overTransport_left_congr _ _ ?_ ?_ _ _ ?_
  · simp [v₀, pV, pr₁, u, ι₀]
  · simp [v₀, pV, pr₂, u, ι₀]
  · simp [v₀, aU]


open FiniteIntermediateField Functor.RepresentableBy in
/-- **The canonical descent datum is defined at a finite separable level.** Let `ks / k` be an
algebraic extension, let `F` be a presheaf on `k`-schemes satisfying the sheaf condition for
every flat surjective quasi-compact morphism, and let `rs` exhibit a scheme `Js` of finite
presentation over `ks` as a representing object of the restriction of `F` to `ks`-schemes. Then
there are a finite subextension `K`, a `K`-scheme `J_K` with `J_K ×_K ks ≅ Js`, and a descent
datum on `J_K` relative to `Spec K ⟶ Spec k` whose base change to `ks` is the canonical descent
datum of `rs`.

The scheme `J_K` comes from spreading out `Js` (Stacks 01ZM), at a level where the projection
`Js ⟶ J_K` is invariant under the canonical transport along `ks / K`
(`AlgebraicGeometry.exists_le_isTransportInvariant`). Then `J_K` represents the restriction of
`F` to `K`-schemes (`CategoryTheory.Functor.RepresentableBy.exists_representableBy_of_isPullback`),
compatibly with `rs`, and the descent datum is its canonical descent datum.

(blueprint: `cor-pd-finite-level`) -/
theorem exists_intermediateField_isBaseChange [LocallyOfFinitePresentation Js.hom]
    [QuasiCompact Js.hom] [QuasiSeparated Js.hom]
    (hF : ∀ {T T' : Over (Spec (.of k))} (π : T' ⟶ T) [Flat π.left] [Surjective π.left]
      [QuasiCompact π.left], Presieve.IsSheafFor F (.singleton π)) :
    ∃ (K : IntermediateField k ks), FiniteDimensional k K ∧
      ∃ (JK : Over (Spec (.of K))) (q : Js.left ⟶ JK.left)
        (hq : IsPullback q Js.hom JK.hom (Spec.map (CommRingCat.ofHom (algebraMap K ks))))
        (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k K))) JK),
        D.IsBaseChange (specMap_algebraMap_comp_specMap_algebraMap_intermediateField K) hq.w
          rs.overDescentDatum := by
  obtain ⟨i, Y, pY, _, _, _, h, hh⟩ :=
    Scheme.exists_isPullback_of_finitePresentation (isLimitSpecCone k ks) Js.hom
  obtain ⟨K, hK₀, hK⟩ := exists_le_isTransportInvariant rs pY h hh
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap K.1 ks))
  let pK := Spec.map (CommRingCat.ofHom (algebraMap k K.1))
  have hs : ιK ≫ pK = Spec.map (CommRingCat.ofHom (algebraMap k ks)) :=
    specMap_algebraMap_comp_specMap_algebraMap_intermediateField K.1
  have : Flat ιK := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective ιK := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  -- the finite-level model `J_K` and the projection `q : Js ⟶ J_K`
  let JK : Over (Spec (.of K.1)) := Over.mk (pullback.snd pY (specMap hK₀))
  let q : Js.left ⟶ JK.left := pullback.lift h (Js.hom ≫ ιK) (by
    rw [hh.w, Category.assoc, specCone_π_app_specMap]
    rfl)
  have hq : IsPullback q Js.hom JK.hom ιK :=
    IsPullback.of_right (by rw [pullback.lift_fst, specCone_π_app_specMap]; exact hh)
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback pY (specMap hK₀))
  -- `J_K` represents the restriction of `F` to `K`-schemes, compatibly with `rs`
  let r' := rs.overMapComp hs
  have hinv : r'.IsTransportInvariant q := fun f₁ f₂ hf a ↦ by
    rw [overTransport_overMapComp]
    apply pullback.hom_ext
    · simpa [q] using hK f₁ f₂ hf a
    · simp only [q, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, Over.w, ← Category.assoc, Over.w a]
      exact hf.symm
  have hFK (T : Over (Spec (.of K.1))) : Presieve.IsSheafFor ((Over.map pK).op ⋙ F)
      (.singleton (Over.baseChangeπ ιK T)) := by
    have : Flat ((Over.map pK).map (Over.baseChangeπ ιK T)).left :=
      inferInstanceAs (Flat (pullback.fst _ _))
    have : Surjective ((Over.map pK).map (Over.baseChangeπ ιK T)).left :=
      inferInstanceAs (Surjective (pullback.fst _ _))
    have : QuasiCompact ((Over.map pK).map (Over.baseChangeπ ιK T)).left :=
      inferInstanceAs (QuasiCompact (pullback.fst _ _))
    exact Presieve.isSheafFor_singleton_of_overMap pK _ (hF _)
  have hJK (T : Over (Spec (.of K.1))) : Presieve.IsSheafFor (yoneda.obj JK)
      (.singleton (Over.baseChangeπ ιK T)) := by
    have : Flat (Over.baseChangeπ ιK T).left := inferInstanceAs (Flat (pullback.fst _ _))
    have : Surjective (Over.baseChangeπ ιK T).left :=
      inferInstanceAs (Surjective (pullback.fst _ _))
    have : QuasiCompact (Over.baseChangeπ ιK T).left :=
      inferInstanceAs (QuasiCompact (pullback.fst _ _))
    exact isSheafFor_singleton_yoneda JK _
  obtain ⟨rK, hrK⟩ := exists_representableBy_of_isPullback (r := r') hq hinv hFK hJK
  refine ⟨K.1, K.2, JK, q, hq, rK.overDescentDatum, fun T f₁ f₂ hf a ↦ ?_⟩
  -- the canonical transport of `rK` lifts that of `rs`
  let b := rs.overTransport f₁ f₂ hf a
  have key : rK.overTransport (f₁ ≫ ιK) (f₂ ≫ ιK) (by simpa [hs] using hf)
      (Over.homMk (a.left ≫ q) (by rw [Category.assoc, hq.w, ← Category.assoc, Over.w a]; rfl) :
        Over.mk (f₁ ≫ ιK) ⟶ JK) =
        (Over.homMk (b.left ≫ q) (by rw [Category.assoc, hq.w, ← Category.assoc, Over.w b]; rfl) :
          Over.mk (f₂ ≫ ιK) ⟶ JK) := by
    apply rK.homEquiv.injective
    erw [homEquiv_overTransport, hrK f₁ a, hrK f₂ b]
    rw [overMapComp_homEquiv, overMapComp_homEquiv]
    erw [homEquiv_overTransport]
    erw [← Functor.map_comp_apply F, ← Functor.map_comp_apply F]
    exact congrArg (fun φ ↦ F.map φ _) (Quiver.Hom.unop_inj (by ext; simp))
  exact congrArg CommaMorphism.left key

end AlgebraicGeometry
