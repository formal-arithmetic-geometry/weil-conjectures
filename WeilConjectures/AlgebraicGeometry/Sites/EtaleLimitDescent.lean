/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Étale algebras and schemes descend along limits

Let `R = colim Rⱼ` be a filtered colimit of commutative rings. An étale `R`-algebra is the base
change of an étale algebra over one of the `Rⱼ`
(`CommRingCat.exists_isPushout_of_etale`): one lifts a standard smooth presentation of relative
dimension zero, together with an inverse of its Jacobian modulo the relations, and the identity
expressing this inverse, to a common stage.

Geometrically, let `{Dᵢ}` be a cofiltered system of schemes with affine transition maps and limit
`X = lim Dᵢ`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_isPullback_of_etale_of_isAffine`: if the `Dᵢ` are affine, an
  affine scheme étale over `X` is the base change of an affine scheme étale over some `Dᵢ`.
- `AlgebraicGeometry.Scheme.exists_isPullback_of_etale_of_isAffineOpen`: the same for
  quasi-separated `Dᵢ` and an affine scheme étale over `X` with image in an affine open of `X`.
- `AlgebraicGeometry.Scheme.exists_isPullbackLift_comp_eq`: for qcqs `Dᵢ` over `R`, a morphism over
  `R` from a base change `Y ×_{Dᵢ} X` to a scheme locally of finite presentation over `R`
  factors through `Y ×_{Dᵢ} Dₖ` for some `k ⟶ i`.
- `AlgebraicGeometry.isLimitBaseChangeOverCone`: for `W ⟶ R` and a system over `R`, the
  `W ×_R Dᵢ` have limit `W ×_R X`.

These are part of blueprint `lem-weil-pbc-etale-finite-data-descent`.
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits

namespace CommRingCat

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] (F : J ⥤ CommRingCat.{u})
  (c : Cocone F) [PreservesColimit F (forget CommRingCat)] (hc : IsColimit c)

include hc in
/-- Finitely many elements of a stage of a filtered colimit of rings which vanish in the colimit
vanish at a common later stage. -/
lemma exists_map_eq_zero_of_finset {j : J} (s : Finset (F.obj j))
    (hs : ∀ x ∈ s, c.ι.app j x = 0) : ∃ (k : J) (α : j ⟶ k), ∀ x ∈ s, F.map α x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k, α, hα⟩ := ih fun x hx ↦ hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨k', β, _, hβ⟩ := Concrete.isColimit_exists_of_rep_eq F hc a 0
      (by rw [hs a (Finset.mem_insert_self a s), map_zero])
    rw [map_zero] at hβ
    let l := IsFiltered.leftToMax k k'
    let r := IsFiltered.rightToMax k k'
    let m := IsFiltered.coeqHom (α ≫ l) (β ≫ r)
    have hm : α ≫ l ≫ m = β ≫ r ≫ m := by
      simpa only [Category.assoc] using IsFiltered.coeq_condition (α ≫ l) (β ≫ r)
    refine ⟨_, α ≫ l ≫ m, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [hm, Functor.map_comp, CommRingCat.comp_apply, hβ, map_zero]
    · rw [Functor.map_comp, CommRingCat.comp_apply, hα x hx, map_zero]

include hc in
/-- A polynomial over a stage of a filtered colimit of rings which vanishes over the colimit
vanishes over a later stage. -/
lemma exists_map_map_eq_zero {σ : Type*} {j : J} (p : MvPolynomial σ (F.obj j))
    (hp : MvPolynomial.map (c.ι.app j).hom p = 0) :
    ∃ (k : J) (α : j ⟶ k), MvPolynomial.map (F.map α).hom p = 0 := by
  classical
  obtain ⟨k, α, hα⟩ := exists_map_eq_zero_of_finset F c hc p.coeffs (fun x hx ↦ by
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hx
    have := congrArg (MvPolynomial.coeff m) hp
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this)
  refine ⟨k, α, MvPolynomial.ext _ _ fun m ↦ ?_⟩
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
  by_cases hm : MvPolynomial.coeff m p = 0
  · rw [hm, map_zero]
  · exact hα _ (MvPolynomial.coeff_mem_coeffs m hm)

/-- The matrix of partial derivatives `∂vₖ/∂X_{m i}` of a family of polynomials `v`. -/
noncomputable abbrev jacobiMatrixOf {A : Type*} [CommRing A] {ι σ : Type*} (m : σ → ι)
    (v : σ → MvPolynomial ι A) : Matrix σ σ (MvPolynomial ι A) :=
  Matrix.of fun i k ↦ MvPolynomial.pderiv (m i) (v k)

lemma map_det_jacobiMatrixOf {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {ι σ : Type*} [Fintype σ] [DecidableEq σ] (m : σ → ι) (v : σ → MvPolynomial ι A) :
    MvPolynomial.map φ (jacobiMatrixOf m v).det =
      (jacobiMatrixOf m fun k ↦ MvPolynomial.map φ (v k)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i k
  simp [MvPolynomial.pderiv_map]

include hc in
/-- **Étale algebras descend along filtered colimits of rings.** If `S` is an étale algebra
over the colimit `c.pt` of a filtered diagram `F` of commutative rings, then `S` is the base
change of an étale algebra `T` over one of the `F.obj j`.
(blueprint: part of `lem-weil-pbc-etale-finite-data-descent`) -/
theorem exists_isPushout_of_etale {S : CommRingCat.{u}} (f : c.pt ⟶ S) (hf : f.hom.Etale) :
    ∃ (j : J) (T : CommRingCat.{u}) (g : F.obj j ⟶ T) (_ : g.hom.Etale) (h : T ⟶ S),
      IsPushout (c.ι.app j) g f h := by
  classical
  algebraize [f.hom]
  obtain ⟨ι, σ, _, _, P₀, hP₀⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 ‹_›).out
  have : Fintype σ := Fintype.ofFinite σ
  let P := P₀.reindex (Finite.equivFin ι).symm (Equiv.refl σ)
  have hP : P.dimension = 0 := by
    rw [← hP₀]
    exact Algebra.Presentation.dimension_reindex _ _ _
  -- an inverse of the Jacobian modulo the relations
  obtain ⟨u, hu⟩ := P.jacobian_isUnit.exists_right_inv
  obtain ⟨g, rfl⟩ := P.algebraMap_surjective u
  have hJ : P.jacobiMatrix.det * g - 1 ∈ P.ker := by
    rw [Algebra.Generators.ker, RingHom.mem_ker, map_sub, map_mul, map_one]
    erw [← P.jacobian_eq_jacobiMatrix_det]
    erw [hu]
    rw [sub_self]
  rw [← P.span_range_relation_eq_ker] at hJ
  obtain ⟨d, hd⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hJ
  have hjac : P.jacobiMatrix = jacobiMatrixOf P.map P.relation := by
    exact Matrix.ext fun i k ↦ P.jacobiMatrix_apply i k
  -- lift everything to a common stage
  obtain ⟨j, hj⟩ := exists_forall_mem_range_map_ι_app F c hc
    (Finset.univ.image P.relation ∪ {g} ∪ Finset.univ.image d)
  choose v hv using fun k ↦ hj (P.relation k) (by simp)
  choose e he using fun k ↦ hj (d k) (by simp)
  obtain ⟨g₀, hg₀⟩ := hj g (by simp)
  obtain ⟨k, α, hα⟩ := exists_map_map_eq_zero F c hc
    ((jacobiMatrixOf P.map v).det * g₀ - 1 - ∑ i, e i * v i) (by
      rw [map_sub, map_sub, map_mul, map_one, map_det_jacobiMatrixOf, map_sum]
      simp only [map_mul, hv, he, hg₀, hd]
      rw [hjac]
      exact sub_self _)
  have hw : ∀ p : MvPolynomial (Fin (Nat.card ι)) (F.obj j), MvPolynomial.map (c.ι.app k).hom
      (MvPolynomial.map (F.map α).hom p) = MvPolynomial.map (c.ι.app j).hom p := fun p ↦ by
    rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, c.w α]; rfl
  let v' : σ → MvPolynomial (Fin (Nat.card ι)) (F.obj k) :=
    fun i ↦ MvPolynomial.map (F.map α).hom (v i)
  have hv' (i : σ) : MvPolynomial.map (c.ι.app k).hom (v' i) = P.relation i := by
    rw [hw, hv]
  have heq : (jacobiMatrixOf P.map v').det * MvPolynomial.map (F.map α).hom g₀ - 1 =
      ∑ i, MvPolynomial.map (F.map α).hom (e i) * v' i := by
    rw [← sub_eq_zero, ← hα, map_sub, map_sub, map_mul, map_one, map_det_jacobiMatrixOf,
      map_sum]
    simp only [map_mul, v']
  -- the descended algebra
  let T := MvPolynomial (Fin (Nat.card ι)) (F.obj k) ⧸ Ideal.span (Set.range v')
  let Q₀ : Algebra.Presentation (F.obj k) T (Fin (Nat.card ι)) σ :=
    Algebra.Presentation.naive (v := v')
  let Q : Algebra.PreSubmersivePresentation (F.obj k) T (Fin (Nat.card ι)) σ :=
    { toPresentation := Q₀
      map := P.map
      map_inj := P.map_inj }
  have hQjac : Q.jacobiMatrix = jacobiMatrixOf P.map v' := by
    exact Matrix.ext fun i k ↦ Q.jacobiMatrix_apply i k
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_iff_exists_inv.2
      ⟨algebraMap Q.Ring T (MvPolynomial.map (F.map α).hom g₀), ?_⟩
    rw [Q.jacobian_eq_jacobiMatrix_det, ← map_mul, ← sub_eq_zero,
      ← map_one (algebraMap Q.Ring T), ← map_sub, hQjac, heq]
    change Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  let Qs : Algebra.SubmersivePresentation (F.obj k) T (Fin (Nat.card ι)) σ :=
    { Q with jacobian_isUnit := hunit }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (F.obj k) T :=
    Qs.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  have hT : Algebra.Etale (F.obj k) T :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.2 this
  -- the pushout square
  obtain ⟨h, hpush⟩ := exists_isPushout_quotient_span (R := c.pt) (S := S) (c.ι.app k) v'
    (ofHom (algebraMap P.Ring S)) P.algebraMap_surjective (by
      change P.ker = _
      rw [← P.span_range_relation_eq_ker]
      congr 1
      ext p
      simp only [Set.mem_range]
      exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, (hv' y).trans hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, (hv' y).symm.trans hy⟩⟩)
  have hf : ofHom MvPolynomial.C ≫ ofHom (algebraMap P.Ring S) = f := by
    ext x
    exact (IsScalarTower.algebraMap_apply c.pt P.Ring S x).symm
  rw [hf] at hpush
  exact ⟨k, of T, _, (RingHom.etale_algebraMap (R := F.obj k)).2 hT, h, hpush⟩

end CommRingCat

namespace AlgebraicGeometry

section AffineDescent

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **Étale affine schemes descend to a finite stage.**

Let `{Dᵢ}` be a cofiltered inverse system of affine schemes with affine transition maps and
let `X` be an affine scheme which is étale over `lim Dᵢ`. Then `X` is the base change of an
affine scheme `Y` which is étale over some `Dᵢ`.
(blueprint: part of `lem-weil-pbc-etale-finite-data-descent`) -/
lemma Scheme.exists_isPullback_of_etale_of_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [Etale g] :
    ∃ (i : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj i)
      (_ : Etale p) (h : X ⟶ Y), IsPullback h g p (c.π.app i) := by
  have hcpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  -- Reduce to the case where `X` is the spectrum of a ring.
  wlog hX : ∃ A, X = Spec A generalizing X
  · obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (X := Spec Γ(X, ⊤)) (X.isoSpec.inv ≫ g) ⟨_, rfl⟩
    refine ⟨i, Y, hYaff, p, hp, X.isoSpec.hom ≫ h, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := X.isoSpec.hom) (snd := g)
      (f := X.isoSpec.inv ≫ g) (g := 𝟙 c.pt) ⟨by simp⟩).paste_horiz hsq
  obtain ⟨A, rfl⟩ := hX
  -- Reduce to the case where the diagram is the spectrum of a diagram of rings.
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := IsAffine.affine
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    have inst : ∀ {i j : I} (f : i ⟶ j),
        IsAffineHom ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map f) := fun f ↦ inferInstance
    have hg : @Etale (Spec A)
        ((Cone.postcompose (asIso e).hom).obj c).pt g := ‹_›
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      hcpt g ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    have : Etale (p ≫ inv (e.app i)) := by
      have := hp; infer_instance
    refine ⟨i, Y, hYaff, p ≫ inv (e.app i), this, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (e.app i)).symm
      (by simp) (Category.comp_id g) (by simp) ?_
    change (c.π.app i ≫ e.app i) ≫ inv (e.app i) = 𝟙 _ ≫ c.π.app i
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (c.π.app i)).symm
  obtain ⟨D, rfl⟩ := hD
  -- Reduce to the case where the limit cone is the spectrum of a colimit cocone of rings.
  wlog hc' : ∃ c' : Cocone D.leftOp, c = Scheme.Spec.mapCone (coneOfCoconeLeftOp c')
    generalizing c
  · let β : c.pt ≅ Spec Γ(c.pt, ⊤) := c.pt.isoSpec
    let φ : ∀ i : Iᵒᵖ, D.leftOp.obj i ⟶ Γ(c.pt, ⊤) :=
      fun i ↦ (Scheme.Spec.preimage (β.inv ≫ c.π.app i.unop)).unop
    have hφ : ∀ i : Iᵒᵖ, Spec.map (φ i) = β.inv ≫ c.π.app i.unop :=
      fun i ↦ Scheme.Spec.map_preimage _
    let c' : Cocone D.leftOp :=
      { pt := Γ(c.pt, ⊤)
        ι :=
        { app := φ
          naturality i j f := by
            apply Quiver.Hom.op_inj
            apply Scheme.Spec.map_injective
            change Spec.map (D.leftOp.map f ≫ φ j) = Spec.map (φ i ≫ 𝟙 _)
            rw [Spec.map_comp, Spec.map_comp, hφ, hφ, Spec.map_id, Category.id_comp]
            exact (Category.assoc _ _ _).trans (congrArg (β.inv ≫ ·) (c.w f.unop)) } }
    have hcc : c ≅ Scheme.Spec.mapCone (coneOfCoconeLeftOp c') :=
      Cone.ext β fun i ↦ by
        change c.π.app i = β.hom ≫ Spec.map (φ (Opposite.op i))
        rw [hφ]
        exact (Iso.hom_inv_id_assoc β (c.π.app i)).symm
    obtain ⟨i, Y, hYaff, p, hp, h, hsq⟩ := this (Scheme.Spec.mapCone (coneOfCoconeLeftOp c'))
      (IsLimit.ofIsoLimit hc hcc) (inferInstanceAs (IsAffine (Spec Γ(c.pt, ⊤))))
      (g ≫ β.hom) ⟨c', rfl⟩
    refine ⟨i, Y, hYaff, p, hp, h, ?_⟩
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) β.symm (Iso.refl _) (by simp) (by simp)
      (by simp) ?_
    change Spec.map (φ (Opposite.op i)) ≫ 𝟙 _ = β.inv ≫ c.π.app i
    rw [Category.comp_id]
    exact hφ (Opposite.op i)
  obtain ⟨c', rfl⟩ := hc'
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  replace hc := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects Scheme.Spec hc)
  obtain ⟨i, T, γ, hγ, h, hpush⟩ := CommRingCat.exists_isPushout_of_etale
    D.leftOp c' hc ψ (HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map ψ)›)
  refine ⟨i.unop, Spec T, inferInstance, Spec.map γ, HasRingHomProperty.Spec_iff.mpr hγ,
    Spec.map h, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

include hc in
/-- **Étale affine schemes over an affine open of the limit descend to a finite stage.**
Let `{Dᵢ}` be a cofiltered inverse system of quasi-separated schemes with affine transition
maps, and let `X` be an affine scheme which is étale over `lim Dᵢ`, with image in an affine open
`N` of `lim Dᵢ`. Then `X` is the base change of an affine scheme `Y` which is étale over some
`Dᵢ`. (blueprint: part of `lem-weil-pbc-etale-finite-data-descent`) -/
lemma Scheme.exists_isPullback_of_etale_of_isAffineOpen [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt) [Etale g] {N : c.pt.Opens}
    (hN : IsAffineOpen N) (hgN : Set.range g ⊆ (N : Set c.pt)) :
    ∃ (i : I) (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ D.obj i) (_ : Etale p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  obtain ⟨i, O, hO, hON⟩ := exists_isAffineOpen_preimage_eq D c hc N hN
  subst hON
  have (j : Over i) : IsAffine ((opensDiagram D i O).obj j) := hO.preimage (D.map _)
  let g' : X ⟶ (c.π.app i ⁻¹ᵁ O).toScheme :=
    IsOpenImmersion.lift (c.π.app i ⁻¹ᵁ O).ι g (by simpa using hgN)
  have hg' : g' ≫ (c.π.app i ⁻¹ᵁ O).ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale g' := by
    have : Etale (g' ≫ (c.π.app i ⁻¹ᵁ O).ι) := hg' ▸ inferInstance
    exact Etale.of_comp g' (c.π.app i ⁻¹ᵁ O).ι
  obtain ⟨k, Y, hY, p, hp, h, H⟩ := Scheme.exists_isPullback_of_etale_of_isAffine
    (opensDiagram D i O) (opensCone D c i O) (isLimitOpensCone D c hc i O) g'
  refine ⟨k.left, Y, hY, p ≫ (D.map k.hom ⁻¹ᵁ O).ι, inferInstance, h, ?_⟩
  have H₂ : IsPullback ((opensCone D c i O).π.app k) (c.π.app i ⁻¹ᵁ O).ι
      (D.map k.hom ⁻¹ᵁ O).ι (c.π.app k.left) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [← Scheme.Hom.comp_preimage])
  simpa [hg'] using H.paste_vert H₂

end AffineDescent

section MorphismDescent

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **Morphisms to a scheme locally of finite presentation descend along a cartesian model.**
Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes over `R` with
affine transition maps, let `X = Y ×_{Dᵢ} lim Dⱼ` for a quasi-compact quasi-separated
`Y ⟶ Dᵢ`, and let `φ : X ⟶ U` be a morphism over `R` to a scheme `U` locally of finite
presentation over `R`. Then `φ` factors through `Y ×_{Dᵢ} Dₖ` for some `k ⟶ i`.
(blueprint: part of `lem-weil-pbc-etale-finite-data-descent`) -/
lemma Scheme.exists_isPullbackLift_comp_eq [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {R : Scheme.{u}} (π : D ⟶ (Functor.const I).obj R)
    {i : I} {X Y : Scheme.{u}} {g : X ⟶ c.pt} {p : Y ⟶ D.obj i} {h : X ⟶ Y}
    [CompactSpace Y] [QuasiSeparatedSpace Y] (H : IsPullback h g p (c.π.app i))
    {U : Scheme.{u}} (q : U ⟶ R) [LocallyOfFinitePresentation q] (φ : X ⟶ U)
    (hφ : φ ≫ q = g ≫ c.π.app i ≫ π.app i) :
    ∃ (k : I) (f : k ⟶ i) (ψ : pullback p (D.map f) ⟶ U),
      ψ ≫ q = pullback.snd p (D.map f) ≫ π.app k ∧ isPullbackLift D c f H ≫ ψ = φ := by
  let t : baseChangeDiagram D p ⟶ (Functor.const (Over i)).obj R :=
    { app j := pullback.snd p (D.map j.hom) ≫ π.app j.left
      naturality j k f := by
        have := π.naturality f.left
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        simp [this] }
  obtain ⟨j, ψ, hψ₁, hψ₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D p) t q (baseChangeCone D c p) (isLimitBaseChangeCone D c p hc)
    (H.isoPullback.inv ≫ φ) (by
      ext j
      have h₁ := π.naturality j.hom
      have h₂ := c.w j.hom
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h₁
      change (baseChangeCone D c p).π.app j ≫ pullback.snd p (D.map j.hom) ≫ π.app j.left =
        (H.isoPullback.inv ≫ φ) ≫ q
      rw [baseChangeCone_π_app_snd_assoc, ← h₁, reassoc_of% h₂, Category.assoc, hφ,
        H.isoPullback_inv_snd_assoc])
  refine ⟨j.left, j.hom, ψ, hψ₂, ?_⟩
  have e : isPullbackLift D c j.hom H = H.isoPullback.hom ≫ (baseChangeCone D c p).π.app j := by
    apply pullback.hom_ext <;> simp
  rw [e, Category.assoc, hψ₁, Iso.hom_inv_id_assoc]

end MorphismDescent

section BaseChangeOver

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) {R : Scheme.{u}}
  (π : D ⟶ (Functor.const I).obj R) (c : Cone D) (P : c.pt ⟶ R)
  (hP : ∀ i, P = c.π.app i ≫ π.app i) {W : Scheme.{u}} (w : W ⟶ R)

/-- The base change `{W ×_R Dᵢ}` of a diagram `{Dᵢ}` of schemes over `R` along `w : W ⟶ R`. -/
@[simps] noncomputable def baseChangeOverDiagram : I ⥤ Scheme.{u} where
  obj i := pullback w (π.app i)
  map {i j} f := pullback.map w (π.app i) w (π.app j) (𝟙 W) (D.map f) (𝟙 R) (by simp)
    (by simp)
  map_id i := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

/-- The cone with point `W ×_R lim Dᵢ` over the base change `{W ×_R Dᵢ}`. -/
@[simps] noncomputable def baseChangeOverCone : Cone (baseChangeOverDiagram D π w) where
  pt := pullback w P
  π.app i := pullback.map w P w (π.app i) (𝟙 W) (c.π.app i) (𝟙 R) (by simp) (by simp [hP i])
  π.naturality {i j} f := by apply pullback.hom_ext <;> simp

/-- The projection `{W ×_R Dᵢ} ⟶ {Dᵢ}`. -/
@[simps] noncomputable def baseChangeOverDiagramπ : baseChangeOverDiagram D π w ⟶ D where
  app i := pullback.snd w (π.app i)

lemma isPullback_baseChangeOverCone_π (i : I) :
    IsPullback ((baseChangeOverCone D π c P hP w).π.app i) (pullback.snd w P)
      (pullback.snd w (π.app i)) (c.π.app i) :=
  isPullback_pullback_map w P (π.app i) (c.π.app i) (hP i).symm

lemma isPullback_baseChangeOverDiagram_map {i j : I} (f : i ⟶ j) :
    IsPullback ((baseChangeOverDiagram D π w).map f) (pullback.snd w (π.app i))
      (pullback.snd w (π.app j)) (D.map f) :=
  isPullback_pullback_map w (π.app i) (π.app j) (D.map f) (by simp)

/-- **Base change of a cofiltered limit over `R`.** If `lim Dᵢ` is a cofiltered limit of schemes
over `R`, then `W ×_R lim Dᵢ` is the limit of the `W ×_R Dᵢ`. -/
noncomputable def isLimitBaseChangeOverCone [IsCofiltered I] (hc : IsLimit c) :
    IsLimit (baseChangeOverCone D π c P hP w) :=
  have := IsCofiltered.isConnected I
  isLimitOfIsPullbackOfIsConnected (baseChangeOverDiagramπ D π w) _ c
    { hom := pullback.snd w P
      w := fun i ↦ by simp }
    (isPullback_baseChangeOverCone_π D π c P hP w) hc

instance [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i j : I} (f : i ⟶ j) :
    IsAffineHom ((baseChangeOverDiagram D π w).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseChangeOverDiagram_map D π w f).flip inferInstance

instance [QuasiCompact w] [∀ i, CompactSpace (D.obj i)] (i : I) :
    CompactSpace ((baseChangeOverDiagram D π w).obj i) :=
  inferInstanceAs (CompactSpace ↥(pullback w (π.app i)))

instance [QuasiSeparated w] [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) :
    QuasiSeparatedSpace ((baseChangeOverDiagram D π w).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd w (π.app i))

end BaseChangeOver

end AlgebraicGeometry
