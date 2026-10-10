/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableRetract

/-!
# Local pure-tensor decompositions of maps into tensor products of complexes

Let `X` be a scheme, `Λ` a commutative ring and `L`, `F` cochain complexes of pro-étale sheaves
of `Λ`-modules. This file provides the local input to Stacks, Tag 0FPV (dualizable complexes are
locally retracts of finite complexes) on the pro-étale site: the global-section statement
`AlgebraicGeometry.ProEtale.exists_comp_Q_map_generatedSubcomplexι_eq` requires the
coevaluation to be represented by a cocycle of `L ⊗ F` which is a finite sum of pure tensors
of sections, and this only holds locally.

## Main definitions

- `AlgebraicGeometry.ProEtale.pureTensorSpan`: the sections of `(L ⊗ F)ⁿ` over `V` spanned by
  pure tensors `xᵖ ⊗ y^q` of sections over `V`.
- `AlgebraicGeometry.ProEtale.pureTensorSieve`: the sieve along which a section restricts into
  `pureTensorSpan`.

## Main statements

- `AlgebraicGeometry.ProEtale.pureTensorSieve_mem`: every section of `(L ⊗ F)ⁿ` is locally a
  finite sum of pure tensors.
- `AlgebraicGeometry.ProEtale.exists_sieve_sum_tensorSectionMap_of_Q_map`: a morphism
  `Q(Λ[0]) ⟶ Q(L ⊗ F)` of the derived category is `Q(φ) ≫ Q(s)⁻¹` for a quasi-isomorphism
  `s : L ⊗ F ⟶ I`, where locally the cocycle of `φ` is cohomologous to the image under `s` of a
  cocycle of `L ⊗ F` which is a finite sum of pure tensors.
- `AlgebraicGeometry.ProEtale.Q_map_eq_of_singleUnitHomEquiv_eq_add`: chain maps out of `Λ[0]`
  with cohomologous cocycles agree in the derived category.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme Sheaf

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  (L F : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)

/-- Naturality of a morphism of pro-étale sheaves of modules, on sections. -/
lemma Sheaf.hom_app_map_apply {G H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (φ : G ⟶ H) {U V : X.ProEt} (f : V ⟶ U) (x : G.obj.obj (op U)) :
    φ.hom.app (op V) (G.obj.map f.op x) = H.obj.map f.op (φ.hom.app (op U) x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality f.op) x

/-- The submodule of sections over `V` of the degree `n` term of `L ⊗ F` spanned by the pure
tensors `xᵖ ⊗ y^q` of sections over `V`, with `p + q = n`. -/
noncomputable def pureTensorSpan (n : ℤ) (V : X.ProEt) :
    Submodule Λ (((L ⊗ F).X n).obj.obj (op V)) :=
  Submodule.span Λ {s | ∃ (p q : ℤ) (h : p + q = n) (x : (L.X p).obj.obj (op V))
    (y : (F.X q).obj.obj (op V)),
    (HomologicalComplex.ιTensorObj L F p q n h).hom.app _ (tensorSectionMap _ _ _ (x ⊗ₜ y)) = s}

variable {L F} in
/-- Restrictions of sections in `pureTensorSpan` lie in `pureTensorSpan`. -/
lemma map_mem_pureTensorSpan {n : ℤ} {U V : X.ProEt} (f : V ⟶ U)
    {s : ((L ⊗ F).X n).obj.obj (op U)} (hs : s ∈ pureTensorSpan L F n U) :
    ((L ⊗ F).X n).obj.map f.op s ∈ pureTensorSpan L F n V := by
  refine Submodule.span_induction (fun t ⟨p, q, h, x, y, ht⟩ ↦ ?_) (by simp)
    (fun a b _ _ ha hb ↦ by simpa using add_mem ha hb)
    (fun r a _ ha ↦ by simpa using Submodule.smul_mem _ r ha) hs
  subst ht
  refine Submodule.subset_span ⟨p, q, h, (L.X p).obj.map f.op x, (F.X q).obj.map f.op y, ?_⟩
  rw [← tensorSectionMap_naturality, Sheaf.hom_app_map_apply]
  rfl

variable {L F} in
/-- The sieve of the arrows `f : V ⟶ U` along which a section `s` of `(L ⊗ F)ⁿ` restricts into
`pureTensorSpan`. -/
noncomputable def pureTensorSieve {n : ℤ} {U : X.ProEt} (s : ((L ⊗ F).X n).obj.obj (op U)) :
    Sieve U where
  arrows V f := ((L ⊗ F).X n).obj.map f.op s ∈ pureTensorSpan L F n V
  downward_closed {V W} f hf g := by
    rw [op_comp, Functor.map_comp]
    exact map_mem_pureTensorSpan g hf

variable {L F} in
/-- A finite sum of sections whose `pureTensorSieve`s are covering has a covering
`pureTensorSieve`. -/
lemma sum_pureTensorSieve_mem {n : ℤ} {U : X.ProEt} {ι : Type*} (t : Finset ι)
    (s : ι → ((L ⊗ F).X n).obj.obj (op U))
    (hs : ∀ i ∈ t, pureTensorSieve (s i) ∈ Scheme.ProEt.topology X U) :
    pureTensorSieve (∑ i ∈ t, s i) ∈ Scheme.ProEt.topology X U := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine (Scheme.ProEt.topology X).superset_covering (fun V f _ ↦ ?_)
      ((Scheme.ProEt.topology X).top_mem U)
    simp [pureTensorSieve]
  | insert i t hi ih =>
    refine (Scheme.ProEt.topology X).superset_covering (fun V f hf ↦ ?_)
      ((Scheme.ProEt.topology X).intersection_covering (hs i (by simp))
        (ih fun j hj ↦ hs j (by simp [hj])))
    rw [Finset.sum_insert hi]
    simpa [pureTensorSieve] using add_mem hf.1 hf.2

variable {L F} in
/-- The image of a section of `Lᵖ ⊗ F^q` in `(L ⊗ F)ⁿ` has a covering `pureTensorSieve`. -/
lemma pureTensorSieve_ιTensorObj_mem {p q n : ℤ} (h : p + q = n) {U : X.ProEt}
    (t : (L.X p ⊗ F.X q).obj.obj (op U)) :
    pureTensorSieve ((HomologicalComplex.ιTensorObj L F p q n h).hom.app _ t) ∈
      Scheme.ProEt.topology X U := by
  obtain ⟨S, hS, hS'⟩ := exists_sieve_sum_tensorSectionMap_eq _ _ t
  refine (Scheme.ProEt.topology X).superset_covering (fun V f hf ↦ ?_) hS
  obtain ⟨m, x, y, hxy⟩ := hS' f hf
  simp only [pureTensorSieve]
  have e : ((L ⊗ F).X n).obj.map f.op ((HomologicalComplex.ιTensorObj L F p q n h).hom.app _ t) =
      (HomologicalComplex.ιTensorObj L F p q n h).hom.app _
        (∑ k, tensorSectionMap _ _ _ (x k ⊗ₜ y k)) := by
    rw [hxy]
    exact (Sheaf.hom_app_map_apply _ f t).symm
  rw [e, map_sum]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.subset_span ⟨p, q, h, x k, y k, rfl⟩

variable {L F} in
/-- **Local pure-tensor decomposition.** Every section of `(L ⊗ F)ⁿ` is, after restriction to
the members of a covering sieve, a finite linear combination of pure tensors `xᵖ ⊗ y^q`. -/
lemma pureTensorSieve_mem {n : ℤ} {U : X.ProEt} (s : ((L ⊗ F).X n).obj.obj (op U)) :
    pureTensorSieve s ∈ Scheme.ProEt.topology X U := by
  obtain ⟨S, hS, hS'⟩ := exists_sieve_sum_sigmaι_eq
    (fun i : (fun x : ℤ × ℤ ↦ x.1 + x.2) ⁻¹' {n} ↦ L.X i.1.1 ⊗ F.X i.1.2) s
  refine (Scheme.ProEt.topology X).transitive hS _ fun V f hf ↦ ?_
  obtain ⟨t, x, hx⟩ := hS' f hf
  refine (Scheme.ProEt.topology X).superset_covering (fun W g hg ↦ ?_)
    (sum_pureTensorSieve_mem t _ fun i _ ↦ pureTensorSieve_ιTensorObj_mem i.2 (x i))
  simp only [pureTensorSieve, Sieve.pullback_apply] at hg ⊢
  have hx' : ((L ⊗ F).X n).obj.map f.op s = ∑ i ∈ t,
      (HomologicalComplex.ιTensorObj L F i.1.1 i.1.2 n i.2).hom.app _ (x i) := hx.symm
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hx']
  exact hg

variable {L F} in
/-- A section in `pureTensorSpan` is a finite sum of pure tensors `xₖ ⊗ yₖ`. -/
lemma exists_sum_eq_of_mem_pureTensorSpan {n : ℤ} {V : X.ProEt}
    {s : ((L ⊗ F).X n).obj.obj (op V)} (hs : s ∈ pureTensorSpan L F n V) :
    ∃ (m : ℕ) (p q : Fin m → ℤ) (h : ∀ k, p k + q k = n)
      (x : ∀ k, (L.X (p k)).obj.obj (op V)) (y : ∀ k, (F.X (q k)).obj.obj (op V)),
      ∑ k, (HomologicalComplex.ιTensorObj L F (p k) (q k) n (h k)).hom.app _
        (tensorSectionMap _ _ _ (x k ⊗ₜ y k)) = s := by
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 hs
  choose p q h x y hg using fun k ↦ (g k).2
  refine ⟨m, p, q, h, fun k ↦ c k • x k, y, Finset.sum_congr rfl fun k _ ↦ ?_⟩
  dsimp only
  rw [← hg k, ← TensorProduct.smul_tmul', map_smul, map_smul]

variable {L F} in
/-- In degree `0`, a section in `pureTensorSpan` is a finite sum of pure tensors `xₖ ⊗ yₖ` of
sections `xₖ` of `L^{pₖ}` and `yₖ` of `F^{-pₖ}`. -/
lemma exists_sum_eq_of_mem_pureTensorSpan_zero {V : X.ProEt}
    {s : ((L ⊗ F).X 0).obj.obj (op V)} (hs : s ∈ pureTensorSpan L F 0 V) :
    ∃ (m : ℕ) (p : Fin m → ℤ) (x : ∀ k, (L.X (p k)).obj.obj (op V))
      (y : ∀ k, (F.X (-p k)).obj.obj (op V)),
      ∑ k, (HomologicalComplex.ιTensorObj L F (p k) (-p k) 0 (by simp)).hom.app _
        (tensorSectionMap _ _ _ (x k ⊗ₜ y k)) = s := by
  obtain ⟨m, p, q, h, x, y, hs⟩ := exists_sum_eq_of_mem_pureTensorSpan hs
  obtain rfl : q = fun k ↦ -p k := funext fun k ↦ by have := h k; lia
  exact ⟨m, p, x, y, hs⟩

open _root_.DerivedCategory in
/-- **Local representatives of maps from the unit into a tensor product.** A morphism
`u : Q(Λ[0]) ⟶ Q(L ⊗ F)` in the derived category is `Q(φ) ≫ Q(s)⁻¹` for a quasi-isomorphism
`s : L ⊗ F ⟶ I` and a chain map `φ : Λ[0] ⟶ I`. Locally on the pro-étale site, the cocycle of
`φ` is cohomologous to the image under `s` of a cocycle of `L ⊗ F` which is a finite sum of
pure tensors `xₖ ⊗ yₖ`. -/
theorem exists_sieve_sum_tensorSectionMap_of_Q_map
    (u : Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))) ⟶ Q.obj (L ⊗ F)) :
    ∃ (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ)
      (s : L ⊗ F ⟶ I) (_ : QuasiIso s) (φ : (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶ I),
      u = Q.map φ ≫ inv (Q.map s) ∧
      ∃ R ∈ Scheme.ProEt.topology X (terminalProEt X), ∀ ⦃V : X.ProEt⦄
        (f : V ⟶ terminalProEt X), R f → ∃ (m : ℕ) (p : Fin m → ℤ)
          (x : ∀ k, (L.X (p k)).obj.obj (op V)) (y : ∀ k, (F.X (-p k)).obj.obj (op V))
          (w : (I.X (-1)).obj.obj (op V)),
          ((L ⊗ F).d 0 1).hom.app _ (∑ k, (HomologicalComplex.ιTensorObj L F (p k) (-p k) 0
            (by simp)).hom.app _ (tensorSectionMap _ _ _ (x k ⊗ₜ y k))) = 0 ∧
          (s.f 0).hom.app _ (∑ k, (HomologicalComplex.ιTensorObj L F (p k) (-p k) 0
            (by simp)).hom.app _ (tensorSectionMap _ _ _ (x k ⊗ₜ y k))) =
            (I.X 0).obj.map f.op (singleUnitHomEquiv I φ).1 + (I.d (-1) 0).hom.app _ w := by
  obtain ⟨I, φ, s, hs, rfl⟩ := left_fac u
  have hs' : QuasiIso s := (isIso_Q_map_iff_quasiIso _ s).1 hs
  obtain ⟨R, hR, hR'⟩ := exists_sieve_lift_cocycle s (m := -1) (n := 0) (by simp)
    (singleUnitHomEquiv I φ).1 (singleUnitHomEquiv I φ).2
  choose z w hz hzw using hR'
  refine ⟨I, s, hs', φ, rfl, _, (Scheme.ProEt.topology X).bind_covering hR
    fun V f hf ↦ pureTensorSieve_mem (z f hf), fun V h ⟨W, g, f, hf, hg, hgf⟩ ↦ ?_⟩
  subst hgf
  obtain ⟨m, p, x, y, hxy⟩ := exists_sum_eq_of_mem_pureTensorSpan_zero hg
  refine ⟨m, p, x, y, (I.X (-1)).obj.map g.op (w f hf), ?_, ?_⟩
  · rw [hxy, Sheaf.hom_app_map_apply]
    simpa using congrArg (((L ⊗ F).X 1).obj.map g.op) (hz f hf)
  · rw [hxy, Sheaf.hom_app_map_apply, Sheaf.hom_app_map_apply, hzw, map_add, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]

open CochainComplex.HomComplex in
/-- Two chain maps from the unit placed in degree `0` whose cocycles over the terminal object
differ by a coboundary `d w` are homotopic, hence agree in the derived category. -/
lemma Q_map_eq_of_singleUnitHomEquiv_eq_add
    {M : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (φ₁ φ₂ : (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶ M)
    (w : (M.X (-1)).obj.obj (op (terminalProEt X)))
    (h : (singleUnitHomEquiv M φ₁).1 =
      (M.d (-1) 0).hom.app _ w + (singleUnitHomEquiv M φ₂).1) :
    _root_.DerivedCategory.Q.map φ₁ = _root_.DerivedCategory.Q.map φ₂ := by
  let z : Cochain _ M (-1) := Cochain.single
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom ≫ (unitHomEquiv _).symm w) (-1)
  refine _root_.DerivedCategory.Q_map_eq_of_homotopy _
    ((Cochain.equivHomotopy φ₁ φ₂).symm ⟨z, Cochain.ext₀ _ _ fun p ↦ ?_⟩)
  by_cases hp : p = 0
  · subst hp
    rw [Cochain.add_v, δ_v (-1) 0 (by simp) z 0 0 (by simp) (-1) 1 (by simp) (by simp),
      Cochain.single_v, HomologicalComplex.single_obj_d, zero_comp, smul_zero, add_zero,
      Cochain.ofHom_v, Cochain.ofHom_v, Category.assoc,
      ← cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv, Preadditive.comp_add,
      Iso.inv_hom_id_assoc]
    apply (unitHomEquiv _).injective
    rw [map_add, unitHomEquiv_comp _ (M.d (-1) 0), AddEquiv.apply_symm_apply]
    exact h
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

end AlgebraicGeometry.ProEtale
