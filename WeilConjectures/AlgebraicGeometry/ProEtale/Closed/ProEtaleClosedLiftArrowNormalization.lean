/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftArrowComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.ClopenPartition
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Normalizing the closed-lift augmentation to actual arrows

Source: Steps 1--2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: lem-sp-proetale-closed-lift-arrow-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A clopen subscheme of a closed-lift test is a closed-lift test.

Proof: it is affine as a closed subscheme of an affine scheme; evaluation on it preserves
epimorphisms by `ProEt.surjective_app_ofOpenImmersion_of_isClosed`; and a specialization of one
of its points into the closed fibre stays inside it because it is closed. -/
theorem ClosedLiftTest.ofOpenImmersion {X Z : Scheme.{u}} {z : Z ⟶ X} {U : X.ProEt}
    (hU : ClosedLiftTest z U) (O : U.left.Opens) (hO : IsClosed (O : Set U.left)) :
    ClosedLiftTest z (ProEt.ofOpenImmersion U O.ι) := by
  obtain ⟨hA, hW, hsp⟩ := hU
  have : IsClosedImmersion O.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa only [Opens.range_ι] using hO)
  have : IsAffine O.toScheme := isAffine_of_isAffineHom O.ι
  refine ⟨‹IsAffine O.toScheme›,
    ProEt.surjective_app_ofOpenImmersion_of_isClosed.{u, u + 1, u + 1} U hW O hO, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := hsp (O.ι x)
  have hmem : pullback.fst U.hom z y ∈ O := by
    have := hy.mem_closed hO
    simpa using this
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := O.ι ≫ U.hom) (g := z) (⟨_, hmem⟩ : O.toScheme) (pullback.snd U.hom z y) (by
      change U.hom (O.ι ⟨_, hmem⟩) = _
      simp only [Opens.ι_apply]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (by rw [pullback.condition]; rfl))
  refine ⟨w, ?_⟩
  change Specializes x (pullback.fst (O.ι ≫ U.hom) z w)
  rw [hw₁]
  exact (O.isOpenEmbedding.toIsInducing.specializes_iff).1 (by simpa using hy)

private theorem freeSheafHomEquiv_map (A : Type u) [CommRing A]
    {X : Scheme.{u}} {V U : X.ProEt} (a : V ⟶ U)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (r : (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj U ⟶ M) :
    ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) V M
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).map a ≫ r) =
      M.obj.map a.op (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) U M r) := by
  simp only [ProEtale.freeSheafHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

/-- The section of `A[P]` over `P` corresponding to the identity is the image of the basis
vector of the identity arrow under sheafification. -/
private theorem freeSheafHomEquiv_id (A : Type u) [CommRing A] {X : Scheme.{u}} (P : X.ProEt) :
    ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) P
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P) (𝟙 _) =
      (toSheafify (ProEt.topology X)
        (uliftYoneda.{u + 1}.obj P ⋙ ModuleCat.free (ULift.{u + 1, u} A))).app (op P)
        (ModuleCat.freeMk (ULift.up (𝟙 P))) := by
  simp only [ProEtale.freeSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_unit]
  erw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id, Category.comp_id,
    sheafificationAdjunction_unit_app]
  rfl

/-- The free arrow `A[v]` corresponds to the sheafified basis vector of `v`. -/
private theorem freeSheafHomEquiv_freeSheaf_map (A : Type u) [CommRing A] {X : Scheme.{u}}
    {W P : X.ProEt} (v : W ⟶ P) :
    ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) W
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).map v) =
      (toSheafify (ProEt.topology X)
        (uliftYoneda.{u + 1}.obj P ⋙ ModuleCat.free (ULift.{u + 1, u} A))).app (op W)
        (ModuleCat.freeMk (ULift.up v)) := by
  rw [← Category.comp_id ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).map v),
    freeSheafHomEquiv_map, freeSheafHomEquiv_id]
  have h := ConcreteCategory.congr_hom ((toSheafify (ProEt.topology X)
      (uliftYoneda.{u + 1}.obj P ⋙ ModuleCat.free (ULift.{u + 1, u} A))).naturality v.op)
    (ModuleCat.freeMk (ULift.up (𝟙 P)))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  refine h.symm.trans (congrArg _ ?_)
  change (ModuleCat.free _).map ((uliftYoneda.{u + 1}.obj P).map v.op) _ = _
  rw [ModuleCat.free_map_apply]
  congr 1

/-- Test relations and actual-arrow summands generate the full augmentation source.
This assertion concerns the source of the augmentation, not its relation kernel;
it does not identify the relations among the actual arrows.

Source: Steps 1--2 of `lem-sp-proetale-closed-lift-kernel-overlap-presentation`.
(blueprint: lem-sp-proetale-closed-lift-arrow-normalization).

Proof: it suffices that every map φ out of the full source killing the image is zero.
Fix a summand A[U] of the full source, given by a test U and a map f from A[U] to A[P].
By local surjectivity of the sheafification of the free presheaf, f is locally a finite
linear combination of actual arrows. Since evaluation at U preserves epimorphisms, the
covering sieve on which this holds contains a finite clopen partition of U
(`ProEt.exists_clopen_partition`). Each piece W is again a test
(`ClosedLiftTest.ofOpenImmersion`). On W, the restriction of the summand minus the
corresponding combination of actual-arrow summands lies in the kernel of the augmentation,
hence is a summand of the test relations, so φ kills it; φ also kills the actual-arrow
summands. Hence φ vanishes on the summand after restriction to every piece of the partition,
and therefore on the summand, by free Yoneda and separatedness. -/
theorem closedLiftArrow_normalization (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt) :
    let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P
    let e := closedLiftGeneratorAugmentation A z Q
    let d := closedLiftGeneratorAugmentation A z (kernel e.hom)
    Epi (biprod.desc (d.hom ≫ kernel.ι e.hom) (closedLiftArrowAugmentation A z P)) := by
  intro Q e d
  classical
  let Λ := ULift.{u + 1, u} A
  let F := ProEtale.freeSheaf Λ X
  let J := ProEt.topology X
  let Fpre : X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ := uliftYoneda.{u + 1}.obj P ⋙ ModuleCat.free Λ
  refine Preadditive.epi_of_cancel_zero _ fun {M} φ hφ ↦ ?_
  -- `φ` kills every map from a test into the kernel of the augmentation.
  have hker (U : X.ProEt) (hU : ClosedLiftTest z U) (x : F.obj U ⟶ e.left)
      (hx : x ≫ e.hom = 0) : x ≫ φ = 0 := by
    have h := biprod.inl ≫= hφ
    rw [biprod.inl_desc_assoc, comp_zero] at h
    let ι := Sigma.ι (fun s : {t : Σ V : X.ProEt, F.obj V ⟶ kernel e.hom //
        ClosedLiftTest z t.1} ↦ F.obj s.val.1) ⟨⟨U, kernel.lift e.hom x hx⟩, hU⟩
    have hd : ι ≫ d.hom = kernel.lift e.hom x hx := Sigma.ι_desc _ _
    have hd' : ι ≫ d.hom ≫ kernel.ι e.hom = x := by
      rw [← Category.assoc, hd]
      exact kernel.lift_ι _ _ _
    rw [← hd']
    simpa only [Category.assoc, comp_zero] using ι ≫= h
  -- `φ` kills every actual-arrow summand.
  have harrow (t : ClosedLiftArrowIndex z P) : closedLiftArrowι A z P t ≫ φ = 0 := by
    have h := biprod.inr ≫= hφ
    rw [biprod.inr_desc_assoc, comp_zero] at h
    have hb : Sigma.ι (fun t : ClosedLiftArrowIndex z P ↦ F.obj t.val.1) t ≫
        closedLiftArrowAugmentation A z P = closedLiftArrowι A z P t := Sigma.ι_desc _ _
    rw [← hb]
    simpa only [Category.assoc, comp_zero] using
      Sigma.ι (fun t : ClosedLiftArrowIndex z P ↦ F.obj t.val.1) t ≫= h
  have hzero (W : X.ProEt) : ProEtale.freeSheafHomEquiv Λ W M 0 = 0 := by
    rw [← Category.id_comp (0 : F.obj W ⟶ M), ProEtale.freeSheafHomEquiv_comp]
    rfl
  refine Sigma.hom_ext (f := fun s : {t : Σ V : X.ProEt, F.obj V ⟶ Q //
    ClosedLiftTest z t.1} ↦ F.obj s.val.1) φ 0 ?_
  rintro ⟨⟨U, f⟩, hU⟩
  rw [comp_zero]
  let ιs := Sigma.ι (fun s : {t : Σ V : X.ProEt, F.obj V ⟶ Q //
    ClosedLiftTest z t.1} ↦ F.obj s.val.1) ⟨⟨U, f⟩, hU⟩
  have hιs : ιs ≫ e.hom = f := Sigma.ι_desc _ _
  let x := ProEtale.freeSheafHomEquiv Λ U Q f
  have : Presheaf.IsLocallySurjective J (toSheafify J Fpre) :=
    Presheaf.isLocallySurjective_toSheafify' J _
  have hS := Presheaf.imageSieve_mem J (toSheafify J Fpre) x
  have : IsAffine U.left := hU.1
  obtain ⟨n, O, hcl, -, htop, hmem⟩ := ProEt.exists_clopen_partition.{u, u + 1} U hU.2.1 _ hS
  -- On each piece of the partition, `φ` kills the restricted summand.
  have hpiece (i : Fin n) :
      F.map (ProEt.ofOpenImmersionHom U (O i).ι) ≫ ιs ≫ φ = 0 := by
    let W := ProEt.ofOpenImmersion U (O i).ι
    let w := ProEt.ofOpenImmersionHom U (O i).ι
    have hW : ClosedLiftTest z W := hU.ofOpenImmersion (O i) (hcl i)
    have hsec (y' : Fpre.obj (op W)) : ∃ σ : e.left.obj.obj (op W),
        e.hom.hom.app (op W) σ = (toSheafify J Fpre).app (op W) y' ∧
          φ.hom.app (op W) σ = 0 := by
      induction y' using Finsupp.induction_linear with
      | zero => exact ⟨0, by simp, by simp⟩
      | add y₁ y₂ h₁ h₂ =>
        obtain ⟨σ₁, h₁, h₁'⟩ := h₁
        obtain ⟨σ₂, h₂, h₂'⟩ := h₂
        exact ⟨σ₁ + σ₂, by simp [h₁, h₂], by simp [h₁', h₂']⟩
      | single a c =>
        refine ⟨c • ProEtale.freeSheafHomEquiv Λ W e.left
          (closedLiftArrowι A z P ⟨⟨W, a.down⟩, hW⟩), ?_, ?_⟩
        · rw [map_smul, ← ProEtale.freeSheafHomEquiv_comp, closedLiftArrowι_augmentation]
          change c • ProEtale.freeSheafHomEquiv Λ W Q (F.map a.down) = _
          rw [freeSheafHomEquiv_freeSheaf_map]
          refine (map_smul (ConcreteCategory.hom ((toSheafify J Fpre).app (op W))) c
            _).symm.trans ?_
          exact congrArg _ (Finsupp.smul_single_one a c)
        · rw [map_smul, ← ProEtale.freeSheafHomEquiv_comp, harrow, hzero, smul_zero]
    obtain ⟨y, hy⟩ := hmem i
    obtain ⟨σ, hσ, hσ'⟩ := hsec y
    let h' := (ProEtale.freeSheafHomEquiv Λ W e.left).symm σ
    have h₁ : F.map w ≫ f = h' ≫ e.hom := by
      apply (ProEtale.freeSheafHomEquiv Λ W Q).injective
      rw [freeSheafHomEquiv_map, ProEtale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply]
      exact (hσ.trans hy).symm
    have h₂ : h' ≫ φ = 0 := by
      apply (ProEtale.freeSheafHomEquiv Λ W M).injective
      rw [ProEtale.freeSheafHomEquiv_comp, Equiv.apply_symm_apply, hσ', hzero]
    have h₃ := hker W hW ((F.map w ≫ ιs : F.obj W ⟶ e.left) - h') (by
      rw [Preadditive.sub_comp, Category.assoc, hιs, h₁, sub_self])
    rw [Preadditive.sub_comp, h₂, sub_zero, Category.assoc] at h₃
    exact h₃
  -- The pieces cover `U`, so the summand is killed by separatedness.
  apply (ProEtale.freeSheafHomEquiv Λ U M).injective
  let M' := (sheafCompose J (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj M
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp M'.property
  have hcov : Sieve.ofArrows _ (fun i : ULift.{u} (Fin n) ↦
      ProEt.ofOpenImmersionHom U (O i.down).ι) ∈ J U := by
    apply ProEt.mem_topology_of_openImmersion _ (fun i : ULift.{u} (Fin n) ↦ (O i.down).ι) _
      (fun i ↦ Sieve.ofArrows_mk _ _ i)
    intro y
    have hy : y ∈ iSup O := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨⟨i⟩, (Opens.range_ι (O i)).symm ▸ hi⟩
  apply (hsh _ hcov).isSeparatedFor.ext
  rintro Y g ⟨_, h, _, ⟨i⟩, rfl⟩
  change M.obj.map (h ≫ _).op (ProEtale.freeSheafHomEquiv Λ U M (ιs ≫ φ)) =
    M.obj.map (h ≫ _).op (ProEtale.freeSheafHomEquiv Λ U M 0)
  rw [← freeSheafHomEquiv_map, ← freeSheafHomEquiv_map, comp_zero, Functor.map_comp,
    Category.assoc, hpiece i.down, comp_zero]

end AlgebraicGeometry.Scheme
