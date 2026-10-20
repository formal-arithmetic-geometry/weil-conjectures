/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import WeilConjectures.Algebra.Homology.UpperTruncationStepSES
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex

/-!
# Canonical truncation filtration

Source: Stacks Project, `literature/stacks-project/homology.tex`, Tag 0118,
with Remark 08J5 (blueprint: lem-kun-canonical-truncation-filtration).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {R : Type u} [CommRing R]

private noncomputable def truncationInclusion
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : a ≤ b) :
    K.truncLE a ⟶ K.truncLE b := by
  have : (K.truncLE a).IsStrictlyLE b := isStrictlyLE_of_le _ a b hab
  exact inv ((K.truncLE a).ιTruncLE b) ≫ truncLEMap (K.ιTruncLE a) b

private lemma truncationInclusion_comp
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : a ≤ b) :
    truncationInclusion K a b hab ≫ K.ιTruncLE b = K.ιTruncLE a := by
  have : (K.truncLE a).IsStrictlyLE b := isStrictlyLE_of_le _ a b hab
  simp [truncationInclusion, Category.assoc]

private lemma truncation_eqToHom
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (h : a = b) :
    eqToHom (congrArg K.truncLE h) ≫ K.ιTruncLE b = K.ιTruncLE a := by
  subst b
  simp

private noncomputable def canonicalFiltration
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : DecreasingFiltration K where
  F p := Subobject.mk (K.ιTruncLE (-p))
  F_succ_le p := Subobject.mk_le_mk_of_comm
    (truncationInclusion K (-(p + 1)) (-p) (by omega))
    (truncationInclusion_comp K _ _ _)

private noncomputable def canonicalStepIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    ((canonicalFiltration K).step p : CochainComplex (ModuleCat.{u} R) ℤ) ≅
      K.truncLE (-p) := Subobject.underlyingIso _

private lemma canonicalStepIso_arrow
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
    (canonicalStepIso K p).hom ≫ K.ιTruncLE (-p) =
      ((canonicalFiltration K).step p).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

private noncomputable def canonicalFilteredMap
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    FilteredObject.Hom ⟨K, canonicalFiltration K⟩
      ⟨L, canonicalFiltration L⟩ where
  hom := f
  preserves p := ⟨(canonicalStepIso K p).hom ≫ truncLEMap f (-p) ≫
    (canonicalStepIso L p).inv, by
      simp [canonicalStepIso, canonicalFiltration, Category.assoc]⟩

private lemma canonicalFiltration_bounded
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) :
    ∃ (a b : ℤ), a < b ∧ (canonicalFiltration K).step a = ⊤ ∧
      (canonicalFiltration K).step b = ⊥ := by
  obtain ⟨m, n, h⟩ := hK
  let q := max m n
  have : K.IsStrictlyLE q := (isStrictlyLE_iff K q).2
    (fun r hr ↦ h r (Or.inr (lt_of_le_of_lt (le_max_right _ _) hr)))
  refine ⟨-q, -m + 1, by dsimp [q]; omega, ?_, ?_⟩
  · change Subobject.mk (K.ιTruncLE (- -q)) = ⊤
    have : K.IsStrictlyLE (- -q) := isStrictlyLE_of_le K q (- -q) (by omega)
    have : IsIso (K.ιTruncLE (- -q)) := (isIso_ιTruncLE_iff K _).2 inferInstance
    exact Subobject.mk_eq_top_of_isIso _
  · apply Subobject.mk_eq_bot_iff_zero.2
    ext r : 1
    by_cases hr : -(-m + 1) < r
    · exact ((K.truncLE _).isZero_of_isStrictlyLE _ r hr).eq_of_src _ _
    · exact (h r (Or.inl (by omega))).eq_of_tgt _ _

private lemma canonicalFiltration_homotopy
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {f g : K ⟶ L}
    (h : Homotopy f g) (p n m : ℤ) :
    ∃ lift : ((canonicalFiltration K).step p : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
      ((canonicalFiltration L).step p : CochainComplex (ModuleCat.{u} R) ℤ).X m,
      lift ≫ ((canonicalFiltration L).step p).arrow.f m =
        ((canonicalFiltration K).step p).arrow.f n ≫ h.hom n m := by
  by_cases hm : m < -p
  · have := isIso_ιTruncLE_f L (-p) m hm
    refine ⟨((canonicalStepIso K p).hom).f n ≫ (K.ιTruncLE (-p)).f n ≫
      h.hom n m ≫ inv ((L.ιTruncLE (-p)).f m) ≫ ((canonicalStepIso L p).inv).f m,
      ?_⟩
    have hi := congrArg (fun f ↦ f.f n) (canonicalStepIso_arrow K p)
    simp only [HomologicalComplex.comp_f] at hi
    have hj : ((canonicalStepIso L p).inv).f m ≫
        ((canonicalFiltration L).step p).arrow.f m = (L.ιTruncLE (-p)).f m :=
      congrArg (fun f ↦ f.f m) (Subobject.underlyingIso_arrow (L.ιTruncLE (-p)))
    simp only [Category.assoc, hj, IsIso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hi]
  · refine ⟨0, ?_⟩
    by_cases hrel : (ComplexShape.up ℤ).Rel m n
    · have hn : -p < n := by change m + 1 = n at hrel; omega
      have hz := (K.truncLE (-p)).isZero_of_isStrictlyLE (-p) n hn
      have hz' := hz.of_iso ((HomologicalComplex.eval _ _ n).mapIso
        (canonicalStepIso K p))
      exact hz'.eq_of_src _ _
    · rw [h.zero n m hrel, comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Canonical good-truncation filtration of a bounded complex, its graded pieces,
naturality, homotopies, and quasi-isomorphism invariance.

Source: Stacks Project, Homology Tag 0118 and Derived Categories Remark 08J5
(blueprint: lem-kun-canonical-truncation-filtration).

Proof steps: choose lower and upper degree bounds and use the canonical truncations;
pin the filtration steps to the canonical subobjects given by the truncation
inclusions; apply `CochainComplex.exists_upperTruncationStepSES` to identify each
quotient with the two-term image-to-kernel complex and to construct the comparison
family to shifted cohomology; use its naturality clause for chain maps; restrict a
chain homotopy degreewise to the truncations; and finally use that a quasi-isomorphism
induces an isomorphism on every cohomology object.
The filtration and filtered homotopy notions are those of
`CategoryTheory.DecreasingFiltration` and `CochainComplex.FiniteFilteredModuleHomotopy`.
-/
theorem exists_canonicalTruncationFiltration :
    ∃ (F : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      DecreasingFiltration K)
      (pi : ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ),
        (F K).gradedPiece i ⟶
          (singleFunctor (ModuleCat.{u} R) (-i)).obj (K.homology (-i))),
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (i : ℤ),
        (F K).step i = Subobject.mk (K.ιTruncLE (-i))) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
        (∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r)) →
          ∃ (a b : ℤ), a < b ∧ (F K).step a = ⊤ ∧ (F K).step b = ⊥) ∧
      (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (i : ℤ),
        ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ)
          (e : (F K).gradedPiece i ≅ M)
          (e₀ : M.X (-i - 1) ≅ cokernel (kernel.ι (K.d (-i - 1) (-i))))
          (e₁ : M.X (-i) ≅ K.cycles (-i)),
          (∀ (r : ℤ), r ≠ -i - 1 → r ≠ -i → IsZero (M.X r)) ∧
          Mono (M.d (-i - 1) (-i)) ∧
          cokernel.π (kernel.ι (K.d (-i - 1) (-i))) ≫ e₀.inv ≫
              M.d (-i - 1) (-i) ≫ e₁.hom ≫ K.iCycles (-i) =
            K.d (-i - 1) (-i) ∧
          (pi K i).f (-i) ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-i)
                (K.homology (-i))).hom =
            e.hom.f (-i) ≫ e₁.hom ≫ K.homologyπ (-i) ∧
          QuasiIso (pi K i)) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
          φ.hom = f ∧
          ∀ (i : ℤ),
            FilteredObject.gradedMapSteps φ i ≫ pi L i =
              pi K i ≫
                (singleFunctor (ModuleCat.{u} R) (-i)).map
                  (HomologicalComplex.homologyMap f (-i))) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f g : K ⟶ L),
        (h : Homotopy f g) →
          ∃ (hf : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            hf.hom = f ∧
            ∃ (hg : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
              hg.hom = g ∧
              ∀ (i n m : ℤ),
                ∃ lift : ((F K).step i : CochainComplex (ModuleCat.{u} R) ℤ).X n ⟶
                  ((F L).step i : CochainComplex (ModuleCat.{u} R) ℤ).X m,
                  lift ≫ ((F L).step i).arrow.f m =
                    ((F K).step i).arrow.f n ≫ h.hom n m) ∧
      (∀ (K L : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (K.X r))
        (hL : ∃ (m n : ℤ), ∀ (r : ℤ), r < m ∨ n < r → IsZero (L.X r))
        (f : K ⟶ L),
        (∀ (r : ℤ), IsIso (K.homologyMap f r)) →
          ∀ (i : ℤ), ∃ (φ : FilteredObject.Hom ⟨K, F K⟩ ⟨L, F L⟩),
            φ.hom = f ∧ QuasiIso (FilteredObject.gradedMapSteps φ i)) := by
  classical
  obtain ⟨inc, j, barj, hinc, hses, hsupport, hcoords, hprojection, hnat⟩ :=
    exists_upperTruncationStepSES (C := ModuleCat.{u} R)
  let F := fun K : CochainComplex (ModuleCat.{u} R) ℤ ↦ canonicalFiltration K
  let s (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :=
    Subobject.ofLE ((F K).step (p + 1)) ((F K).step p) ((F K).F_succ_le p)
  let ep (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      ((F K).step (p + 1) : CochainComplex (ModuleCat.{u} R) ℤ) ≅
        K.truncLE (-p - 1) :=
    canonicalStepIso K (p + 1) ≪≫
      eqToIso (congrArg K.truncLE (by omega : -(p + 1) = -p - 1))
  have hep (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      (ep K p).hom ≫ K.ιTruncLE (-p - 1) = ((F K).step (p + 1)).arrow := by
    dsimp only [ep, Iso.trans_hom, eqToIso.hom]
    rw [Category.assoc, truncation_eqToHom, canonicalStepIso_arrow]
    omega
  have hs (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      s K p ≫ (canonicalStepIso K p).hom = (ep K p).hom ≫ inc K (-p) := by
    apply (cancel_mono (K.ιTruncLE (-p))).1
    rw [Category.assoc, canonicalStepIso_arrow]
    rw [Category.assoc, hinc, hep]
    exact Subobject.ofLE_arrow _
  let e (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      (F K).gradedPiece p ≅ cokernel (inc K (-p)) :=
    cokernel.mapIso (s K p) (inc K (-p)) (ep K p) (canonicalStepIso K p) (hs K p)
  let pi (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :=
    (e K p).hom ≫ barj K (-p)
  have he (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      cokernel.π (s K p) ≫ (e K p).hom =
        (canonicalStepIso K p).hom ≫ cokernel.π (inc K (-p)) := by
    simp [e]
  have hpi (K : CochainComplex (ModuleCat.{u} R) ℤ) (p : ℤ) :
      cokernel.π (s K p) ≫ pi K p = (canonicalStepIso K p).hom ≫ j K (-p) := by
    dsimp only [pi]
    rw [← Category.assoc, he, Category.assoc, ← (hprojection K (-p)).2.2.1]
  have hres {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (p : ℤ) :
      FilteredObject.restrictionSteps (canonicalFilteredMap f) p ≫
          (canonicalStepIso L p).hom =
        (canonicalStepIso K p).hom ≫ truncLEMap f (-p) := by
    apply (cancel_mono (L.ιTruncLE (-p))).1
    rw [Category.assoc, canonicalStepIso_arrow, Category.assoc, ιTruncLE_naturality]
    rw [← Category.assoc, canonicalStepIso_arrow]
    exact Classical.choose_spec ((canonicalFilteredMap f).preserves p)
  have hnatural {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (p : ℤ) :
      FilteredObject.gradedMapSteps (canonicalFilteredMap f) p ≫ pi L p =
        pi K p ≫ (singleFunctor (ModuleCat.{u} R) (-p)).map
          (HomologicalComplex.homologyMap f (-p)) := by
    obtain ⟨_, g, hg, hb⟩ := hnat f (-p)
    have hj : truncLEMap f (-p) ≫ j L (-p) =
        j K (-p) ≫ (singleFunctor (ModuleCat.{u} R) (-p)).map
          (HomologicalComplex.homologyMap f (-p)) := by
      rw [(hprojection L (-p)).2.2.1, ← Category.assoc, hg, Category.assoc,
        ← hb, ← Category.assoc, ← (hprojection K (-p)).2.2.1]
    apply (cancel_epi (cokernel.π (s K p))).1
    have hgr := Classical.choose_spec
      (FilteredObject.exists_gradedMap_steps _ _ (canonicalFilteredMap f) p)
    change cokernel.π (s K p) ≫
        FilteredObject.gradedMapSteps (canonicalFilteredMap f) p =
      FilteredObject.restrictionSteps (canonicalFilteredMap f) p ≫
        cokernel.π (s L p) at hgr
    rw [← Category.assoc, hgr, Category.assoc, hpi, ← Category.assoc, hres,
      Category.assoc, hj, ← Category.assoc, ← hpi, Category.assoc]
  refine ⟨F, pi, fun K p ↦ rfl, canonicalFiltration_bounded, ?_, ?_, ?_, ?_⟩
  · intro K hK p
    obtain ⟨e₀, e₁, _, _, hd, hm, hb⟩ := hcoords K (-p)
    have hb' : (barj K (-p)).f (-p) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-p)
          (K.homology (-p))).hom = e₁.hom ≫ K.homologyπ (-p) := by
      rw [← hb]
      simp
    have : QuasiIso (barj K (-p)) := (hprojection K (-p)).2.2.2.2.2
    refine ⟨cokernel (inc K (-p)), e K p, e₀, e₁, hsupport K (-p), hm, hd, ?_, ?_⟩
    · simp only [pi, HomologicalComplex.comp_f, Category.assoc, hb']
    · dsimp only [pi]
      infer_instance
  · intro K L hK hL f
    exact ⟨canonicalFilteredMap f, rfl, hnatural f⟩
  · intro K L hK hL f g h
    exact ⟨canonicalFilteredMap f, rfl, canonicalFilteredMap g, rfl,
      canonicalFiltration_homotopy h⟩
  · intro K L hK hL f hf p
    have : QuasiIso (barj K (-p)) := (hprojection K (-p)).2.2.2.2.2
    have : QuasiIso (barj L (-p)) := (hprojection L (-p)).2.2.2.2.2
    have : QuasiIso (pi K p) := by dsimp only [pi]; infer_instance
    have : QuasiIso (pi L p) := by dsimp only [pi]; infer_instance
    have := hf (-p)
    have : IsIso ((singleFunctor (ModuleCat.{u} R) (-p)).map
        (HomologicalComplex.homologyMap f (-p))) := inferInstance
    refine ⟨canonicalFilteredMap f, rfl, ?_⟩
    apply (quasiIso_iff_comp_right _ (pi L p)).1
    rw [hnatural]
    infer_instance

end CochainComplex
