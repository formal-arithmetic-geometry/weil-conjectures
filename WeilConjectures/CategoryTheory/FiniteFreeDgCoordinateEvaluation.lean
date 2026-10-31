/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import Mathlib.Data.Int.Interval
import all WeilConjectures.Algebra.Homology.RingedSiteStrictPerfectHom
import all WeilConjectures.Algebra.Homology.RingedOrdinaryEvaluationLocalization

/-! # Finite-free DG coordinate evaluation

Source: Stacks Project, `sdga.tex`, Tag 0FRS, lemma-tensor-hom-adjunction-dg;
the finite homogeneous-basis expansion for a bounded finite-free complex
(blueprint: lem-sf-finite-free-dg-coordinate-evaluation).

For a bounded complex whose terms are finite sums of the coefficient sheaf, the
canonical sheafified total-tensor evaluation is an isomorphism.  On a homogeneous
map its inverse is the finite sum of the values on the chosen homogeneous basis
against the corresponding dual basis; the tensor order displayed in the source
has no additional Koszul sign.  The formula is natural in both complexes and the
same finite expansion proves preservation of quasi-isomorphisms, with no bound on
the input complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

namespace FiniteFreeDgEvaluation

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "O" => ringedSiteDualityUnitComplex.{c, v, r} J R
set_option hygiene false in
set_option quotPrecheck false in
local notation "H" => homComplex.{c, v, max c v r, max c v r} (R := R)
set_option hygiene false in
set_option quotPrecheck false in
local notation "T" => WeilConjectures.coefficientTotalTensor.{r, c, v} J R

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem section_ext (P M : CochainComplex Mod ℤ) (n : ℤ) (U : Cᵒᵖ)
    (x y : ((H P M).X n).val.obj U)
    (h : ∀ i, (homComplexπ P M n i (i + n) rfl).val.app U x =
      (homComplexπ P M n i (i + n) rfl).val.app U y) : x = y := by
  apply Concrete.isLimit_ext _
    (isLimitOfPreserves (SheafOfModules.evaluation _ U) (homComplexIsLimit P M n)) x y
  intro i
  simp only [Functor.mapCone_π_app, Fan.mk_π_app,
    SheafOfModules.evaluation, Functor.comp_map, Functor.comp_obj,
    PresheafOfModules.evaluation, Discrete.functor_obj_eq_as, SheafOfModules.forget]
  with_unfolding_all exact h i.as

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem post_apply (P M N : CochainComplex Mod ℤ) (f : M ⟶ N)
    (n i j : ℤ) (hij : i + n = j) (U : Cᵒᵖ) (z : ((H P M).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (P.X i).val.obj (op W.unop.left)) :
    (((homComplexπ P N n i j hij).val.app U
      (((homComplexFunctor (R := R)).obj (op P)).map f |>.f n |>.val.app U <| z)).app
      W).hom x =
      (f.f j).val.app (op W.unop.left)
        ((((homComplexπ P M n i j hij).val.app U z).app W).hom x) := by
  have h := congrArg (fun k ↦ ((k.val.app U z).app W).hom x)
    (homComplexFunctor_obj_map_f_π (R := R) (L := P) f n i j hij)
  exact h

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem pre_apply (P P' M : CochainComplex Mod ℤ) (g : P' ⟶ P)
    (n i j : ℤ) (hij : i + n = j) (U : Cᵒᵖ) (z : ((H P M).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (P'.X i).val.obj (op W.unop.left)) :
    (((homComplexπ P' M n i j hij).val.app U
      ((((homComplexFunctor (R := R)).map g.op).app M).f n |>.val.app U <| z)).app
      W).hom x =
      (((homComplexπ P M n i j hij).val.app U z).app W).hom
        ((g.f i).val.app (op W.unop.left) x) := by
  have h := homComplexFunctor_map_f_π (R := R) g (𝟙 M) n i j hij
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at h
  exact congrArg (fun k ↦ ((k.val.app U z).app W).hom x) h

private theorem evaluation_apply (P M : CochainComplex Mod ℤ)
    (ε : (T).obj (M, H P O) ⟶ H P M) (hε : RingedSiteEvaluationFormula.{c, v, r} J R P M ε)
    (p q n i : ℤ) (hpq : p + q = n) (hiq : i + q = 0) (hip : i + n = p)
    (U : Cᵒᵖ) (y : (M.X p).val.obj U) (φ : ((H P O).X q).val.obj U)
    (x : (P.X i).val.obj U) :
    (((homComplexπ P M n i p hip).val.app U
      ((ε.f n).val.app U
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M (H P O) p q n hpq U y φ))).app
      (op (Over.mk (𝟙 U.unop)))).hom x =
      (((homComplexπ P O q i 0 hiq).val.app U φ).app
        (op (Over.mk (𝟙 U.unop)))).hom x • y := by
  have h := hε.1 p q n i hpq hiq hip U y φ (op (Over.mk (𝟙 U.unop))) x
  change _ = _ • (show (M.X p).val.obj U from (M.X p).val.map (𝟙 U) y) at h
  have hid : (M.X p).val.map (𝟙 U) y = y := by
    rw [PresheafOfModules.map_id]
    rfl
  exact h.trans (congrArg (fun z : (M.X p).val.obj U ↦
    (((homComplexπ P O q i 0 hiq).val.app U φ).app
      (op (Over.mk (𝟙 U.unop)))).hom x • z) hid)

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem hom_section_naturality (A B : Mod) (U : Cᵒᵖ)
    (φ : (SheafOfModules.homObj (R := R) A B).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj U) :
    B.val.map W.unop.hom.op
      ((φ.app (op (Over.mk (𝟙 U.unop)))).hom x) =
      (φ.app W).hom (A.val.map W.unop.hom.op x) := by
  exact (PresheafOfModules.naturality_apply φ
    (Over.homMk W.unop.hom (by simp) : W.unop ⟶ Over.mk (𝟙 U.unop)).op x).symm

private theorem natural_target (P M N : CochainComplex Mod ℤ)
    (ε : (T).obj (M, H P O) ⟶ H P M) (ε' : (T).obj (N, H P O) ⟶ H P N)
    (hε : RingedSiteEvaluationFormula.{c, v, r} J R P M ε)
    (hε' : RingedSiteEvaluationFormula.{c, v, r} J R P N ε') (f : M ⟶ N) :
    ε ≫ ((homComplexFunctor (R := R)).obj (op P)).map f =
      (T).map (Prod.mkHom f (𝟙 (H P O))) ≫ ε' := by
  let : HasDerivedCategory.{max c v r + 1} Mod := HasDerivedCategory.standard Mod
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro i j hij
  apply ordinaryTotalHom_ext.{c, v, r} J R M (H P O) (P.X i) (N.X j) n
  intro p q hpq U y φ x
  change (((homComplexπ P N n i j hij).val.app U
      (((((homComplexFunctor (R := R)).obj (op P)).map f).f n).val.app U
        ((ε.f n).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M (H P O)
            p q n hpq U y φ)))).app (op (Over.mk (𝟙 U.unop)))).hom x = _
  rw [post_apply.{c, v, r} J R]
  change _ = (((homComplexπ P N n i j hij).val.app U
    ((ε'.f n).val.app U
      ((((T).map (Prod.mkHom f (𝟙 (H P O)))).f n).val.app U
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M (H P O)
          p q n hpq U y φ)))).app (op (Over.mk (𝟙 U.unop)))).hom x
  erw [ordinaryGenerator_map.{c, v, r} J R]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  by_cases hiq : i + q = 0
  · have hjp : j = p := by omega
    subst p
    erw [evaluation_apply.{c, v, r} J R P M ε hε j q n i hpq hiq hij,
      evaluation_apply.{c, v, r} J R P N ε' hε' j q n i hpq hiq hij]
    exact map_smul _ _ _
  · have h₁ := hε.2 p q n i j hpq hij hiq U y φ
    have h₂ := hε'.2 p q n i j hpq hij hiq U ((f.f p).val.app U y) φ
    change (homComplexπ P M n i j hij).val.app U _ = 0 at h₁
    change (homComplexπ P N n i j hij).val.app U _ = 0 at h₂
    erw [h₁, h₂]
    exact ((f.f j).val.app U).hom.map_zero

private theorem natural_source (P P' M : CochainComplex Mod ℤ)
    (ε : (T).obj (M, H P O) ⟶ H P M) (ε' : (T).obj (M, H P' O) ⟶ H P' M)
    (hε : RingedSiteEvaluationFormula.{c, v, r} J R P M ε)
    (hε' : RingedSiteEvaluationFormula.{c, v, r} J R P' M ε') (g : P' ⟶ P) :
    ε ≫ ((homComplexFunctor (R := R)).map g.op).app M =
      (T).map (Prod.mkHom (𝟙 M) (((homComplexFunctor (R := R)).map g.op).app O)) ≫ ε' := by
  let : HasDerivedCategory.{max c v r + 1} Mod := HasDerivedCategory.standard Mod
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro i j hij
  apply ordinaryTotalHom_ext.{c, v, r} J R M (H P O) (P'.X i) (M.X j) n
  intro p q hpq U y φ x
  change (((homComplexπ P' M n i j hij).val.app U
      (((((homComplexFunctor (R := R)).map g.op).app M).f n).val.app U
        ((ε.f n).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M (H P O)
            p q n hpq U y φ)))).app (op (Over.mk (𝟙 U.unop)))).hom x = _
  rw [pre_apply.{c, v, r} J R]
  change _ = (((homComplexπ P' M n i j hij).val.app U
    ((ε'.f n).val.app U
      ((((T).map (Prod.mkHom (𝟙 M)
        (((homComplexFunctor (R := R)).map g.op).app O))).f n).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M (H P O)
            p q n hpq U y φ)))).app (op (Over.mk (𝟙 U.unop)))).hom x
  erw [ordinaryGenerator_map.{c, v, r} J R]
  simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  by_cases hiq : i + q = 0
  · have hjp : j = p := by omega
    subst p
    erw [evaluation_apply.{c, v, r} J R P M ε hε j q n i hpq hiq hij,
      evaluation_apply.{c, v, r} J R P' M ε' hε' j q n i hpq hiq hij,
      pre_apply.{c, v, r} J R]
  · have h₁ := hε.2 p q n i j hpq hij hiq U y φ
    have h₂ := hε'.2 p q n i j hpq hij hiq U y
      (((((homComplexFunctor (R := R)).map g.op).app O).f q).val.app U φ)
    change (homComplexπ P M n i j hij).val.app U _ = 0 at h₁
    change (homComplexπ P' M n i j hij).val.app U _ = 0 at h₂
    erw [h₁, h₂]
    rfl

end FiniteFreeDgEvaluation

/-- The finite-free tensor--Hom evaluation comparison, with the finite homogeneous-basis
inverse and its quasi-isomorphism consequences.

Source: Stacks Project, `sdga.tex`, Tag 0FRS, lemma-tensor-hom-adjunction-dg
(blueprint: lem-sf-finite-free-dg-coordinate-evaluation).
The inverse is the finite sum `Ψ_M(h) = Σ h^i(e_{i,j}) ⊗ e^*_{i,j}` on a homogeneous
map `h`; it is independent of the chosen bases and has no extra sign in the order
`M tensor P^vee`. The `RingedSiteEvaluationFormula` conjunct spells out the canonical
homogeneous evaluation, including the zero components.

Proof plan:
1. In degree n the tensor total and Hom product reduce to the finitely many
   source degrees in [a,b]. Sheafified bilinear evaluation gives the stated map.
2. For each finite basis define the inverse by summing h(e) tensor e*. The
   reconstruction identity on each slice proves both inverse identities.
   Hence every basis gives the same inverse of the same evaluation map.
3. Expand the tensor and Hom differentials. Both give lambda(p) dm plus
   (-1)^(degree(m)+degree(lambda)+1) lambda(dp) m. Thus evaluation is a chain map
   and its degreewise inverse is automatically a chain map.
4. Postcomposition with a chain map commutes with scalar evaluation, proving
   naturality; precomposition proves contravariant naturality in P.
5. The dual is bounded, with finite-free and therefore flat terms. Apply the
   bounded-above flat K-flat criterion (Stacks 06YQ).
6. K-flat tensor preserves every quasi-isomorphism (Stacks 06YP). Naturality
   conjugates Hom(P,f) to f tensor id through the two evaluation isomorphisms.
   No step imposes a bound on either target complex.
-/
theorem finiteFreeDgCoordinateEvaluation
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (a b : ℤ) (bounded : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (finiteFree : ∀ i : ℤ, ∃ n : ℕ,
      Nonempty (P.X i ≅ ∐ (fun _ : Fin n ↦
        SheafOfModules.unit ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))) :
    ∃ Θ : ∀ (M : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ),
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
          (M, homComplex.{c, v, max c v r, max c v r} (R := R) P
            (ringedSiteDualityUnitComplex.{c, v, r} J R)) ≅
        homComplex.{c, v, max c v r, max c v r} (R := R) P M,
      (∀ (M : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ),
        RingedSiteEvaluationFormula.{c, v, r} J R P M (Θ M).hom) ∧
      (∀ (M : CochainComplex (SheafOfModules.{max c v r}
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
        (U : Cᵒᵖ) (n : ℤ) (ranks : ↥(Finset.Icc a b) → ℕ)
        (e : ∀ i : ↥(Finset.Icc a b), Fin (ranks i) → (P.X i.val).val.obj U)
        (dual : ∀ i : ↥(Finset.Icc a b), Fin (ranks i) →
          ((homComplex.{c, v, max c v r, max c v r} (R := R) P
            (ringedSiteDualityUnitComplex.{c, v, r} J R)).X (-i.val)).val.obj U),
        (∀ (i : ↥(Finset.Icc a b)) (W : (Over U.unop)ᵒᵖ)
          (x : (P.X i.val).val.obj (op W.unop.left)),
          ∑ j : Fin (ranks i),
            ((((WeilConjectures.coefficientHomComponent.{r, c, v} J R P
              (ringedSiteDualityUnitComplex.{c, v, r} J R) (-i.val) i.val 0
              (add_neg_cancel i.val)).val.app U (dual i j)).app W).hom x) •
              (P.X i.val).val.map W.unop.hom.op (e i j) = x) →
        ∀ h : ((homComplex.{c, v, max c v r, max c v r} (R := R) P M).X n).val.obj U,
          (((Θ M).inv.f n).val.app U h) =
            ∑ i : ↥(Finset.Icc a b), ∑ j : Fin (ranks i),
              WeilConjectures.coefficientTensorGenerator.{r, c, v} J R M
                (homComplex.{c, v, max c v r, max c v r} (R := R) P
                  (ringedSiteDualityUnitComplex.{c, v, r} J R))
                (i.val + n) (-i.val) n (by omega) U
                ((((WeilConjectures.coefficientHomComponent.{r, c, v} J R P M
                  n i.val (i.val + n) rfl).val.app U h).app
                    (op (Over.mk (𝟙 U.unop)))).hom (e i j)) (dual i j)) ∧
      (∀ (M N : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
        (f : M ⟶ N),
        (Θ M).hom ≫
            ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f =
          (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).map
            (Prod.mkHom f
              (𝟙 (homComplex.{c, v, max c v r, max c v r} (R := R) P
              (ringedSiteDualityUnitComplex.{c, v, r} J R)))) ≫ (Θ N).hom) ∧
      (∀ (P' M : CochainComplex (SheafOfModules.{max c v r}
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
        (g : P' ⟶ P)
        (ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
            (M, homComplex.{c, v, max c v r, max c v r} (R := R) P'
              (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶
          homComplex.{c, v, max c v r, max c v r} (R := R) P' M),
        RingedSiteEvaluationFormula.{c, v, r} J R P' M ε →
        (Θ M).hom ≫
            ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map g.op).app M =
          (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).map
            (Prod.mkHom (𝟙 M)
              (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map g.op).app
                (ringedSiteDualityUnitComplex.{c, v, r} J R))) ≫ ε) ∧
      (∀ (M N : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
        (f : M ⟶ N),
        HomologicalComplex.quasiIso _ (.up ℤ) f →
        HomologicalComplex.quasiIso _ (.up ℤ)
          ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).map
            (Prod.mkHom f
              (𝟙 (homComplex.{c, v, max c v r, max c v r} (R := R) P
              (ringedSiteDualityUnitComplex.{c, v, r} J R)))))) ∧
      (∀ (M N : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
        (f : M ⟶ N),
        HomologicalComplex.quasiIso _ (.up ℤ) f →
        HomologicalComplex.quasiIso _ (.up ℤ)
          (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f)) := by
  classical
  let Mod := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : HasDerivedCategory.{max c v r + 1} Mod := HasDerivedCategory.standard Mod
  let : HasFiniteBiproducts Mod := HasFiniteBiproducts.of_hasFiniteProducts
  let ranks (i : ℤ) := (finiteFree i).choose
  let e (i : ℤ) := (finiteFree i).choose_spec.some ≪≫
    (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _
  let pkg : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ P :=
    { N := ranks
      i := fun i ↦ (e i).hom
      p := fun i ↦ (e i).inv
      splitting := fun i ↦ (e i).hom_inv_id }
  have hbound : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (P.X i) :=
    ⟨a, b, bounded⟩
  have hiso (M) : IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R P M) :=
    ordinaryEvaluation_isIso_assembly.{c, v, r} J R P M hbound pkg
  let Θ (M) := @asIso _ _ _ _ (ringedSiteOrdinaryEvaluation.{c, v, r} J R P M) (hiso M)
  refine ⟨Θ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M
    exact (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P M).exists.choose_spec
  · intro M U n ranks e dual hframe h
    have hε : RingedSiteEvaluationFormula.{c, v, r} J R P M (Θ M).hom :=
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P M).exists.choose_spec
    let eU := (SheafOfModules.evaluation _ U).mapIso
      ((HomologicalComplex.eval Mod (.up ℤ) n).mapIso (Θ M))
    apply (ConcreteCategory.bijective_of_isIso eU.hom).1
    change ((Θ M).hom.f n).val.app U _ = ((Θ M).hom.f n).val.app U _
    have hcancel : ((Θ M).hom.f n).val.app U (((Θ M).inv.f n).val.app U h) = h :=
      congrArg (fun f ↦ (f.f n).val.app U h) (Θ M).inv_hom_id
    rw [hcancel]
    apply FiniteFreeDgEvaluation.section_ext.{c, v, r} J R P M n U
    intro k
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    let ev : ((homComplex (R := R) P M).X n).val.obj U →+
        (M.X (k + n)).val.obj (op W.unop.left) :=
      { toFun z := (((homComplexπ P M n k (k + n) rfl).val.app U z).app W).hom x
        map_zero' := by simp only [map_zero]; rfl
        map_add' z z' := by rw [map_add]; rfl }
    change ev h = ev (((Θ M).hom.f n).val.app U _)
    simp only [map_sum]
    by_cases hk : k ∈ Finset.Icc a b
    · let k' : ↥(Finset.Icc a b) := ⟨k, hk⟩
      rw [Finset.sum_eq_single k']
      · have hreconstruct := congrArg
          (fun y ↦ (((homComplexπ P M n k (k + n) rfl).val.app U h).app W).hom y)
          (hframe k' W x)
        rw [map_sum] at hreconstruct
        simp only [map_smul] at hreconstruct
        symm
        calc
          _ = ∑ j : Fin (ranks k'),
              ((((WeilConjectures.coefficientHomComponent.{r, c, v} J R P
                (ringedSiteDualityUnitComplex.{c, v, r} J R) (-k) k 0 (by omega)).val.app U
                  (dual k' j)).app W).hom x) •
                (M.X (k + n)).val.map W.unop.hom.op
                  ((((homComplexπ P M n k (k + n) rfl).val.app U h).app
                    (op (Over.mk (𝟙 U.unop)))).hom (e k' j)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact hε.1 (k + n) (-k) n k (by omega) (by omega) rfl U _ _ W x
          _ = _ := by
            simp_rw [FiniteFreeDgEvaluation.hom_section_naturality.{c, v, r} J R]
            exact hreconstruct
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        have hki : k + -i.val ≠ 0 := by
          intro hki
          apply hi
          apply Subtype.ext
          dsimp [k']
          omega
        have hz := hε.2 (i.val + n) (-i.val) n k (k + n) (by omega) rfl hki U
          ((((WeilConjectures.coefficientHomComponent.{r, c, v} J R P M
            n i.val (i.val + n) rfl).val.app U h).app
              (op (Over.mk (𝟙 U.unop)))).hom (e i j)) (dual i j)
        change (homComplexπ P M n k (k + n) rfl).val.app U _ = 0 at hz
        dsimp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [hz]
        rfl
      · intro hk'
        exact (hk' (Finset.mem_univ k')).elim
    · have hz := bounded k (by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hk)
      have hx : x = 0 :=
        congrArg (fun f ↦ f.val.app (op W.unop.left) x) (hz.eq_of_src (𝟙 _) 0)
      subst x
      have hev (z) : ev z = 0 :=
        (((homComplexπ P M n k (k + n) rfl).val.app U z).app W).hom.map_zero
      simp only [hev, Finset.sum_const_zero]
  · intro M N f
    exact FiniteFreeDgEvaluation.natural_target.{c, v, r} J R P M N _ _
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P M).exists.choose_spec
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P N).exists.choose_spec f
  · intro P' M g ε hε
    exact FiniteFreeDgEvaluation.natural_source.{c, v, r} J R P P' M _ ε
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P M).exists.choose_spec hε g
  · intro M N f hf
    have hn := FiniteFreeDgEvaluation.natural_target.{c, v, r} J R P M N
      (Θ M).hom (Θ N).hom
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P M).exists.choose_spec
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R P N).exists.choose_spec f
    have : QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by
      let : QuasiIso f := hf
      exact SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms.{c, v, r}
        J R P hbound (fun i S hS ↦ term_exact.{c, v, r} J R (P.X i)
          (pkg.N i) (pkg.i i) (pkg.p i) (pkg.splitting i) S hS) f
    apply (quasiIso_iff_comp_right _ (Θ N).hom).1
    rw [← hn]
    infer_instance
  · intro M N f hf
    let : QuasiIso f := hf
    exact SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms.{c, v, r}
      J R P hbound (fun i S hS ↦ term_exact.{c, v, r} J R (P.X i)
        (pkg.N i) (pkg.i i) (pkg.p i) (pkg.splitting i) S hS) f

end CategoryTheory
