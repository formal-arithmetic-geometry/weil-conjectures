/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorCoherence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearCartesianHomEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Existence of the ordinary semilinear system calculus

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.SemilinearSections

variable {C₀ : Type c} [Category.{v} C₀] (J₀ : GrothendieckTopology C₀)
  [EssentiallySmall.{max c v r} C₀]
  (B₀ : ℕ → Sheaf J₀ CommRingCat.{max c v r})
  (τ₀ : ∀ n : ℕ, B₀ (n + 1) ⟶ B₀ n)

/-- The ordinary system calculus and its cartesian internal-Hom transition law.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
Proof: construct the ringed sequence site, its Grothendieck derived category,
component evaluations, K-flat tensor and K-injective Hom models. The transition
law is obtained by transposing the component evaluation map through the
cartesian reduction isomorphisms and the tensor-Hom adjunction; the tensor
associators give its cocycle. -/
structure SemilinearSystemData where
  systems : Data.{c, v, r} J₀ B₀ τ₀
  homTransition : systems.HomReductionFormula J₀ B₀ τ₀
  /-- Normalization is retained with the calculus, rather than inferred from binary models. -/
  tensorNormalization : Nonempty { M : NormalizedTensorModel.{c, v, r}
    (coefficientSequenceTopology J₀) (systemRing.{c, v, max c v r} J₀ B₀ τ₀) //
      M.closed = systems.closed }

private theorem systemsGrothendieck :
    IsGrothendieckAbelian.{max c v r} (Systems.{c, v, max c v r} J₀ B₀ τ₀) := by
  let : HasSheafify (coefficientSequenceTopology J₀) AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} (coefficientSequenceTopology J₀)
  let : (coefficientSequenceTopology J₀).WEqualsLocallyBijective
      AddCommGrpCat.{max c v r} :=
    locallyBijective.{c, v, max c v r} (coefficientSequenceTopology J₀)
  exact
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      (coefficientSequenceTopology J₀) (systemRing.{c, v, max c v r} J₀ B₀ τ₀)).1

private theorem evaluationTriangulated (n : ℕ) :
    ∃ (_ : (e.{c, v, max c v r} J₀ B₀ τ₀ n).CommShift ℤ),
      (e.{c, v, max c v r} J₀ B₀ τ₀ n).IsTriangulated := by
  exact ⟨inferInstance, inferInstance⟩

private theorem systemsIsZero (M : Systems.{c, v, max c v r} J₀ B₀ τ₀)
    (hM : ∀ n : ℕ, IsZero ((evaluation.{c, v, max c v r} J₀ B₀ τ₀ n).obj M)) :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨n, U⟩
  ext x
  exact congrArg (fun f ↦ f.val.app (op U) x) ((hM n).eq_of_src (𝟙 _) 0)

private theorem systemsComponentwise (s : ShortComplex (Systems.{c, v, max c v r} J₀ B₀ τ₀)) :
    s.Exact ↔ ∀ n : ℕ, (s.map (evaluation.{c, v, max c v r} J₀ B₀ τ₀ n)).Exact := by
  constructor
  · intro hs n
    exact hs.map _
  · intro hs
    apply s.exact_iff_isZero_homology.mpr
    apply systemsIsZero.{c, v, r} J₀ B₀ τ₀
    intro n
    exact IsZero.of_iso
      ((s.map (evaluation.{c, v, max c v r} J₀ B₀ τ₀ n)).exact_iff_isZero_homology.mp (hs n))
      (s.mapHomologyIso (evaluation.{c, v, max c v r} J₀ B₀ τ₀ n)).symm

private theorem evaluationDetects {M N : Systems.{c, v, max c v r} J₀ B₀ τ₀}
    (f : M ⟶ N) (hf : ∀ n : ℕ, IsIso ((evaluation.{c, v, max c v r} J₀ B₀ τ₀ n).map f)) :
    IsIso f := by
  let U := SheafOfModules.forget
      (ring.{c, v, max c v r} (coefficientSequenceTopology J₀)
        (systemRing.{c, v, max c v r} J₀ B₀ τ₀)) ⋙
    PresheafOfModules.toPresheaf _
  have : IsIso (U.map f) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    rintro ⟨n, V⟩
    have := hf n
    exact inferInstanceAs (IsIso
      (((SheafOfModules.toSheaf (ring.{c, v, max c v r} J₀ (B₀ n))).map
        ((evaluation.{c, v, max c v r} J₀ B₀ τ₀ n).map f)).hom.app (op V)))
  exact isIso_of_reflects_iso f U

private theorem derivedEvaluationDetects {M N : DS.{c, v, max c v r} J₀ B₀ τ₀}
    (f : M ⟶ N) (hf : ∀ n : ℕ, IsIso ((e.{c, v, max c v r} J₀ B₀ τ₀ n).map f)) :
    IsIso f := by
  apply (DerivedCategory.isIso_iff (Systems.{c, v, max c v r} J₀ B₀ τ₀) f).mpr
  intro i
  apply evaluationDetects.{c, v, r} J₀ B₀ τ₀
  intro n
  have := hf n
  exact (NatIso.isIso_map_iff
    ((evaluation.{c, v, max c v r} J₀ B₀ τ₀ n).mapDerivedCategoryHomologyFunctorIso i) f).2
    (inferInstanceAs (IsIso
      ((DerivedCategory.homologyFunctor (Mod.{c, v, max c v r} J₀ (B₀ n)) i).map
        ((e.{c, v, max c v r} J₀ B₀ τ₀ n).map f))))

private theorem reductionNaturality
    (S : ∀ {m n : ℕ} (h : n ≤ m),
      ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J₀ B₀ τ₀ h))
    {m n : ℕ} (h : n ≤ m)
    {M N : DS.{c, v, max c v r} J₀ B₀ τ₀} (f : M ⟶ N) :
    (S h).T.map ((e.{c, v, max c v r} J₀ B₀ τ₀ m).map f) ≫
        reduction.{c, v, max c v r} J₀ B₀ τ₀ h (S h) N =
      reduction.{c, v, max c v r} J₀ B₀ τ₀ h (S h) M ≫
        (e.{c, v, max c v r} J₀ B₀ τ₀ n).map f := by
  apply ((S h).adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  exact (derivedTransition.{c, v, max c v r} J₀ B₀ τ₀ h).naturality f

private theorem tensorHomTranspose
    {D₀ D₁ : Type*} [Category* D₀] [Category* D₁]
    (H₁ : D₁ᵒᵖ × D₁ ⥤ D₁) (S₁ : CoefficientClosedStructure H₁)
    (t₀ : D₀ × D₀ ⥤ D₀) (F : D₀ ⥤ D₁)
    (μ : t₀ ⋙ F ≅ (F.prod F) ⋙ S₁.tensor)
    {V W X Y : D₀} {X' Y' : D₁}
    (a : V ⟶ W) (v₀ : t₀.obj (W, X) ⟶ Y)
    (x : F.obj V ⟶ H₁.obj (op X', Y')) (y : F.obj X ≅ X') (z : F.obj Y ⟶ Y')
    (hw : S₁.tensor.map (Prod.mkHom x y.hom) ≫ S₁.evaluation X' Y' =
      μ.inv.app (V, X) ≫ F.map (t₀.map (Prod.mkHom a (𝟙 X)) ≫ v₀) ≫ z) :
    x = F.map a ≫ S₁.transpose _ X' Y'
      (S₁.tensor.map (Prod.mkHom (𝟙 _) y.inv) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z) := by
  let := S₁.monoidal
  have hmap {P Q : D₁} (f : P ⟶ Q) :
      (MonoidalCategory.tensorRight X').map f =
        S₁.tensor.map (Prod.mkHom f (𝟙 X')) := by
    exact (MonoidalCategory.tensorHom_id f X').symm
  apply ((S₁.adjunction X').homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [CoefficientClosedStructure.transpose]
  erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, hmap, hmap]
  change S₁.tensor.map (Prod.mkHom x (𝟙 X')) ≫ S₁.evaluation X' Y' =
    S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 X')) ≫
      (S₁.tensor.map (Prod.mkHom (𝟙 _) y.inv) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z)
  have : IsIso (Prod.mkHom (𝟙 (F.obj V)) y.hom) :=
    (isIso_prod_iff D₁ D₁).mpr ⟨inferInstance, inferInstance⟩
  apply (cancel_epi (S₁.tensor.map (Prod.mkHom (𝟙 (F.obj V)) y.hom))).mp
  have hc : S₁.tensor.map (Prod.mkHom (𝟙 (F.obj V)) y.hom) ≫
      S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 X')) ≫
      S₁.tensor.map (Prod.mkHom (𝟙 (F.obj W)) y.inv) =
      S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 (F.obj X))) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp,
      Category.comp_id, Iso.hom_inv_id]
  calc
    _ = S₁.tensor.map (Prod.mkHom x y.hom) ≫ S₁.evaluation X' Y' := by
      simp only [← Category.assoc, ← Functor.map_comp, prod_comp,
        Category.id_comp, Category.comp_id]
    _ = μ.inv.app (V, X) ≫ F.map (t₀.map (Prod.mkHom a (𝟙 X)) ≫ v₀) ≫ z := hw
    _ = S₁.tensor.map (Prod.mkHom (F.map a) (𝟙 (F.obj X))) ≫
        μ.inv.app (W, X) ≫ F.map v₀ ≫ z := by
      have hn := congrArg (fun k ↦ k ≫ F.map v₀ ≫ z)
        (μ.inv.naturality (Prod.mkHom a (𝟙 X))).symm
      dsimp only [Functor.comp_map, Functor.prod_map, Prod.mkHom] at hn
      simpa only [F.map_id, F.map_comp, Category.assoc] using hn
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ μ.inv.app (W, X) ≫ F.map v₀ ≫ z) hc.symm

private theorem homReductionFormula
    (A : Data.{c, v, r} J₀ B₀ τ₀)
    (hTensor : ∀ {m n : ℕ} (h : n ≤ m) (M N : DS.{c, v, max c v r} J₀ B₀ τ₀),
      (A.scalar h).T.map ((A.tensorEvaluation m).hom.app (M, N)) ≫
          (A.scalarTensor h).hom.app
            ((e.{c, v, max c v r} J₀ B₀ τ₀ m).obj M,
              (e.{c, v, max c v r} J₀ B₀ τ₀ m).obj N) ≫
          (A.levelClosed n).tensor.map
            (Prod.mkHom (reduction.{c, v, max c v r} J₀ B₀ τ₀ h (A.scalar h) M)
              (reduction.{c, v, max c v r} J₀ B₀ τ₀ h (A.scalar h) N)) =
        reduction.{c, v, max c v r} J₀ B₀ τ₀ h (A.scalar h) (A.closed.tensor.obj (M, N)) ≫
          (A.tensorEvaluation n).hom.app (M, N)) :
    A.HomReductionFormula J₀ B₀ τ₀ := by
  intro M N hM m n h
  let H := (internalHom.{c, v, r} (coefficientSequenceTopology J₀)
    (systemRing.{c, v, max c v r} J₀ B₀ τ₀)).obj (op M, N)
  let Em := e.{c, v, max c v r} J₀ B₀ τ₀ m
  let En := e.{c, v, max c v r} J₀ B₀ τ₀ n
  let F := (A.scalar h).T
  let R (P : DS.{c, v, max c v r} J₀ B₀ τ₀) :=
    reduction.{c, v, max c v r} J₀ B₀ τ₀ h (A.scalar h) P
  let a := (A.homEvaluation M hM m).hom.app N
  let b := (A.homEvaluation M hM n).hom.app N
  let μ := A.scalarTensor h
  let δm := (A.tensorEvaluation m).app (H, M)
  let δn := (A.tensorEvaluation n).app (H, M)
  let d := A.cartesianReduction J₀ B₀ τ₀ M hM h
  have hr : (A.levelClosed n).tensor.map (Prod.mkHom (R H) (R M)) ≫ δn.inv =
      μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫ R (A.closed.tensor.obj (H, M)) := by
    have ht := hTensor h H M
    change F.map δm.hom ≫ μ.hom.app (Em.obj H, Em.obj M) ≫
      (A.levelClosed n).tensor.map (Prod.mkHom (R H) (R M)) =
      R (A.closed.tensor.obj (H, M)) ≫ δn.hom at ht
    have ht' := congrArg
      (fun f ↦ μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫ f ≫ δn.inv) ht
    simpa only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      F.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
      Iso.hom_inv_id, Category.comp_id] using ht'
  have hem : (A.levelClosed m).tensor.map (Prod.mkHom a (𝟙 (Em.obj M))) ≫
      (A.levelClosed m).evaluation (Em.obj M) (Em.obj N) =
      δm.inv ≫ Em.map (A.closed.evaluation M N) := by
    simpa only [a, δm, Em, H, Iso.app_inv] using A.homEvaluation_evaluation M N hM m
  have hen : (A.levelClosed n).tensor.map (Prod.mkHom b (𝟙 (En.obj M))) ≫
      (A.levelClosed n).evaluation (En.obj M) (En.obj N) =
      δn.inv ≫ En.map (A.closed.evaluation M N) := by
    simpa only [b, δn, En, H, Iso.app_inv] using A.homEvaluation_evaluation M N hM n
  have hw : (A.levelClosed n).tensor.map (Prod.mkHom (R H ≫ b) d.hom) ≫
      (A.levelClosed n).evaluation (En.obj M) (En.obj N) =
      μ.inv.app (Em.obj H, Em.obj M) ≫
        F.map ((A.levelClosed m).tensor.map (Prod.mkHom a (𝟙 (Em.obj M))) ≫
          (A.levelClosed m).evaluation (Em.obj M) (Em.obj N)) ≫ R N := by
    calc
      _ = (A.levelClosed n).tensor.map (Prod.mkHom (R H) (R M)) ≫
          ((A.levelClosed n).tensor.map (Prod.mkHom b (𝟙 (En.obj M))) ≫
            (A.levelClosed n).evaluation (En.obj M) (En.obj N)) := by
        have hp : Prod.mkHom (R H ≫ b) (R M) =
            Prod.mkHom (R H) (R M) ≫ Prod.mkHom b (𝟙 (En.obj M)) :=
          Prod.ext rfl (Category.comp_id (R M)).symm
        change (A.levelClosed n).tensor.map (Prod.mkHom (R H ≫ b) (R M)) ≫ _ = _
        rw [hp, Functor.map_comp, Category.assoc]
      _ = (A.levelClosed n).tensor.map (Prod.mkHom (R H) (R M)) ≫
          δn.inv ≫ En.map (A.closed.evaluation M N) := by
        rw [hen]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫
          R (A.closed.tensor.obj (H, M)) ≫ En.map (A.closed.evaluation M N) := by
        rw [← Category.assoc, hr, Category.assoc, Category.assoc]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫ F.map δm.inv ≫
          F.map (Em.map (A.closed.evaluation M N)) ≫ R N := by
        rw [reductionNaturality.{c, v, r} J₀ B₀ τ₀ A.scalar h (A.closed.evaluation M N)]
      _ = μ.inv.app (Em.obj H, Em.obj M) ≫
          F.map (δm.inv ≫ Em.map (A.closed.evaluation M N)) ≫ R N := by
        rw [F.map_comp, Category.assoc]
      _ = _ := by rw [← hem]
  exact tensorHomTranspose _ (A.levelClosed n) (A.levelClosed m).tensor F μ
    a ((A.levelClosed m).evaluation (Em.obj M) (Em.obj N))
    (R H ≫ b) d (R N) hw

/-- Ordinary semilinear system calculus and cartesian internal Hom.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 079P, 06YS, 06YY,
07A4 and 08J7--08JB (blueprint: lem-coef-semilinear-system-existence).
Proof:
1. Present the sequence topos by the small site $\mathcal C\times\mathbf N_{\geq1}$: an arrow
$(U,n)\to(W,m)$ consists of $U\to W$ and $n\leq m$, and generating covers have fixed index and are
covers of $\mathcal C$. Pulling back such a cover along an index-changing arrow still gives a
fixed-index cover, so this is a site. Its sheaf condition says exactly that each level is a sheaf;
the other restrictions give inverse-sequence transitions. The ring sheaf $(U,n)\mapsto B_n(U)$ is
therefore $B_\bullet$, and its module sheaves are exactly $\mathscr S(B)$. Kernels and cokernels
are computed at each level using kernels and sheafified cokernels of module sheaves; the
scalar-linear transitions descend to these constructions. Hence cohomology of a complex of systems
is componentwise.

2. Apply [lem-pur-ringed-site-grothendieck-abelian] and [prop-pur-kinjective-resolutions-exist] to
that small ringed site. This gives Grothendieck abelianness and unbounded K-injective resolutions
in $\mathscr S(B)$. Exact evaluation descends termwise by
[situation-conventions]. A morphism in the derived category is
invertible exactly when its cone is acyclic; its evaluated cones are the cones of its evaluations.
Componentwise cohomology therefore proves joint detection of isomorphisms. This uses only
localization of complexes of systems, not a category of diagrams in triangulated categories.

3. On underlying sequence topoi, evaluation $e_n$ is inverse image of a geometric morphism: its
right adjoint sends a sheaf $F$ to the sequence with value $F$ for $q\geq n$ and terminal sheaf
for $q<n$. The adjunction follows by extending the component at $n$ along the given transitions;
evaluation preserves finite limits. The structural ring map is $e_nB_\bullet=B_n$. Thus
[lem-weil-pbc-ringed-topos-kflat-pullback] says evaluation carries flat-term K-flat complexes on
the sequence site to flat-term K-flat complexes over $B_n$. Apply [lem-pc-kflat-resolution] on
that site and [lem-weil-pbc-site-derived-tensor-descent]: evaluating the resulting total tensor
complexes computes $e_n(M\otimes^L_{B_\bullet}N)=M_n\otimes^L_{B_n}N_n$. The comparisons on
morphisms are induced by actual tensor chain maps and inversion of quasi-isomorphisms.

4. For a $B_n$-module $F$, define $(E_nF)_q=F\otimes_{B_n}B_q$ for $q\leq n$ and zero for $q>n$,
with quotient-induced transitions. A map $h:F\to M_n$ extends uniquely to $E_nF\to M$: its
component at $q\leq n$ is $x\otimes a\mapsto a\,\tau_{nq}(h(x))$, and above $n$ the source is
zero. Balancing and the transition cocycle verify this formula; evaluating at $n$ recovers $h$.
This proves the natural adjunction $E_n\dashv e_n$ by the module tensor/restriction adjunction.
These formulas also commute with the Hom-complex differential $d(h)=d_Mh-(-1)^{|h|}hd_F$, giving
the adjunction on homotopy categories.

5. The additive functor $QE_n$ preserves shifts and cone matrices. Every complex over $B_n$ has a
flat-term K-flat resolution [lem-pc-kflat-resolution]. A quasi-isomorphism between such complexes
remains a quasi-isomorphism after each tensor $-\otimes_{B_n}B_q$ by
[lem-pur-derived-change-of-rings](1), and hence after $E_n$ by componentwise cohomology. The
resolving-class criterion [lem-pur-left-derived-from-kflat-class] gives an everywhere-defined
$L_n=LE_n$, computed by $E_nP$ on those representatives. By
[lem-weil-pbc-exact-functor-derived-functor], exact evaluation is its own everywhere-defined right
derived functor, so [lem-pc-derived-adjoint-functors] gives $L_n\dashv e_n$. In particular
$e_qL_nP=P\otimes^L_{B_n}B_q$ for $q\leq n$ and is zero otherwise. No coefficient-flatness
hypothesis entered this argument.

6. For $m\geq n$, put $T_{m,n}=-\otimes^L_{B_m}B_n$. There is a natural map
$\sigma_{mn}:L_nT_{m,n}\to L_m$: on a flat-term K-flat $P$ over $B_m$, its components are the
tensor rebracketing identity $P\otimes_{B_m}B_q$ for $q\leq n$ and the zero-source map for $q>n$.
K-flat pullback ensures the iterated tensors compute the displayed functors. Resolving-class
tensor descent makes this a transformation of functors on the derived categories. Both composites
for three indices have precisely the same components as chain maps on the same representative, so
they are equal after localization. The derived adjunction sends precomposition with $\sigma_{mn}$
to $h\mapsto t_{m,n}T_{m,n}(h)$: this is the tensor-adjoint formula $x\otimes a\mapsto
a\tau_{mn}h(x)$. It follows that the $t_{m,n}$ are natural and satisfy their cocycle.
Invertibility of adjacent reductions implies invertibility of all reductions by this cocycle and
preservation of isomorphisms by tensor; this proves the stated normalization criterion.

7. On any of the small ringed sites in use, define $H(M,N)$ by the K-injective construction
[def-pur-derived-internal-hom]; its independence is [lem-pur-rhom-well-defined]. The internal-Hom
identity of [lem-weil-pbc-ringed-internal-hom-exact-restriction] and the global-sections
identification of [lem-pur-rhom-global-sections] give $$\operatorname{Hom}(P,H(M,N))\cong
H^0R\Gamma H(P,H(M,N))\cong H^0R\Gamma H(P\otimes^LM,N)\cong\operatorname{Hom}(P\otimes^LM,N).$$
These bijections are natural. Hence they define the tensor-Hom adjunction and its evaluation on
the sequence site as well as on each level. This supplies the system internal Hom without trying
to assemble unrelated fiber objects.

8. Let $M$ be cartesian. There is a canonical system map $$L_n(P\otimes^L_{B_n}M_n)\cong
L_nP\otimes^L_{B_\bullet}L_nM_n\longrightarrow L_nP\otimes^L_{B_\bullet}M,$$ where the last arrow
uses the counit $L_ne_nM\to M$. For the first isomorphism take flat-term K-flat representatives
over $B_n$. Their $E_n$ extensions are K-flat with flat terms: below $n$ this is K-flat pullback,
above $n$ zero; componentwise exactness and tensor then test K-flatness of these particular
systems. The ordinary tensor rebracketing gives the isomorphism on these strict models and
descends by tensor descent. At $q\leq n$ the second arrow is $T_{n,q}P\otimes^L t^M_{n,q}$, which
is invertible by cartesianness, and above $n$ it is $0\to0$. Joint detection therefore makes the
displayed projection map an isomorphism of derived systems. This is a constructed map, not an
inference of equality from evaluations.

9. For every $P\in D(B_n)$, apply the adjunctions and the preceding projection isomorphism to
obtain
$$\operatorname{Hom}(P,e_nH_B(M,N))\cong\operatorname{Hom}(L_nP,H_B(M,N))\cong\operatorname{Hom}(L
_nP\otimes^LM,N)\cong\operatorname{Hom}(L_n(P\otimes^LM_n),N)\cong\operatorname{Hom}(P\otimes^LM_n
,N_n)\cong\operatorname{Hom}(P,H_{B_n}(M_n,N_n)).$$
Yoneda gives the claimed natural internal-Hom comparison. Its definition by these transposes
carries system evaluation to the fiber evaluation. Transpose the reduction transition of the
system evaluation map. Since $t^M_{m,n}$ is invertible, the resulting equation uniquely determines
the reduction of $H_B(M,N)$: it is exactly the transpose of the formula displayed in the
statement. The cocycle holds as an equation of system maps because evaluation and its adjunction
were constructed on the sequence site; alternatively its two transposes are the same
twice-reassociated evaluation followed by the transition of $N$, by the tensor associators. The
inverse cartesian comparison is essential here. -/
theorem semilinearSystemData : Nonempty (SemilinearSystemData.{c, v, r} J₀ B₀ τ₀) := by
  obtain ⟨S⟩ := systemScalarCoherence_nonempty.{c, v, r} J₀ B₀ τ₀
  obtain ⟨T⟩ := systemTensorCoherence_nonempty.{c, v, r} J₀ B₀ τ₀ S
  obtain ⟨H⟩ := systemCartesianHomEvaluation_nonempty.{c, v, r} J₀ B₀ τ₀ S T
  let A : Data.{c, v, r} J₀ B₀ τ₀ := {
    grothendieck := systemsGrothendieck.{c, v, r} J₀ B₀ τ₀
    componentwise := systemsComponentwise.{c, v, r} J₀ B₀ τ₀
    evaluation_triangulated := evaluationTriangulated.{c, v, r} J₀ B₀ τ₀
    detects := derivedEvaluationDetects.{c, v, r} J₀ B₀ τ₀
    scalar := S.scalar
    scalarComposition := S.scalarComposition
    scalarComposition_transpose := S.scalarComposition_transpose
    reduction_cocycle := S.reduction_cocycle
    closed := T.closed
    tensorModels := T.tensorModels
    levelClosed := T.levelClosed
    levelTensorModels := T.levelTensorModels
    tensorEvaluation := T.tensorEvaluation
    tensorEvaluationModel := T.tensorEvaluationModel
    tensorEvaluationModel_ordinary := T.tensorEvaluationModel_ordinary
    scalarTensor := T.scalarTensor
    scalarTensorModel := T.scalarTensorModel
    homEvaluation := H.homEvaluation
    homEvaluation_evaluation := H.homEvaluation_evaluation }
  exact ⟨⟨A, homReductionFormula.{c, v, r} J₀ B₀ τ₀ A T.reduction_tensor,
    T.tensorNormalization⟩⟩

end WeilConjectures.SemilinearSections
