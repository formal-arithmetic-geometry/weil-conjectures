module

public import Sheaf.Paper.CompactSupportScalarShiftStructures
import Sheaf.Paper.OriginalScalarMateShift
import Sheaf.Paper.StrictScalarMateShift
import Sheaf.Paper.ScalarLimitConstraintShift
import Sheaf.Paper.CompactSupportScalarShiftWitness

/-! # Canonical shifts of scalar compact-support comparison maps

Source: Stacks 05SU, 06YU, 0B56, 0941 and 03DJ; auxiliary comparison Steps 12--13
(blueprint: lem-pur-compact-support-scalar-shift-normalization).
The data helpers expose canonical shifts of existing functors. The theorem retains
proper/open, strict-tower, signed Roos, and completed total-limit equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
private theorem shiftStructureExt {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D) (s t : G.CommShift ℤ)
    (h : ∀ r : ℤ, Functor.commShiftIso G (self := s) r =
      Functor.commShiftIso G (self := t) r) : s = t := by
  cases s with
  | mk si sz sa =>
    cases t with
    | mk ti tz ta =>
      have hh : si = ti := funext h
      subst ti
      rfl

private theorem localizedShiftUnique
    {C D V : Type*} [Category C] [Category D] [Category V]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift V ℤ]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (G : D ⥤ V) (H : C ⥤ V)
    [L.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (e : L ⋙ G ≅ H) [NatTrans.CommShift e.hom ℤ] :
    ∃! s : G.CommShift ℤ, letI := s; NatTrans.CommShift e.hom ℤ := by
  let s : G.CommShift ℤ := inferInstance
  refine ⟨s, inferInstance, ?_⟩
  intro t ht
  apply shiftStructureExt G t s
  intro r
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro P
  have square (q : G.CommShift ℤ)
      (hq : letI := q; NatTrans.CommShift e.hom ℤ) :
      G.map ((L.commShiftIso r).hom.app P) ≫
        (Functor.commShiftIso G (self := q) r).hom.app (L.obj P) ≫
        (e.hom.app P)⟦r⟧' =
      e.hom.app (P⟦r⟧) ≫ (H.commShiftIso r).hom.app P := by
    let := q
    have := hq
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm e.hom r P
  apply (cancel_epi (G.map ((L.commShiftIso r).hom.app P))).1
  apply (cancel_mono ((e.hom.app P)⟦r⟧')).1
  simpa only [Category.assoc] using (square t ht).trans (square s inferInstance).symm

private theorem tensorShiftUnique (W : Scheme.{u}) :
    ∃! s : (tensor l E F i W).mapDerivedCategory.CommShift ℤ,
      letI := s
      NatTrans.CommShift (tensor l E F i W).mapDerivedCategoryFactors.hom ℤ := by
  exact localizedShiftUnique DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (tensor l E F i W).mapDerivedCategory
    ((tensor l E F i W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (tensor l E F i W).mapDerivedCategoryFactors

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- Canonical shifts of the actual scalar proper/open mates and scalar-limit maps.
Source: Stacks 05SU, 06YU, 0B56, 0941 and 03DJ; returned comparison Steps 12--13
(blueprint: lem-pur-compact-support-scalar-shift-normalization).

Proof:
1. Use lem-pur-derived-change-of-rings and
lem-pur-right-kan-extension-coherent-shift. The degree-zero scalar tensor commutes
with shifts termwise. Postcomposition by the shift equivalence preserves the Kan
bijection; its injectivity gives uniqueness of counit-normalized coherent shifts.
2. The balanced pullback/scalar comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback commutes with shifts on K-flat
models: both routes give the same balanced tensor. In the normalized constraints
of lem-pur-derived-tensor-additive-constraints the coefficient degree is zero,
so the first-variable sign is one. Resolving localization gives the actual square.
3. By lem-weil-pbc-derived-adjunction-shift the counit commutes with every integer
shift. Thus the geometric transpose of the proper mate shifts to itself.
Injectivity of the adjunction Hom bijection gives the proper square. Apply this
on the original sites and on the diagram sites of
lem-weil-pbc-diagram-site-realization, before evaluating any level.
4. Exact open extension has its degreewise shift. On the presheaf generator
indexed by V to X both routes send x tensor b to that same indexed tensor.
Sheafification preserves the equality; both differentials acquire (-1)^r.
This commutes with all diagram arrows and quotient transitions.
5. Whisker the open square by proper image and compose with the proper square.
lem-weil-pbc-commshift-nattrans-comp-whisker gives the square for the actual arrow
of lem-pur-compact-support-strict-scalar-mate. Arithmetic selection only reindexes
terms and composes transitions. The native reduction adjunction fixes its shift.
6. Apply total derived inverse limit using
lem-weil-pbc-ringed-strict-tower-homotopy-limit. K-injective shifts are still
K-injective by lem-weil-pbc-kinjective-shift. Exact countable products and
lem-sf-strict-roos-derived-limit-comparison identify the canonical shift with the
Roos shift: the resolution arrow is diagonal and the augmentation's extra
coordinate is zero. Use lem-weil-roos-comm-shift for the cone sign.
7. In lem-pur-compact-support-roos-cofinality, selection and the block sum commute
with shifts termwise. The extra Roos coordinate carries the same (-1)^r on
both routes. The finite-free tensor/product map commutes by its projections
(lem-weil-product-comm-shift). Invert the cofinal square to obtain the inverse's
square; these are the actual factors of scalarLimitArrow.
8. On a K-flat model the actual chi of
lem-weil-finite-free-completed-scalar-comparison has quotient-product coordinate
and zero extra coordinate. lem-weil-completed-scalar-chain-shift gives its signed
chain square, including the cone sign. The counit-normalized ordinary shift and
the normalized strict descent in lem-weil-integral-scalar-extension-well-defined
identify the descended square with that of this very chi.
9. Use the exact factorization of
lem-pur-compact-support-scalar-limit-reduction. Constant/completed transport of
lem-weil-pbc-constant-completion-equivalence commutes with shifts; full
faithfulness fixes the inverse comparison by its unit and counit. Compose the
three squares for tau, R(q) and inverse cofinal restriction. The intermediate
shift maps cancel, giving the displayed gamma equation. Every factor has coherent
integer shifts, so the same equation holds for zero and negative shifts too. -/
theorem compactSupportScalarShiftNormalization (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) :
    OriginalMateShift (PurCompactSupport.completedChange l E F i) c ∧
    (∀ n : ℕ, OriginalMateShift
      (PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)) c) ∧
    NatTrans.CommShift (proper l E F i c.g) ℤ ∧
    NatTrans.CommShift (openTensor l E F i c.i) ℤ ∧
    NatTrans.CommShift (strictScalarPull l E F i c.g).inv ℤ ∧
    NatTrans.CommShift
      (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c.g).counit ℤ ∧
    (∀ W : Scheme.{u}, ∃! s :
      (pbcDerivedExtend (completedCoefficientMap l E F i W)).CommShift ℤ,
      PurCompactSupport.IsScalarShiftNormalized (completedCoefficientMap l E F i W) s) ∧
    (∀ (W : Scheme.{u}) (n : ℕ), ∃! s :
      (pbcDerivedExtend ((PurCompactSupport.finiteChange l E F i e he hepos
        (n + 1) (Nat.le_add_left 1 n)).map W)).CommShift ℤ,
      PurCompactSupport.IsScalarShiftNormalized
        ((PurCompactSupport.finiteChange l E F i e he hepos
          (n + 1) (Nat.le_add_left 1 n)).map W) s) ∧
    (∀ W : Scheme.{u}, ∃! s : (tensor l E F i W).mapDerivedCategory.CommShift ℤ,
      letI := s
      NatTrans.CommShift (tensor l E F i W).mapDerivedCategoryFactors.hom ℤ) ∧
    @NatTrans.CommShift _ _ _ _ _ _ (scalarCompletion l E F i Y).hom ℤ _ _ _
      inferInstance (scalarCompletionTargetCommShift l E F i Y) ∧
    NatTrans.CommShift (scalarLimitTensor l E F i Y).hom ℤ ∧
    NatTrans.CommShift (scalarLimitRestriction l F Y e) ℤ ∧
    ∃ γ : (finiteTorConstructibleIntegral l E X).ι ⋙ scalarSupport l E c S ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y) ⟶
      (finiteTorConstructibleIntegral l E X).ι ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙ scalarSupport l F c S',
      ∀ M : finiteTorConstructibleIntegralCategory l E X,
        ((baseTensor l E F i Y).map
            ((scalarSupportLimit l E c S).hom.app M.obj) ≫
          scalarLimitArrow l E F i c S S' e he hepos M.obj =
        (scalarCompletion l E F i Y).hom.app ((scalarSupport l E c S).obj M.obj) ≫
          (scalarConstantRestriction l F Y).map (γ.app M) ≫
          (scalarSupportLimit l F c S').hom.app
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M.obj)) ∧
      (∀ r : ℤ, ∃ hMr : finiteTorConstructibleIntegral l E X (M.obj⟦r⟧),
        (arrow l E F i c S S' e he hepos).app (M.obj⟦r⟧) ≫
            ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
              support l F c S' ⋙ subsequence l F Y e).commShiftIso r).hom.app M.obj =
          ((support l E c S ⋙ T l E F i Y).commShiftIso r).hom.app M.obj ≫
            ((arrow l E F i c S S' e he hepos).app M.obj)⟦r⟧' ∧
        scalarLimitArrow l E F i c S S' e he hepos (M.obj⟦r⟧) ≫
            ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
              support l F c S' ⋙ scalarLimit l F Y).commShiftIso r).hom.app M.obj =
          ((support l E c S ⋙ scalarLimit l E Y ⋙
              baseTensor l E F i Y).commShiftIso r).hom.app M.obj ≫
            (scalarLimitArrow l E F i c S S' e he hepos M.obj)⟦r⟧' ∧
        γ.app ⟨M.obj⟦r⟧, hMr⟩ ≫
            ((pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
              scalarSupport l F c S').commShiftIso r).hom.app M.obj =
          ((scalarSupport l E c S ⋙
            pbcDerivedExtend (completedCoefficientMap l E F i Y)).commShiftIso r).hom.app
              M.obj ≫ (γ.app M)⟦r⟧') := by
  have hm := strictScalarMateShift l E F i c S S' e he hepos
  have hc := scalarLimitConstraintShift l E F i c S e
  have hc' := scalarLimitConstraintShift l F F (AlgHom.id ℚ_[l] F) c S' e
  refine ⟨originalScalarMateShift _ c, fun n ↦ originalScalarMateShift _ c,
    hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1,
    fun W ↦ PurCompactSupport.scalarCommShift_existsUnique _,
    fun W n ↦ PurCompactSupport.scalarCommShift_existsUnique _,
    tensorShiftUnique l E F i, hc.1, hc.2.1, hc'.2.2.1, ?_⟩
  obtain ⟨γ, hγ⟩ := compactSupportScalarShiftWitness l E F i D hl f c S S' e he hepos
  have := hm.2.2.2.2
  refine ⟨γ, fun M ↦ ⟨(hγ M).1, fun r ↦ ?_⟩⟩
  obtain ⟨hMr, h⟩ := (hγ M).2 r
  exact ⟨hMr, (NatTrans.shift_app_comm (arrow l E F i c S S' e he hepos) r M.obj).symm,
    hc.2.2.2.2 S' he hepos M.obj r, h⟩

end Geometry
end WeilConjectures.PurStrictScalar
