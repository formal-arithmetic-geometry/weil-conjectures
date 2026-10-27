/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.CompactSupportTermHomFinite
import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-! # Canonical constructible exceptional composition

Source: blueprint main-20261015, Verdier exchange, proof Step 1
(blueprint: def-sf-constructible-exceptional-compositor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- Change from the finite tensor-pullback presentation to the published fixed-scalar
one, preserving the ordinary units. The coefficient-identification transport has
identity hom. Source: blueprint finite exceptional adjunction
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def constructibleFinitePullIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingModulePullback f
        ((PurCompactSupport.finite l E n n.pos).ring Y)
        ((PurCompactSupport.finite l E n n.pos).ring X)
        ((PurCompactSupport.finite l E n n.pos).pull f) ≅
      @sfIntrinsicPullback (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  eqToIso (congrArg
      (fun e ↦ proEtaleRingModulePullback f
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) e)
      (Iso.ext (by rfl) :
        @sfConstantCoefficientIso X Y f (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos) =
        proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E n))) ≪≫
    @openSquarePullbackModel (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n n.pos) X Y f

/-- The finite proper/open presentations are compared by their unit-normalized
adjunctions, then by termwise and K-injective descent.
Source: blueprint finite exceptional adjunction, ordinary open-extension comparison
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def constructibleFiniteImageIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    PurCompactSupport.image (PurCompactSupport.finite l E n n.pos) c ≅
      @sfIntrinsicCompactSupport X Y f c (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n n.pos) :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n n.pos
  letI : IsOpenImmersion c.i := c.isOpenImmersion
  letI : (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)).Additive :=
    sfIntrinsicExtensionByZero_additive c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteLimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteLimits c.i (Padic.coefficientExtensionRing l E n)
  letI : Limits.PreservesFiniteColimits
      (sfIntrinsicExtensionByZero c.i (Padic.coefficientExtensionRing l E n)) :=
    sfIntrinsicExtensionByZero_preservesFiniteColimits c.i (Padic.coefficientExtensionRing l E n)
  letI : (proEtaleConstantModuleDirectImage c.g
      (Padic.coefficientExtensionRing l E n)).Additive :=
    proEtaleConstantModuleDirectImage_additive c.g (Padic.coefficientExtensionRing l E n)
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (((PurCompactSupport.openAdjunction
          (PurCompactSupport.finite l E n n.pos) c.i).ofNatIsoRight
            (constructibleFinitePullIso l E n c.i)).leftAdjointUniq
          (@sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos) X c.Z c.i
            c.isOpenImmersion))) _ ≪≫
  Functor.isoWhiskerLeft _
    (Functor.rightDerivedFunctorNatIso
      (((proEtaleRingModuleAdjunction c.g
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))
          (proEtaleConstantRing c.Z (Padic.coefficientExtensionRing l E n))
          (@sfConstantCoefficientIso c.Z Y c.g (Padic.coefficientExtensionRing l E n) _
            (Padic.finite_coefficientExtensionRing l E n n.pos))).ofNatIsoLeft
              (constructibleFinitePullIso l E n c.g)).rightAdjointUniq
        (@sfIntrinsicConstantModuleAdjunction c.Z Y c.g
          (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n n.pos))))

private theorem derivedLimit_hom_ext_of_finite
    {T : Type*} [Category T] [CategoryTheory.Limits.HasZeroObject T] [HasShift T ℤ]
    [Preadditive T] [∀ m : ℤ, (shiftFunctor T m).Additive] [Pretriangulated T]
    (V : ℕ → T) [CategoryTheory.Limits.HasProduct V]
    (v : ∀ n, V (n + 1) ⟶ V n) (Q : T)
    (q : Q ⟶ CategoryTheory.Limits.piObj V)
    (d : CategoryTheory.Limits.piObj V ⟶ Q⟦(1 : ℤ)⟧)
    (hQ : IsDerivedLimitTriangle v Q q d) (P : T)
    (hfinite : ∀ n, Finite (P⟦(1 : ℤ)⟧ ⟶ V n))
    (a b : P ⟶ Q)
    (hab : ∀ n, a ≫ q ≫ CategoryTheory.Limits.Pi.π V n =
      b ≫ q ≫ CategoryTheory.Limits.Pi.π V n) : a = b := by
  let S := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism v) d
  have hS : S ∈ Pretriangulated.distinguishedTriangles := hQ
  have hvd : towerTransitionEndomorphism v ≫ d = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₂₃ S hS
  have hq : (a - b) ≫ q = 0 := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro n
    simp only [Preadditive.sub_comp, Category.assoc, CategoryTheory.Limits.zero_comp]
    exact sub_eq_zero.mpr (hab n)
  obtain ⟨u, hu⟩ := Pretriangulated.Triangle.coyoneda_exact₁ S hS
    ((a - b)⟦(1 : ℤ)⟧') (by
      simp only [S, Pretriangulated.Triangle.mk_mor₁, ← Functor.map_comp,
        hq, Functor.map_zero])
  dsimp only [S, Pretriangulated.Triangle.mk] at u hu
  let (n : ℕ) : Finite (P⟦(1 : ℤ)⟧ ⟶ V n) := hfinite n
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun n ↦ P⟦(1 : ℤ)⟧ ⟶ V n)
    (fun n ↦ Preadditive.rightComp _ (v n))
    (fun n ↦ u ≫ CategoryTheory.Limits.Pi.π V n)
  have huw : u = CategoryTheory.Limits.Pi.lift w ≫ towerTransitionEndomorphism v := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Category.assoc, Preadditive.rightComp] using (hw n).symm
  apply sub_eq_zero.mp
  apply (shiftFunctor T (1 : ℤ)).map_eq_zero_iff.mp
  rw [hu, huw, Category.assoc, hvd, CategoryTheory.Limits.comp_zero]

private theorem normalizedProjection_functor_ext
    {A C T : Type*} [Category A] [Category C] [Category T]
    (i : C ⥤ T) [i.Faithful] (F G : A ⥤ C) (V : A → C)
    (L : ℕ → A ⥤ T) (p : ∀ K n, i.obj (V K) ⟶ (L n).obj K)
    (hF : ∀ K, F.obj K = V K) (hG : ∀ K, G.obj K = V K)
    (qF : ∀ n, F ⋙ i ⟶ L n) (qG : ∀ n, G ⋙ i ⟶ L n)
    (hqF : ∀ K n, HEq ((qF n).app K) (p K n))
    (hqG : ∀ K n, HEq ((qG n).app K) (p K n))
    (hp : ∀ K K' (a b : i.obj (V K) ⟶ i.obj (V K')),
      (∀ n, a ≫ p K' n = b ≫ p K' n) → a = b) : F = G := by
  have hnorm {W W' Z : T} (e : W = W') (a : W ⟶ Z) (b : W' ⟶ Z)
      (h : HEq a b) : a = eqToHom e ≫ b := by
    subst W'
    simpa using eq_of_heq h
  have hmap {W W' : C} (e : W = W') :
      i.map (eqToHom e) = eqToHom (congrArg i.obj e) := by
    subst W'
    exact i.map_id _
  have hqF' (K : A) (n : ℕ) :
      (qF n).app K = i.map (eqToHom (hF K)) ≫ p K n := by
    simpa only [hmap] using hnorm (congrArg i.obj (hF K)) _ _ (hqF K n)
  have hqG' (K : A) (n : ℕ) :
      (qG n).app K = i.map (eqToHom (hG K)) ≫ p K n := by
    simpa only [hmap] using hnorm (congrArg i.obj (hG K)) _ _ (hqG K n)
  let F' := F.copyObj V (fun K ↦ eqToIso (hF K))
  let G' := G.copyObj V (fun K ↦ eqToIso (hG K))
  have hcopy (J : A ⥤ C) (hJ : ∀ K, J.obj K = V K) :
      J.copyObj V (fun K ↦ eqToIso (hJ K)) = J := by
    apply Functor.hext (fun K ↦ (hJ K).symm)
    intro K K' f
    dsimp only [Functor.copyObj, eqToIso.hom, eqToIso.inv]
    exact (eqToHom_comp_heq _ (hJ K).symm).trans (comp_eqToHom_heq _ (hJ K'))
  have hFG : F' = G' := by
    refine CategoryTheory.Functor.ext (F := F') (G := G') (fun _ ↦ rfl) ?_
    intro K K' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply i.map_injective
    apply hp K K'
    intro n
    have hf := (qF n).naturality f
    have hg := (qG n).naturality f
    rw [hqF', hqF'] at hf
    rw [hqG', hqG'] at hg
    simp only [Functor.comp_map] at hf hg
    have hf' := congrArg (fun z ↦ i.map (eqToHom (hF K).symm) ≫ z) hf
    have hg' := congrArg (fun z ↦ i.map (eqToHom (hG K).symm) ≫ z) hg
    simp only [← Category.assoc, ← Functor.map_comp, eqToHom_trans,
      eqToHom_refl] at hf' hg'
    rw [i.map_id, Category.id_comp] at hf' hg'
    simp only [Category.assoc] at hf' hg'
    apply Eq.trans (b := p K n ≫ (L n).map f)
    · simpa only [F', Functor.copyObj, eqToIso.hom, eqToIso.inv] using hf'
    · symm
      simpa only [G', Functor.copyObj, eqToIso.hom, eqToIso.inv] using hg'
  exact (hcopy F hF).symm.trans (hFG.trans (hcopy G hG))

private theorem projections_from_realization
    {A C T U : Type*} [Category A] [Category C] [Category T] [Category U]
    {i : A ⥤ C} {F : A ⥤ U} {tower : C ⥤ T} {limit : T ⥤ U}
    {eval : ℕ → T ⥤ U} {L : ℕ → C ⥤ U}
    {e : ∀ n, tower ⋙ eval n ≅ L n}
    {π : ∀ n, limit ⟶ eval n}
    {V : A → U} {p : ∀ K n, V K ⟶ (L n).obj (i.obj K)}
    (γ : F ≅ i ⋙ tower ⋙ limit)
    (hγ : ∀ K n, HEq (γ.hom.app K ≫ (π n).app (tower.obj (i.obj K)) ≫
        (e n).hom.app (i.obj K)) (p K n)) :
    ∃ q : ∀ n, F ⟶ i ⋙ L n, ∀ K n, HEq ((q n).app K) (p K n) := by
  refine ⟨fun n ↦ γ.hom ≫ Functor.whiskerLeft i
    (Functor.whiskerLeft tower (π n) ≫ (e n).hom), ?_⟩
  intro K n
  exact hγ K n

attribute [local irreducible] sfCompactSupportTransition
  sfIntegralCompactSupportValue in
set_option backward.isDefEq.respectTransparency true in
private theorem finiteIntegralFunctor_projections
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (hF : SfCompactSupportFiniteRealizationSpec l K₀ hl c E F) :
    letI := integralOperationsDerivedCountableProducts l E Y
    ∃ q : ∀ n : ℕ,
      F ⋙
          (sfIntegralConstructible l E Y).ι ⟶
        (sfIntegralConstructible l E X).ι ⋙
          compactSupportRestrictedLevel l E c n,
      ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
        HEq ((q n).app K)
          (Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
            (sfCompactSupportTerm l E c K.obj)
            (sfCompactSupportTransition l E c K.obj)).1) ≫
              CategoryTheory.Limits.Pi.π (sfCompactSupportTerm l E c K.obj) n) := by
  letI := integralOperationsDerivedCountableProducts l E Y
  obtain ⟨_, _, _, ⟨delta, hdelta⟩, _⟩ := hF
  -- Extract the recorded functors without re-elaborating their nested choice terms.
  -- The generated term is an application of the proved generic projection lemma.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let some gd := ctx.findFromUserName? `delta | throwError "missing comparison"
    let some hd := ctx.findFromUserName? `hdelta | throwError "missing normalization"
    let gamma := gd.toExpr
    let hgamma := hd.toExpr
    Lean.Meta.forallTelescopeReducing (← Lean.Meta.inferType hgamma) fun vars raw ↦ do
      let body := raw.consumeMData
      let args := body.getAppArgs
      unless args.size == 4 do
        throwError "expected HEq with four arguments, got {body.getAppFn}, {args.size}"
      let p ← Lean.Meta.mkLambdaFVars vars args[3]!
      let rhsType := args[2]!.getAppArgs
      let v ← Lean.Meta.mkLambdaFVars #[vars[0]!] rhsType[rhsType.size - 2]!
      let gt := (← Lean.Meta.inferType gamma).getAppArgs
      let f := gt[gt.size - 2]!
      let target := gt[gt.size - 1]!.getAppArgs
      let i := target[target.size - 2]!
      let composite := target[target.size - 1]!.getAppArgs
      let tower := composite[composite.size - 2]!
      let limit := composite[composite.size - 1]!
      let lhs := args[1]!.consumeMData
      let outer := lhs.getAppArgs
      unless outer.size ≥ 2 do
        throwError "expected composite, got {lhs.getAppFn}, {outer.size}"
      let rest := outer[outer.size - 1]!.consumeMData
      let inner := rest.getAppArgs
      unless inner.size ≥ 2 do
        throwError "expected second composite, got {rest.getAppFn}, {inner.size}"
      let b := inner[inner.size - 2]!.consumeMData
      let c := inner[inner.size - 1]!.consumeMData
      unless b.getAppArgs.size ≥ 2 && c.getAppArgs.size ≥ 2 do
        throwError "expected components, got {b.getAppFn}, {c.getAppFn}"
      let bn := b.getAppArgs[b.getAppArgs.size - 2]!.consumeMData
      let cn := c.getAppArgs[c.getAppArgs.size - 2]!.consumeMData
      unless cn.getAppArgs.size > 0 do
        throwError "expected evaluation hom, got {cn.getAppFn}"
      let e := cn.getAppArgs[cn.getAppArgs.size - 1]!.appFn!
      let pi := bn.appFn!
      let et := (← Lean.Meta.inferType cn.getAppArgs[cn.getAppArgs.size - 1]!).getAppArgs
      let left := et[et.size - 2]!.getAppArgs
      let eval := left[left.size - 1]!.appFn!
      let levels := et[et.size - 1]!.appFn!
      let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo
        (Lean.mkIdent `projections_from_realization)
      let it := (← Lean.Meta.inferType i).getAppArgs
      let tt := (← Lean.Meta.inferType tower).getAppArgs
      let lt := (← Lean.Meta.inferType limit).getAppArgs
      let proof ← Lean.Meta.withTransparency .all <| Lean.Meta.mkAppOptM name
        #[some it[0]!, some it[2]!, some tt[2]!, some lt[2]!,
        some it[1]!, some it[3]!, some tt[3]!, some lt[3]!,
        some i, some f, some tower, some limit,
        some eval, some levels, some e, some pi, some v, some p,
        some gamma, some hgamma]
      (← Lean.Elab.Tactic.getMainGoal).assign proof
      Lean.Elab.Tactic.replaceMainGoal []

/-- The operation datum's integral support is the specified normalized realization.
Source: blueprint exceptional adjunction, integral construction, and the operation
normalizations (blueprint: def-sf-constructible-exceptional-compositor-data).

Proof:
1. Project supportConstruction from S.higher and the realization specification of
   sfCompactSupportFiniteIntegralFunctor. Their object-normalization clauses give
   the same sfIntegralCompactSupportValue, so first transport to these fixed objects.
2. For a morphism v, naturality of the two strict-tower comparisons and their
   projection normalizations identify the composites of both image maps with every
   fixed Roos projection. The finite maps are the same proper/open reduction maps.
3. To deduce equality of the image maps, apply the Milnor exact sequence for maps
   into the total derived inverse limit. Its kernel is lim^1 of the degree-minus-one
   Hom tower. Reduction adjunction identifies these Hom groups with finite-level
   constructible Ext groups. They are finite by constructible etale finiteness over
   the algebraically closed finite-field base, using etale origin and the common
   bounded constructible intervals. An inverse sequence of finite groups is
   Mittag-Leffler: in each finite target its descending images stabilize. Hence this
   lim^1 vanishes. Equality of the fixed projection composites now implies equality
   of maps into this total limit. This uses finiteness, not faithfulness of finite
   evaluation on arbitrary derived systems.
4. The full-subcategory inclusion is faithful. Apply functor extensionality to the
   object equalities and transported map equalities; proof irrelevance identifies
   the constructibility witnesses. This proves equality of the normalized functors,
   so eqToIso below is the identity transport of their common normalization. -/
theorem constructibleIntegralSupport_eq
    (D : FiniteFieldDatum.{u}) (B : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic B.l) E]
    [FiniteDimensional (Padic B.l) E] (n : ℕ+) (S : SixFunctorOperationDatum D B E n n.pos)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    S.higher.integral.support f c =
      sfCompactSupportFiniteIntegralFunctor B.l D.k
        (PurCompactSupport.coefficientPrimeUnit B.l D B.different) c E := by
  letI := integralOperationsDerivedCountableProducts B.l E Y.obj.left
  let hl := PurCompactSupport.coefficientPrimeUnit B.l D B.different
  let iX := (sfIntegralConstructible B.l E X.obj.left).ι
  let iY := (sfIntegralConstructible B.l E Y.obj.left).ι
  let F := S.higher.integral.support f c
  let G := sfCompactSupportFiniteIntegralFunctor B.l D.k hl c E
  let V := sfIntegralCompactSupportValue B.l E D.k hl c
  let L (n : ℕ) := iX ⋙ compactSupportRestrictedLevel B.l E c n
  let p (K : sfIntegralConstructibleCategory B.l E X.obj.left) (n : ℕ) :=
    Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
      (sfCompactSupportTerm B.l E c K.obj)
      (sfCompactSupportTransition B.l E c K.obj)).1) ≫
        CategoryTheory.Limits.Pi.π (sfCompactSupportTerm B.l E c K.obj) n
  obtain ⟨T, _, _, hF, gamma, hgamma, _⟩ := S.higher.supportConstruction f hl c
  let qF (n : ℕ) : F ⋙ iY ⟶ L n :=
    gamma.hom ≫ Functor.whiskerLeft iX
      (Functor.whiskerLeft T.tower (T.projections n) ≫ (T.evaluations n).hom)
  have hG : SfCompactSupportFiniteRealizationSpec B.l D.k hl c E G := by
    dsimp only [G]
    delta sfCompactSupportFiniteIntegralFunctor
    exact (sfCompactSupportFiniteRealization B.l D.k hl c E).choose_spec
  obtain ⟨qG, hdelta⟩ := finiteIntegralFunctor_projections B.l E D.k hl c G hG
  apply normalizedProjection_functor_ext iY F G V L p hF
    (sfCompactSupportFiniteIntegralFunctor_obj B.l D.k hl c E) qF qG hgamma hdelta
  intro K K' a b hab
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm B.l E c K'.obj)
    (sfCompactSupportTransition B.l E c K'.obj)).1
  let hm := Classical.choose_spec h
  exact derivedLimit_hom_ext_of_finite _ _ _ (Classical.choose hm)
    (Classical.choose (Classical.choose_spec hm))
    (Classical.choose_spec (Classical.choose_spec hm)) _
    (compactSupportTerm_hom_finite D B E f c (V K) K') a b hab


end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The existing finite-Tor full subcategory included in the constructible category.
Source: blueprint finite-Tor convention
(blueprint: def-sf-finite-exceptional-compositor-maps). -/
def finiteInclusion (E : FieldStage.{u} B.l) (n : ℕ+) (X : SixFunctorSpace D) :
    C.{u, u} B.l B.Qbar X.obj.left (.finite E n) ⥤
      sixFunctorFiniteCategory D B E.carrier n n.pos X :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

/-- Integral inclusion is the dependency's recorded inclusion.
Source: blueprint completed finite-Tor convention
(blueprint: def-sf-exceptional-compositor-coefficient-data). -/
abbrev integralInclusion (E : FieldStage.{u} B.l) (X : SixFunctorSpace D) :=
  PurCompactSupport.finiteTorIntegralInclusion B.l E.carrier X.obj.left

section OneArrow
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))

/-- The finite comparison is the unique lift of the two specified ambient realizations.
No new comparison map is chosen. Source: blueprint compact-support restriction
(blueprint: def-sf-finite-exceptional-compositor-maps). -/
def finiteLeft (E : FieldStage.{u} B.l) (n : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos) (c : Compactification f.hom.left) :
    (P.ring.operation c (.finite E n)).F ⋙ finiteInclusion B E n Y ≅
      finiteInclusion B E n X ⋙ S.finite.support f c :=
  ((intrinsicFiniteTorsionConstructible B.l E.carrier n n.pos
    Y.obj.left).fullyFaithfulι.whiskeringRight _).preimageIso
    (X := (P.ring.operation c (.finite E n)).F ⋙ finiteInclusion B E n Y)
    (Y := finiteInclusion B E n X ⋙ S.finite.support f c)
    (P.ring.left c (.finite E n) ≪≫
      Functor.isoWhiskerLeft _ (constructibleFiniteImageIso B.l E.carrier n c) ≪≫
      (Functor.isoWhiskerLeft (finiteInclusion B E n X) (S.finiteSupport f c)).symm)

/-- The integral comparison is fixed by the normalized integral realization, and the
identity transport between the two presentations of that same realization.
Source: blueprint completed support construction
(blueprint: def-sf-exceptional-compositor-coefficient-data). -/
def integralLeft (E : FieldStage.{u} B.l)
    (S : SixFunctorOperationDatum D B E.carrier 1 (by decide))
    (c : Compactification f.hom.left) :
    (P.ring.operation c (.integral E)).F ⋙ integralInclusion B E Y ≅
      integralInclusion B E X ⋙ S.higher.integral.support f c :=
  P.ring.integralLeft c E ≪≫ Functor.isoWhiskerLeft (integralInclusion B E X)
    (eqToIso (constructibleIntegralSupport_eq D B E.carrier 1 S f c).symm)

end OneArrow

/-- The composite in the full over category has its original underlying scheme map.
Source: blueprint composable finite-type morphisms
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
instance separatedComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left] :
    IsSeparated (f ≫ g).hom.left :=
  inferInstanceAs (IsSeparated (f.hom.left ≫ g.hom.left))

/-- Finite type is stable under composition, with no new hypothesis.
Source: blueprint composable finite-type morphisms
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
instance lftComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f.hom.left] [LocallyOfFiniteType g.hom.left] :
    LocallyOfFiniteType (f ≫ g).hom.left :=
  inferInstanceAs (LocallyOfFiniteType (f.hom.left ≫ g.hom.left))

/-- Quasi-compactness is stable under composition, with no new hypothesis.
Source: blueprint composable finite-type morphisms
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
instance qcComp {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f.hom.left] [QuasiCompact g.hom.left] :
    QuasiCompact (f ≫ g).hom.left :=
  inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))

/-- The exact coefficient comparison equation for a left compositor. Its q maps
are the recorded coefficient maps, including their specified normalizations.
Source: blueprint completed/rational/common compact-support forms
(blueprint: def-sf-exceptional-compositor-coefficient-data). -/
def LeftCoefficientEquation {X Y Z : Scheme.{u}} {s t : Stage.{u} B.l}
    (A : Operation.{u, u} B.l B.Qbar X Y s) (A' : Operation.{u, u} B.l B.Qbar X Y t)
    (G : Operation.{u, u} B.l B.Qbar Y Z s) (G' : Operation.{u, u} B.l B.Qbar Y Z t)
    (H : Operation.{u, u} B.l B.Qbar X Z s) (H' : Operation.{u, u} B.l B.Qbar X Z t)
    (TX : C.{u, u} B.l B.Qbar X s ⥤ C.{u, u} B.l B.Qbar X t)
    (TY : C.{u, u} B.l B.Qbar Y s ⥤ C.{u, u} B.l B.Qbar Y t)
    (TZ : C.{u, u} B.l B.Qbar Z s ⥤ C.{u, u} B.l B.Qbar Z t)
    (qf : A.F ⋙ TY ≅ TX ⋙ A'.F) (qg : G.F ⋙ TZ ≅ TY ⋙ G'.F)
    (qx : H.F ⋙ TZ ≅ TX ⋙ H'.F)
    (alpha : A.F ⋙ G.F ≅ H.F) (alpha' : A'.F ⋙ G'.F ≅ H'.F) : Prop :=
  ∀ K : C.{u, u} B.l B.Qbar X s,
    TZ.map (alpha.hom.app K) ≫ qx.hom.app K =
      qg.hom.app (A.F.obj K) ≫ G'.F.map (qf.hom.app K) ≫ alpha'.hom.app (TX.obj K)

/-- The exceptional compositor is literally the conjugate of inverse alpha under
the composite constructible adjunction and the direct constructible adjunction.
Source: blueprint Verdier-exchange proof Step 1; Mathlib conjugateIsoEquiv
(blueprint: def-sf-finite-exceptional-compositor-maps). -/
def exceptionalIso {X Y Z : Scheme.{u}} {s : Stage.{u} B.l}
    (A : Operation.{u, u} B.l B.Qbar X Y s) (G : Operation.{u, u} B.l B.Qbar Y Z s)
    (H : Operation.{u, u} B.l B.Qbar X Z s) (alpha : A.F ⋙ G.F ≅ H.F) : G.G ⋙ A.G ≅ H.G :=
  conjugateIsoEquiv (A.adjunction.comp G.adjunction) H.adjunction alpha.symm

/-- Hom action, the pasted counit, componentwise uniqueness, and integer-shift
compatibility. Naturality and invertibility are already fields of exceptionalIso.
Source: blueprint Verdier-exchange proof Step 1, expanded mate calculation
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def MateProperties {X Y Z : Scheme.{u}} {s : Stage.{u} B.l}
    (A : Operation.{u, u} B.l B.Qbar X Y s) (G : Operation.{u, u} B.l B.Qbar Y Z s)
    (H : Operation.{u, u} B.l B.Qbar X Z s) (alpha : A.F ⋙ G.F ≅ H.F) : Prop :=
  (∀ (K : C.{u, u} B.l B.Qbar X s) (L : C.{u, u} B.l B.Qbar Z s) (u : K ⟶ (G.G ⋙ A.G).obj L),
    u ≫ (exceptionalIso B A G H alpha).hom.app L =
      H.adjunction.homEquiv K L
        (alpha.inv.app K ≫ ((A.adjunction.comp G.adjunction).homEquiv K L).symm u)) ∧
  (∀ L : C.{u, u} B.l B.Qbar Z s,
    alpha.hom.app ((G.G ⋙ A.G).obj L) ≫
        H.F.map ((exceptionalIso B A G H alpha).hom.app L) ≫ H.adjunction.counit.app L =
      G.F.map (A.adjunction.counit.app (G.G.obj L)) ≫ G.adjunction.counit.app L) ∧
  (∀ (L : C.{u, u} B.l B.Qbar Z s) (t : (G.G ⋙ A.G).obj L ⟶ H.G.obj L),
    (alpha.hom.app ((G.G ⋙ A.G).obj L) ≫ H.F.map t ≫ H.adjunction.counit.app L =
      G.F.map (A.adjunction.counit.app (G.G.obj L)) ≫ G.adjunction.counit.app L) ↔
        t = (exceptionalIso B A G H alpha).hom.app L) ∧
  alpha.hom.CommShift ℤ ∧ (exceptionalIso B A G H alpha).hom.CommShift ℤ

section TwoArrows
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))
  (Q : System.{u, u} B.l B.Qbar D B.different (f := g.hom.left))
  (R : System.{u, u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))

/-- Canonical finite compact-support composition, lifted from the published normalized
compactification compositor along the fully faithful finite-Tor inclusion.
Source: blueprint compact-support composition and its finite-Tor restriction
(blueprint: def-sf-finite-exceptional-compositor-maps). -/
def finiteAlpha (E : FieldStage.{u} B.l) (n : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left) :
    (P.ring.operation cf (.finite E n)).F ⋙ (Q.ring.operation cg (.finite E n)).F ≅
      (R.ring.operation cx (.finite E n)).F :=
  ((ObjectProperty.fullyFaithfulιOfLE
    (show finiteTorConstructible B.l E.carrier n n.pos Z.obj.left ≤
      intrinsicFiniteTorsionConstructible B.l E.carrier n n.pos Z.obj.left from
        fun _ h ↦ h.1)).whiskeringRight _).preimageIso
    (X := (P.ring.operation cf (.finite E n)).F ⋙ (Q.ring.operation cg (.finite E n)).F)
    (Y := (R.ring.operation cx (.finite E n)).F)
    (Functor.associator (P.ring.operation cf (.finite E n)).F
        (Q.ring.operation cg (.finite E n)).F (finiteInclusion B E n Z) ≪≫
      Functor.isoWhiskerLeft (P.ring.operation cf (.finite E n)).F
        (finiteLeft B g Q E n S cg) ≪≫
      (Functor.associator (P.ring.operation cf (.finite E n)).F
        (finiteInclusion B E n Y) (S.finite.support g cg)).symm ≪≫
      Functor.isoWhiskerRight (finiteLeft B f P E n S cf) (S.finite.support g cg) ≪≫
      Functor.associator (finiteInclusion B E n X)
        (S.finite.support f cf) (S.finite.support g cg) ≪≫
      Functor.isoWhiskerLeft (finiteInclusion B E n X) (S.finite.composition f g cf cg cx).symm ≪≫
      (finiteLeft B (f ≫ g) R E n S cx).symm)

/-- Canonical completed composition, transported through the specified integral
realizations and lifted through the full finite-Tor inclusion. Source: blueprint
completed support composition (blueprint: def-sf-exceptional-compositor-coefficient-data). -/
def integralAlpha (E : FieldStage.{u} B.l)
    (S : SixFunctorOperationDatum D B E.carrier 1 (by decide))
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left) :
    (P.ring.operation cf (.integral E)).F ⋙ (Q.ring.operation cg (.integral E)).F ≅
      (R.ring.operation cx (.integral E)).F :=
  ((ObjectProperty.fullyFaithfulιOfLE
    (show finiteTorConstructibleIntegral B.l E.carrier Z.obj.left ≤
      sfIntegralConstructible B.l E.carrier Z.obj.left from
        fun _ h ↦ h.1)).whiskeringRight _).preimageIso
    (X := (P.ring.operation cf (.integral E)).F ⋙ (Q.ring.operation cg (.integral E)).F)
    (Y := (R.ring.operation cx (.integral E)).F)
    (Functor.associator (P.ring.operation cf (.integral E)).F
        (Q.ring.operation cg (.integral E)).F (integralInclusion B E Z) ≪≫
      Functor.isoWhiskerLeft (P.ring.operation cf (.integral E)).F
        (integralLeft B g Q E S cg) ≪≫
      (Functor.associator (P.ring.operation cf (.integral E)).F
        (integralInclusion B E Y) (S.higher.integral.support g cg)).symm ≪≫
      Functor.isoWhiskerRight (integralLeft B f P E S cf) (S.higher.integral.support g cg) ≪≫
      Functor.associator (integralInclusion B E X)
        (S.higher.integral.support f cf) (S.higher.integral.support g cg) ≪≫
      Functor.isoWhiskerLeft (integralInclusion B E X)
        (S.higher.integral.composition f g cf cg cx).symm ≪≫
      (integralLeft B (f ≫ g) R E S cx).symm)

/-- The canonical left maps at all four coefficient stages. The finite and integral
maps equal the published compactification maps lifted above, and the field maps
satisfy their actual localization and common-stage component equations. Thus no
unconstrained isomorphism between left adjoints is supplied here.
Source: blueprint Verdier-exchange Step 1, coefficient conventions
(blueprint: def-sf-exceptional-compositor-coefficient-data). -/
structure LeftCompositors
    (S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos) where
  alpha (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (s : Stage.{u} B.l) :
    (P.ring.operation cf s).F ⋙ (Q.ring.operation cg s).F ≅ (R.ring.operation cx s).F
  finite (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) (n : ℕ+) :
    alpha cf cg cx (.finite E n) = finiteAlpha B f g P Q R E n (S E n) cf cg cx
  integral (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) :
    alpha cf cg cx (.integral E) = integralAlpha B f g P Q R E (S E 1) cf cg cx
  rational (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left) (E : FieldStage.{u} B.l) :
    LeftCoefficientEquation B
      (P.ring.operation cf (.integral E)) (P.ring.operation cf (.rational E))
      (Q.ring.operation cg (.integral E)) (Q.ring.operation cg (.rational E))
      (R.ring.operation cx (.integral E)) (R.ring.operation cx (.rational E))
      (rationalization B.l B.Qbar E X.obj.left)
      (rationalization B.l B.Qbar E Y.obj.left)
      (rationalization B.l B.Qbar E Z.obj.left)
      (P.fields.rationalizationComparison cf E).q
      (Q.fields.rationalizationComparison cg E).q
      (R.fields.rationalizationComparison cx E).q
      (alpha cf cg cx (.integral E)) (alpha cf cg cx (.rational E))
  common (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
      (cx : Compactification (f ≫ g).hom.left)
      (i : AlgebraicallyClosedCoefficients.Index B.l B.Qbar) :
    LeftCoefficientEquation B
      (P.ring.operation cf (.rational (commonField B.l B.Qbar i)))
      (P.ring.operation cf .closed)
      (Q.ring.operation cg (.rational (commonField B.l B.Qbar i)))
      (Q.ring.operation cg .closed)
      (R.ring.operation cx (.rational (commonField B.l B.Qbar i)))
      (R.ring.operation cx .closed)
      (commonInclusion B.l B.Qbar X.obj.left i)
      (commonInclusion B.l B.Qbar Y.obj.left i)
      (commonInclusion B.l B.Qbar Z.obj.left i)
      (P.common.commonComparison cf i).q (Q.common.commonComparison cg i).q
      (R.common.commonComparison cx i).q
      (alpha cf cg cx (.rational (commonField B.l B.Qbar i))) (alpha cf cg cx .closed)

/-- Independence is the actual commuting refinement square on right adjoints,
with the specified counit-compatible comparisons, in their contravariant direction.
Source: blueprint compactification independence, Verdier-exchange Step 1
(blueprint: def-sf-constructible-exceptional-compositor-data). -/
def RefinementIndependent
    {S : ∀ (E : FieldStage.{u} B.l) (n : ℕ+),
      SixFunctorOperationDatum D B E.carrier n n.pos}
    (A : LeftCompositors B f g P Q R S) : Prop :=
  ∀ (cf df : Compactification f.hom.left) (rf : cf.Refinement df)
    (cg dg : Compactification g.hom.left) (rg : cg.Refinement dg)
    (cx dx : Compactification (f ≫ g).hom.left) (rx : cx.Refinement dx)
    (s : Stage.{u} B.l) (L : C.{u, u} B.l B.Qbar Z.obj.left s),
    (P.refinements.refinement rf s).right.hom.app ((Q.ring.operation dg s).G.obj L) ≫
        (P.ring.operation cf s).G.map ((Q.refinements.refinement rg s).right.hom.app L) ≫
        (exceptionalIso B (P.ring.operation cf s) (Q.ring.operation cg s)
          (R.ring.operation cx s) (A.alpha cf cg cx s)).hom.app L =
      (exceptionalIso B (P.ring.operation df s) (Q.ring.operation dg s)
        (R.ring.operation dx s) (A.alpha df dg dx s)).hom.app L ≫
          (R.refinements.refinement rx s).right.hom.app L

end TwoArrows

end WeilConjectures.ConstructibleExceptionalCompositor
