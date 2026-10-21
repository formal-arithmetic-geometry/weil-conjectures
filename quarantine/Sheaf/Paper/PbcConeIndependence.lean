/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.PbcCommonStageCones

/-! # Compatibility and independence of common-stage cone triangles

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
`prop-weil-pbc-cone-independence`; Stacks Project, Tags 014B and 014A.
(blueprint: prop-weil-pbc-cone-independence)

The assertion is packaged over the existing stage-system interface to keep its
formulas readable. The theorem specializes it to the recorded concrete PBC system,
with its actual categories, tensor transitions, associators and normalized shifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w v u c
open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]

/-- The scalar-extended cone with endpoints identified by the specified associators.
Its first arrow is transport of the representative, and its last arrow includes sigma.
Source: blueprint main-20261015, cone independence, first sentence
(blueprint: prop-weil-pbc-cone-independence). -/
def transportedCone {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) : Triangle (C N) :=
  Triangle.mk (S.tr hr r.u)
    ((S.assoc r.hY hr).inv.app Y.obj ≫ (S.T hr).map g)
    ((S.T hr).map h ≫ ((S.T hr).commShiftIso (1 : ℤ)).hom.app _ ≫
      (shiftFunctor (C N) (1 : ℤ)).map ((S.assoc r.hX hr).hom.app X.obj))

variable [∀ i, Preadditive (C i)] [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ]

/-- The four clauses of common-stage cone independence, for the specified stage system.
This is an assertion, not an additional choice of cones or of comparison maps.
Source: blueprint main-20261015, cone independence, all four sentences
(blueprint: prop-weil-pbc-cone-independence). -/
structure ConeIndependenceSpec : Prop where
  /-- Scalar extension and the endpoint associators identify a distinguished cone
  with a distinguished cone of exactly the transported arrow. -/
  scalarExtension : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
      transportedCone S r hr Z g h ∈ distTriang (C N) ∧
        ∃ e : (S.T hr).mapTriangle.obj (Triangle.mk r.u g h) ≅
            transportedCone S r hr Z g h,
          e.hom.hom₁ = (S.assoc r.hX hr).hom.app X.obj ∧
            e.hom.hom₂ = (S.assoc r.hY hr).hom.app Y.obj ∧ e.hom.hom₃ = 𝟙 _
  /-- Equal pair morphisms have distinguished cones isomorphic at an agreement field. -/
  representatives : ∀ {X Y : S.PairCategory} (r s : PairCategory.Rep X Y),
    PairCategory.mkHom r.k r.hX r.hY r.u = PairCategory.mkHom s.k s.hX s.hY s.u →
    ∀ (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
      (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
      (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
    Triangle.mk s.u g' h' ∈ distTriang (C s.k) →
      ∃ (Q : I) (hr : r.k ≤ Q) (hs : s.k ≤ Q), S.tr hr r.u = S.tr hs s.u ∧
        ∃ e : transportedCone S r hr Z g h ≅ transportedCone S s hs Z' g' h',
          e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _
  /-- Two distinguished cones of one finite-stage arrow are isomorphic fixing endpoints. -/
  finiteStage : ∀ (M : I) {A B Z Z' : C M} (f : A ⟶ B)
    (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧) (g' : B ⟶ Z') (h' : Z' ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang (C M) →
    Triangle.mk f g' h' ∈ distTriang (C M) →
      ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h',
        e.hom.hom₁ = 𝟙 A ∧ e.hom.hom₂ = 𝟙 B
  /-- Replacement preserves the pair cone fixing endpoints and every distinguishedness
  witness, in both directions. -/
  witnesses : ∀ {X Y : S.PairCategory} (r s : PairCategory.Rep X Y),
    PairCategory.mkHom r.k r.hX r.hY r.u = PairCategory.mkHom s.k s.hX s.hY s.u →
    ∀ (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
      (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
      (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
    Triangle.mk s.u g' h' ∈ distTriang (C s.k) →
      (∃ e : commonStageCone S X Y r.k r.hX r.hY Z r.u g h ≅
          commonStageCone S X Y s.k s.hX s.hY Z' s.u g' h',
        e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y) ∧
      (∀ D : Triangle S.PairCategory,
        Nonempty (D ≅ commonStageCone S X Y r.k r.hX r.hY Z r.u g h) ↔
        Nonempty (D ≅ commonStageCone S X Y s.k s.hX s.hY Z' s.u g' h'))

omit [IsDirectedOrder I] [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ] in
private def transportedConeIso {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) :
    (S.T hr).mapTriangle.obj (Triangle.mk r.u g h) ≅ transportedCone S r hr Z g h :=
  Triangle.isoMk _ _ ((S.assoc r.hX hr).app X.obj)
    ((S.assoc r.hY hr).app Y.obj) (Iso.refl _)
    (by dsimp [transportedCone, tr, Functor.mapTriangle, Triangle.mk]; simp)
    (by dsimp [transportedCone, Functor.mapTriangle, Triangle.mk]; simp)
    (by dsimp [transportedCone, Functor.mapTriangle, Triangle.mk]; simp)

omit [IsDirectedOrder I] [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ] in
private theorem transportedCone_distinguished
    [∀ {i j : I} (hr : i ≤ j), (S.T hr).IsTriangulated]
    {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
    (hd : Triangle.mk r.u g h ∈ distTriang (C r.k)) :
    transportedCone S r hr Z g h ∈ distTriang (C N) :=
  (distinguished_iff_of_iso (transportedConeIso S r hr Z g h)).mp
    ((S.T hr).map_distinguished _ hd)

omit [Preorder I] [IsDirectedOrder I] in
private theorem finiteConeIso (M : I) {A B Z Z' : C M} (f : A ⟶ B)
    (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧) (g' : B ⟶ Z') (h' : Z' ⟶ A⟦(1 : ℤ)⟧)
    (hd : Triangle.mk f g h ∈ distTriang (C M))
    (hd' : Triangle.mk f g' h' ∈ distTriang (C M)) :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h',
      e.hom.hom₁ = 𝟙 A ∧ e.hom.hom₂ = 𝟙 B := by
  refine ⟨isoTriangleOfIso₁₂ _ _ hd hd' (Iso.refl _) (Iso.refl _)
    (by dsimp [Triangle.mk]; simp), ?_, ?_⟩
  · rfl
  · rfl

omit [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ] in
private theorem representativesConeIso
    [∀ {i j : I} (hr : i ≤ j), (S.T hr).IsTriangulated]
    {X Y : S.PairCategory} (r s : PairCategory.Rep X Y)
    (he : PairCategory.mkHom r.k r.hX r.hY r.u =
      PairCategory.mkHom s.k s.hX s.hY s.u)
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
    (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
    (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧)
    (hd : Triangle.mk r.u g h ∈ distTriang (C r.k))
    (hd' : Triangle.mk s.u g' h' ∈ distTriang (C s.k)) :
    ∃ (Q : I) (hr : r.k ≤ Q) (hs : s.k ≤ Q), S.tr hr r.u = S.tr hs s.u ∧
      ∃ e : transportedCone S r hr Z g h ≅ transportedCone S s hs Z' g' h',
        e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _ := by
  obtain ⟨Q, hr, hs, heq⟩ := (PairCategory.mkHom_eq_mkHom_iff' _ _).mp he
  refine ⟨Q, hr, hs, heq, ?_⟩
  refine ⟨isoTriangleOfIso₁₂ _ _ (transportedCone_distinguished S r hr Z g h hd)
    (transportedCone_distinguished S s hs Z' g' h' hd')
    (Iso.refl _) (Iso.refl _) ?_, ?_, ?_⟩
  · dsimp [transportedCone, Triangle.mk]
    simpa using heq
  · rfl
  · rfl

omit [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ] [∀ i, Pretriangulated (C i)]
  [∀ i, Limits.HasZeroObject (C i)] [∀ i, HasShift (C i) ℤ]
  [∀ i, Preadditive (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] in
private theorem isoToStage_trans (X : S.PairCategory) {M N : I}
    (hX : X.stage ≤ M) (hr : M ≤ N) :
    (S.isoToStage X hX).hom ≫
      (S.isoToStage ((S.ι M).obj (X.toStage hX)) hr).hom ≫
      (S.ι N).map ((S.assoc hX hr).hom.app X.obj) =
        (S.isoToStage X (hX.trans hr)).hom := by
  have hu : (S.T hr).map ((S.assoc hX (le_refl M)).inv.app X.obj) =
      (S.assoc (le_refl M) hr).inv.app (X.toStage hX) := by
    apply (cancel_epi ((S.assoc hX hr).inv.app X.obj)).mp
    exact S.cocycle_inv hX (le_refl M) hr X.obj
  change (PairCategory.mkHom M hX (le_refl M)
      ((S.assoc hX (le_refl M)).inv.app X.obj) : X ⟶ ⟨M, X.toStage hX⟩) ≫
    (PairCategory.mkHom N hr (le_refl N)
      ((S.assoc hr (le_refl N)).inv.app (X.toStage hX)) :
        (⟨M, X.toStage hX⟩ : S.PairCategory) ⟶ ⟨N, (S.T hr).obj (X.toStage hX)⟩) ≫
    (PairCategory.mkHom N (le_refl N) (le_refl N)
      ((S.T (le_refl N)).map ((S.assoc hX hr).hom.app X.obj)) :
        (⟨N, (S.T hr).obj (X.toStage hX)⟩ : S.PairCategory) ⟶
          ⟨N, X.toStage (hX.trans hr)⟩) =
    PairCategory.mkHom (X := X) (Y := ⟨N, X.toStage (hX.trans hr)⟩)
      N (hX.trans hr) (le_refl N)
      ((S.assoc (hX.trans hr) (le_refl N)).inv.app X.obj)
  rw [← PairCategory.mkHom_tr (X := X) (Y := ⟨M, X.toStage hX⟩)
    (hX := hX) (hY := le_refl M) hr ((S.assoc hX (le_refl M)).inv.app X.obj),
    PairCategory.mkHom_comp_mkHom,
    PairCategory.mkHom_comp_mkHom]
  congr 1
  simp only [tr, hu, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← S.cocycle_inv_assoc hX hr (le_refl N)]
  simp [← Functor.map_comp]

private def commonStageConeIso {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) :
    commonStageCone S X Y r.k r.hX r.hY Z r.u g h ≅
      (S.ι r.k).mapTriangle.obj (Triangle.mk r.u g h) :=
  Triangle.isoMk _ _ (S.isoToStage X r.hX) (S.isoToStage Y r.hY) (Iso.refl _)
    (by dsimp [commonStageCone, Functor.mapTriangle, Triangle.mk]
        simp [mkHom_eq_isoToStage, Category.assoc])
    (by dsimp [commonStageCone, Functor.mapTriangle, Triangle.mk]; simp)
    (by dsimp [commonStageCone, Functor.mapTriangle, Triangle.mk]
        simp [Category.assoc, ← Functor.map_comp])

private def commonStageConeMapIso {X Y : S.PairCategory}
    (r : PairCategory.Rep X Y) {N : I} (hr : r.k ≤ N)
    [NatTrans.CommShift (S.transIso hr).hom ℤ]
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) :
    commonStageCone S X Y r.k r.hX r.hY Z r.u g h ≅
      (S.ι N).mapTriangle.obj (transportedCone S r hr Z g h) :=
  commonStageConeIso S r Z g h ≪≫
    (Functor.mapTriangleIso (S.transIso hr)).symm.app (Triangle.mk r.u g h) ≪≫
    (Functor.mapTriangleCompIso (S.T hr) (S.ι N)).app (Triangle.mk r.u g h) ≪≫
    (S.ι N).mapTriangle.mapIso (transportedConeIso S r hr Z g h)

omit [∀ i, Pretriangulated (C i)] [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, Preadditive (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] in
private theorem commonStageConeMapIso_hom₁ {X Y : S.PairCategory}
    (r : PairCategory.Rep X Y) {N : I} (hr : r.k ≤ N)
    [NatTrans.CommShift (S.transIso hr).hom ℤ]
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) :
    (commonStageConeMapIso S r hr Z g h).hom.hom₁ =
      (S.isoToStage X (r.hX.trans hr)).hom := by
  change (S.isoToStage X r.hX).hom ≫
    (S.transIso hr).inv.app (X.toStage r.hX) ≫
      𝟙 _ ≫ (S.ι N).map ((S.assoc r.hX hr).hom.app X.obj) = _
  dsimp only [Functor.comp_obj, transIso_inv_app, ι_obj]
  erw [Category.id_comp]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc, ι_obj]
    using isoToStage_trans S X r.hX hr

omit [∀ i, Pretriangulated (C i)] [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, Preadditive (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] in
private theorem commonStageConeMapIso_hom₂ {X Y : S.PairCategory}
    (r : PairCategory.Rep X Y) {N : I} (hr : r.k ≤ N)
    [NatTrans.CommShift (S.transIso hr).hom ℤ]
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) :
    (commonStageConeMapIso S r hr Z g h).hom.hom₂ =
      (S.isoToStage Y (r.hY.trans hr)).hom := by
  change (S.isoToStage Y r.hY).hom ≫
    (S.transIso hr).inv.app (Y.toStage r.hY) ≫
      𝟙 _ ≫ (S.ι N).map ((S.assoc r.hY hr).hom.app Y.obj) = _
  dsimp only [Functor.comp_obj, transIso_inv_app, ι_obj]
  erw [Category.id_comp]
  simpa only [Category.id_comp, Category.comp_id, Category.assoc, ι_obj]
    using isoToStage_trans S Y r.hY hr

private theorem pairConeIso
    [∀ {i j : I} (hr : i ≤ j), (S.T hr).IsTriangulated]
    [∀ {i j : I} (hr : i ≤ j), NatTrans.CommShift (S.transIso hr).hom ℤ]
    {X Y : S.PairCategory} (r s : PairCategory.Rep X Y)
    (he : PairCategory.mkHom r.k r.hX r.hY r.u =
      PairCategory.mkHom s.k s.hX s.hY s.u)
    (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
    (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
    (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧)
    (hd : Triangle.mk r.u g h ∈ distTriang (C r.k))
    (hd' : Triangle.mk s.u g' h' ∈ distTriang (C s.k)) :
    ∃ e : commonStageCone S X Y r.k r.hX r.hY Z r.u g h ≅
        commonStageCone S X Y s.k s.hX s.hY Z' s.u g' h',
      e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y := by
  obtain ⟨Q, hr, hs, _, e, he₁, he₂⟩ :=
    representativesConeIso S r s he Z g h Z' g' h' hd hd'
  let a := commonStageConeMapIso S r hr Z g h
  let b := commonStageConeMapIso S s hs Z' g' h'
  refine ⟨a ≪≫ (S.ι Q).mapTriangle.mapIso e ≪≫ b.symm, ?_, ?_⟩
  · change a.hom.hom₁ ≫ (S.ι Q).map e.hom.hom₁ ≫ b.inv.hom₁ = 𝟙 X
    erw [he₁, Functor.map_id, Category.id_comp]
    have hab : a.hom.hom₁ = b.hom.hom₁ := by
      simp only [a, b, commonStageConeMapIso_hom₁]
      rfl
    rw [hab]
    exact congrArg TriangleMorphism.hom₁ b.hom_inv_id
  · change a.hom.hom₂ ≫ (S.ι Q).map e.hom.hom₂ ≫ b.inv.hom₂ = 𝟙 Y
    erw [he₂, Functor.map_id, Category.id_comp]
    have hab : a.hom.hom₂ = b.hom.hom₂ := by
      simp only [a, b, commonStageConeMapIso_hom₂]
      rfl
    rw [hab]
    exact congrArg TriangleMorphism.hom₂ b.hom_inv_id

/-- Exact coherent transitions imply all four cone-independence clauses.
Source: blueprint cone-independence proof, Steps 1--6
(blueprint: prop-weil-pbc-cone-independence). -/
theorem coneIndependenceOfExact
    [∀ {i j : I} (hr : i ≤ j), (S.T hr).IsTriangulated]
    [∀ {i j : I} (hr : i ≤ j), NatTrans.CommShift (S.transIso hr).hom ℤ] :
    ConeIndependenceSpec S := by
  refine { scalarExtension := ?_, representatives := ?_, finiteStage := ?_, witnesses := ?_ }
  · intro X Y r N hr Z g h hd
    exact ⟨transportedCone_distinguished S r hr Z g h hd,
      transportedConeIso S r hr Z g h, rfl, rfl, rfl⟩
  · exact representativesConeIso S
  · exact finiteConeIso
  · intro X Y r s he Z g h Z' g' h' hd hd'
    obtain ⟨e, he₁, he₂⟩ := pairConeIso S r s he Z g h Z' g' h' hd hd'
    refine ⟨⟨e, he₁, he₂⟩, ?_⟩
    intro D
    constructor
    · rintro ⟨i⟩
      exact ⟨i ≪≫ e⟩
    · rintro ⟨i⟩
      exact ⟨i ≪≫ e.symm⟩

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]

private theorem coneTransIsoCommShift
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
    {i j : I} (h : i ≤ j) : NatTrans.CommShift (S.transIso h).hom ℤ := by
  constructor
  intro n
  ext X
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((S.ι j).map (((S.T h).commShiftIso n).hom.app X) ≫
    𝟙 _) ≫ (pbcPairShift S n).map ((S.transIso h).hom.app X) =
    (S.transIso h).hom.app ((shiftFunctor (C i) n).obj X) ≫ 𝟙 _
  simp only [Category.comp_id]
  simp only [transIso_hom_app, isoToStage, pbcPairShift]
  erw [Morphism.functor_map_mkHom, ι_map_eq (le_rfl : j ≤ j),
    PairCategory.mkHom_comp_mkHom]
  congr 1
  change (S.T (le_rfl : j ≤ j)).map (((S.T h).commShiftIso n).hom.app X) ≫
    (((S.T (le_rfl : j ≤ j)).commShiftIso n).hom.app ((S.T h).obj X) ≫
      (shiftFunctor (C j) n).map ((S.assoc h le_rfl).hom.app X) ≫
        ((S.T h).commShiftIso n).inv.app X) =
    (S.assoc h le_rfl).hom.app ((shiftFunctor (C i) n).obj X)
  have eq := congrArg (fun f ↦ f ≫ ((S.T h).commShiftIso n).inv.app X)
    (pbcStageShift_coherence S n h le_rfl X)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
    Category.comp_id] using eq

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry

section Exactness

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

private theorem coneIntegralExact {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcIntegralScalarExtension l Ω T hDim.out hInv.out h).IsTriangulated := by
  have := (pbcDerivedScalarAdjunction
    (pbcCompletedScalarMap l Ω T h)).commShift_of_rightAdjoint ℤ
  have : (pbcDerivedRestrict (pbcCompletedScalarMap l Ω T h)).IsTriangulated :=
    inferInstanceAs
      (((pbcRestrict (pbcCompletedScalarMap l Ω T h)).mapDerivedCategory).IsTriangulated)
  have : (pbcAmbientScalarExtension l Ω T h).IsTriangulated :=
    (pbcDerivedScalarAdjunction
      (pbcCompletedScalarMap l Ω T h)).isTriangulated_leftAdjoint
  have hc := Functor.CommShift.ofComp_compatibility
    (F := pbcIntegralScalarExtension l Ω T hDim.out hInv.out h)
    (G := pbcStageInclusion l Ω T F)
    (Iso.refl (pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h)) ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (F := pbcIntegralScalarExtension l Ω T hDim.out hInv.out h)
    (G := pbcStageInclusion l Ω T F)
    (Iso.refl (pbcStageInclusion l Ω T E ⋙ pbcAmbientScalarExtension l Ω T h))).mpr
      inferInstance

private theorem coneLocalizationExact (E : Padic.FiniteCoefficientFields l Ω) :
    (pbcStageLocalization l Ω T E).IsTriangulated := by
  constructor
  intro D hD
  exact (qbarStagePretriangulated_exists l Ω T E).exists.choose_spec _ |>.mpr
    ⟨D, hD, ⟨Iso.refl _⟩⟩

private theorem coneScalarExact {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (pbcScalarExtension l Ω T hDim.out hInv.out h).IsTriangulated := by
  have := coneIntegralExact l Ω T h
  have := coneLocalizationExact l Ω T E
  have := coneLocalizationExact l Ω T F
  have := (pbcScalarShift_exists l Ω T hDim.out hInv.out h).exists.choose_spec
  constructor
  intro D hd
  obtain ⟨D', hd', ⟨e⟩⟩ :=
    (qbarStagePretriangulated_exists l Ω T E).exists.choose_spec D |>.mp hd
  let B := pbcScalarExtension l Ω T hDim.out hInv.out h
  let Q := pbcStageLocalization l Ω T E
  let Q' := pbcStageLocalization l Ω T F
  let A := pbcIntegralScalarExtension l Ω T hDim.out hInv.out h
  have he : B.mapTriangle.obj D ≅ Q'.mapTriangle.obj (A.mapTriangle.obj D') :=
    B.mapTriangle.mapIso e ≪≫ (Functor.mapTriangleCompIso Q B).symm.app D' ≪≫
      (Functor.mapTriangleIso
        (pbcScalarIntegralComparison l Ω T hDim.out hInv.out h)).app D' ≪≫
      (Functor.mapTriangleCompIso A Q').app D'
  exact (distinguished_iff_of_iso he).mpr
    (Q'.map_distinguished _ (A.map_distinguished _ hd'))

end Exactness

-- Bound instance search while specializing the normalized coefficient system.
set_option synthInstance.maxHeartbeats 5000 in
-- Bound specialization of the normalized coefficient system.
set_option maxHeartbeats 30000 in
/-- Common-stage cones in the actual PBC coefficient system are independent of the
representative, common field and chosen distinguished cone, in all four specified senses.
Source: blueprint main-20261015, cone independence; Stacks Tags 014B and 014A
(blueprint: prop-weil-pbc-cone-independence).
Proof:
1. Exactness from prop-weil-pbc-scalar-extension makes the mapped triangle, with
   its sigma last arrow, distinguished. Replace its endpoints by A_X and A_Y;
   the three squares give the required isomorphism, and TR1 preserves distinguishedness.
2. For one finite-stage arrow, TR3 extends the identity square; the third
   component is invertible by lem-sf-triangle-morphism-iso (Stacks 014A).
3. The equality criterion of prop-weil-pbc-common-stage-calculus supplies a
   finite agreement field Q. Apply Steps 1 and 2 there to compare the cones.
4. Identify each original pair cone with its extension at Q. The cone comparison
   is represented by identity at Q. Shift-associator coherence identifies the
   third-arrow representatives, including the sigma inverse of commonStageCone.
5. Represent the Step 3 cone isomorphism and its inverse at Q, and compose with
   the Step 4 comparisons. This gives a pair-triangle isomorphism fixing endpoints.
6. Compose any distinguishedness witness with this isomorphism or its inverse.
   Thus the witnesses in def-weil-pbc-common-stage-cones are interchangeable. -/
theorem pbcConeIndependence (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    StageSystem.ConeIndependenceSpec (pbcScalarSystem l Ω T hDim.out hInv.out) := by
  let S := pbcScalarSystem l Ω T hDim.out hInv.out
  have : ∀ {i j : Padic.FiniteCoefficientFields l Ω} (hr : i ≤ j),
      (S.T hr).IsTriangulated := fun hr ↦
    coneScalarExact l Ω T hr
  have : ∀ {i j : Padic.FiniteCoefficientFields l Ω} (hr : i ≤ j),
      NatTrans.CommShift (S.transIso hr).hom ℤ :=
    fun hr ↦ StageSystem.coneTransIsoCommShift S hr
  exact StageSystem.coneIndependenceOfExact S

end AlgebraicGeometry.Scheme
