/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.TruncationStep
public import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The truncation triangles in the derived category

Let `C` be an abelian category. The canonical truncations `τ_{≤ n}` of cochain complexes
preserve quasi-isomorphisms, hence descend along the localization functor
`Q : CochainComplex C ℤ ⥤ DerivedCategory C` to functors `DerivedCategory.truncLE C n`
(blueprint `lem-weil-pbc-truncation-descends`). The inclusions `τ_{≤ q₀} ⟶ τ_{≤ q}` and the
projections `τ_{≤ q} ⟶ H^q(-)[-q]` descend to natural transformations
`DerivedCategory.truncLEMapOfLE` and `DerivedCategory.truncLEToHomologySingle`.

For `q₀ + 1 = q`, we construct the connecting morphism
`DerivedCategory.truncLEδ : H^q(-)[-q] ⟶ τ_{≤ q₀}(-)⟦1⟧` and show that the truncation
triangles

`τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧`

are distinguished (`DerivedCategory.truncLETriangle_distinguished`), functorially in `X`
(`DerivedCategory.truncLETriangle`), and that the third morphism is the only one making the
triangle distinguished (`DerivedCategory.truncLEδ_unique`). This is blueprint
`lem-weil-pbc-truncation-triangle` (Stacks, Remark 08J5; [BBD, 1.1.9, 1.1.10]).

The connecting morphism is first constructed on the image `Q.obj K` of a complex, from the
distinguished triangle of the short exact sequence `0 ⟶ τ_{≤ q₀} K ⟶ τ_{≤ q} K ⟶ M_q(K) ⟶ 0`
(`DerivedCategory.triangleOfSES_distinguished`, blueprint `lem-weil-pbc-complex-ses-triangle`)
and the quasi-isomorphism `M_q(K) ⟶ H^q(K)[-q]` (`CochainComplex.quasiIso_truncLEStepToSingle`),
then transported to an arbitrary object. Its naturality follows from the vanishing of
`Hom((τ_{≤ q₀} X)⟦1⟧, H^q(Y)[-q])` for the canonical t-structure and blueprint
`lem-weil-pbc-triangle-morphism-extension`.

The descent of functors and natural transformations uses the universal property of the
localization (`CategoryTheory.Localization.lift`, `CategoryTheory.Localization.liftNatTrans`,
`CategoryTheory.Localization.natTrans_ext`; blueprint
`lem-weil-pbc-localization-universal-property`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CochainComplex

variable (C : Type*) [Category* C] [Abelian C]

/-- The canonical truncation functor `K ↦ τ_{≤ n} K` on cochain complexes. -/
noncomputable abbrev truncLEFunctor (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.truncLE n
  map φ := truncLEMap φ n
  map_id K := HomologicalComplex.truncLEMap_id K _
  map_comp φ ψ := HomologicalComplex.truncLEMap_comp φ ψ _

/-- The inclusions `τ_{≤ n} K ⟶ K`, as a natural transformation. -/
@[simps]
noncomputable def ιTruncLENatTrans (n : ℤ) : truncLEFunctor C n ⟶ 𝟭 _ where
  app K := K.ιTruncLE n
  naturality _ _ φ := CochainComplex.ιTruncLE_naturality φ n

/-- The inclusions `τ_{≤ a} K ⟶ τ_{≤ b} K` for `a ≤ b`, as a natural transformation. -/
@[simps]
noncomputable def truncLEMapOfLENatTrans (a b : ℤ) (h : a ≤ b) :
    truncLEFunctor C a ⟶ truncLEFunctor C b where
  app K := K.truncLEMapOfLE a b h
  naturality _ _ φ := truncLEMapOfLE_naturality φ a b h

/-- The projections `τ_{≤ q} K ⟶ H^q(K)[-q]`, as a natural transformation. -/
@[simps]
noncomputable def truncLEToSingleNatTrans (q : ℤ) :
    truncLEFunctor C q ⟶ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ⋙
      HomologicalComplex.single C (ComplexShape.up ℤ) q where
  app K := K.truncLEToSingle q
  naturality _ _ φ := truncLEToSingle_naturality φ q

end CochainComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

section Descent

omit [HasDerivedCategory C] in
/-- This is blueprint `lem-weil-pbc-truncation-descends` (a) for `τ_{≤ n}`: the canonical
truncation of a quasi-isomorphism is a quasi-isomorphism. -/
lemma quasiIso_truncLEMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ] (n : ℤ) :
    QuasiIso (CochainComplex.truncLEMap φ n) :=
  (CochainComplex.quasiIso_truncLEMap_iff (φ := φ) (n := n)).2 (fun _ _ ↦ inferInstance)

omit [HasDerivedCategory C] in
/-- This is blueprint `lem-weil-pbc-truncation-descends` (a) for `H^q(-)[-q]`: for a
quasi-isomorphism `φ`, the morphism `H^q(φ)[-q]` is an isomorphism of complexes. -/
lemma isIso_single_map_homologyMap {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (q : ℤ) : IsIso ((HomologicalComplex.single C (ComplexShape.up ℤ) q).map
      (HomologicalComplex.homologyMap φ q)) :=
  inferInstance

variable (C) in
lemma quasiIso_isInvertedBy_truncLEFunctor (n : ℤ) :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy
      (CochainComplex.truncLEFunctor C n ⋙ Q) := fun K L φ hφ ↦ by
  have : QuasiIso φ := hφ
  have := quasiIso_truncLEMap φ n
  exact inferInstanceAs (IsIso (Q.map (CochainComplex.truncLEMap φ n)))

variable (C) in
/-- The canonical truncation functor `τ_{≤ n} : D(C) ⥤ D(C)`, induced by the canonical truncation
of cochain complexes (blueprint `lem-weil-pbc-truncation-descends` (b)). -/
noncomputable def truncLE (n : ℤ) : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift _ (quasiIso_isInvertedBy_truncLEFunctor C n) Q

noncomputable instance (n : ℤ) :
    Localization.Lifting Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (CochainComplex.truncLEFunctor C n ⋙ Q) (truncLE C n) :=
  Localization.liftingLift _ _ _

variable (C) in
/-- The isomorphism `τ_{≤ n}(Q K) ≅ Q(τ_{≤ n} K)`, natural in `K`. -/
noncomputable def truncLEFactors (n : ℤ) :
    Q ⋙ truncLE C n ≅ CochainComplex.truncLEFunctor C n ⋙ Q :=
  Localization.Lifting.iso _ (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _

/-- The isomorphism `τ_{≤ n}(Q K) ≅ Q(τ_{≤ n} K)`. -/
noncomputable def truncLEFactorsApp (n : ℤ) (K : CochainComplex C ℤ) :
    (truncLE C n).obj (Q.obj K) ≅ Q.obj (K.truncLE n) :=
  (truncLEFactors C n).app K

variable (C) in
/-- The functor `X ↦ H^q(X)[-q]` on the derived category. -/
noncomputable abbrev homologySingleFunctor (q : ℤ) : DerivedCategory C ⥤ DerivedCategory C :=
  homologyFunctor C q ⋙ singleFunctor C q

variable (C) in
/-- The isomorphism `H^q(Q K)[-q] ≅ Q(H^q(K)[-q])`, natural in `K`. -/
noncomputable def homologySingleFunctorFactors (q : ℤ) :
    Q ⋙ homologySingleFunctor C q ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ⋙
        HomologicalComplex.single C (ComplexShape.up ℤ) q ⋙ Q :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (homologyFunctorFactors C q) _ ≪≫
    Functor.isoWhiskerLeft _ (singleFunctorIsoCompQ C q)

/-- The isomorphism `H^q(Q K)[-q] ≅ Q(H^q(K)[-q])`. -/
noncomputable def homologySingleFunctorFactorsApp (q : ℤ) (K : CochainComplex C ℤ) :
    (homologySingleFunctor C q).obj (Q.obj K) ≅
      Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) q).obj (K.homology q)) :=
  (homologySingleFunctorFactors C q).app K

noncomputable instance (q : ℤ) :
    Localization.Lifting Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ⋙
        HomologicalComplex.single C (ComplexShape.up ℤ) q ⋙ Q) (homologySingleFunctor C q) :=
  ⟨homologySingleFunctorFactors C q⟩

variable (C) in
/-- The inclusion `i : τ_{≤ a} ⟶ τ_{≤ b}` of truncation functors on the derived category, for
`a ≤ b` (blueprint `lem-weil-pbc-truncation-descends` (b)). -/
noncomputable def truncLEMapOfLE (a b : ℤ) (h : a ≤ b) : truncLE C a ⟶ truncLE C b :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    (Functor.whiskerRight (CochainComplex.truncLEMapOfLENatTrans C a b h) Q)

variable (C) in
/-- The morphism `τ_{≤ n} ⟶ 𝟭` of functors on the derived category. -/
noncomputable def truncLEι (n : ℤ) : truncLE C n ⟶ 𝟭 _ :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (CochainComplex.truncLEFunctor C n ⋙ Q) Q _ _
    (Functor.whiskerRight (CochainComplex.ιTruncLENatTrans C n) Q ≫ (Functor.leftUnitor Q).hom)

variable (C) in
/-- The projection `j : τ_{≤ q} ⟶ H^q(-)[-q]` of functors on the derived category (blueprint
`lem-weil-pbc-truncation-descends` (b)). -/
noncomputable def truncLEToHomologySingle (q : ℤ) : truncLE C q ⟶ homologySingleFunctor C q :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ⋙
        HomologicalComplex.single C (ComplexShape.up ℤ) q ⋙ Q) _ _
    (Functor.whiskerRight (CochainComplex.truncLEToSingleNatTrans C q) Q ≫
      (Functor.associator _ _ _).hom)

/-- This is blueprint `lem-weil-pbc-truncation-descends` (b): on the image of a complex `K`, the
inclusion `τ_{≤ a} ⟶ τ_{≤ b}` is `Q` of the inclusion of complexes. -/
@[reassoc]
lemma truncLEMapOfLE_app_Q (a b : ℤ) (h : a ≤ b) (K : CochainComplex C ℤ) :
    (truncLEMapOfLE C a b h).app (Q.obj K) = (truncLEFactorsApp a K).hom ≫
      Q.map (K.truncLEMapOfLE a b h) ≫ (truncLEFactorsApp b K).inv := by
  rw [truncLEMapOfLE, Localization.liftNatTrans_app]
  rfl

@[reassoc]
lemma truncLEι_app_Q (n : ℤ) (K : CochainComplex C ℤ) :
    (truncLEι C n).app (Q.obj K) = (truncLEFactorsApp n K).hom ≫ Q.map (K.ιTruncLE n) := by
  rw [truncLEι, Localization.liftNatTrans_app]
  dsimp
  erw [comp_id, comp_id]
  rfl

/-- This is blueprint `lem-weil-pbc-truncation-descends` (b): on the image of a complex `K`, the
projection `τ_{≤ q} ⟶ H^q(-)[-q]` is `Q` of the projection of complexes. -/
@[reassoc]
lemma truncLEToHomologySingle_app_Q (q : ℤ) (K : CochainComplex C ℤ) :
    (truncLEToHomologySingle C q).app (Q.obj K) ≫ (homologySingleFunctorFactorsApp q K).hom =
      (truncLEFactorsApp q K).hom ≫ Q.map (K.truncLEToSingle q) := by
  rw [truncLEToHomologySingle, Localization.liftNatTrans_app, assoc, assoc]
  erw [Iso.inv_hom_id_app, comp_id]
  dsimp
  erw [comp_id]
  rfl

end Descent

section Cohomology

/-- The truncation `τ_{≤ n} X` is `≤ n` for the canonical t-structure. -/
instance isLE_truncLE_obj (X : DerivedCategory C) (n : ℤ) : ((truncLE C n).obj X).IsLE n := by
  have : (Q.obj ((Q.objPreimage X).truncLE n)).IsLE n := inferInstance
  exact TStructure.t.isLE_of_iso
    ((truncLEFactorsApp n (Q.objPreimage X)).symm ≪≫
      (truncLE C n).mapIso (Q.objObjPreimageIso X)) n

/-- This is blueprint `lem-weil-pbc-truncation-cohomology` in the derived category: the morphism
`τ_{≤ n} X ⟶ X` induces isomorphisms on `H^i` for `i ≤ n`. -/
lemma isIso_homologyFunctor_map_truncLEι_app (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor C i).map ((truncLEι C n).app X)) := by
  let K := Q.objPreimage X
  let e : Q.obj K ≅ X := Q.objObjPreimageIso X
  have h : (truncLEι C n).app X =
      (truncLE C n).map e.inv ≫ (truncLEι C n).app (Q.obj K) ≫ e.hom := by
    have := (truncLEι C n).naturality e.inv
    dsimp at this
    rw [reassoc_of% this, e.inv_hom_id, comp_id]
  have : IsIso ((homologyFunctor C i).map (Q.map (K.ιTruncLE n))) :=
    (NatIso.isIso_map_iff (homologyFunctorFactors C i) (K.ιTruncLE n)).2
      (K.isIso_homologyMap_ιTruncLE n i hi)
  rw [h, truncLEι_app_Q]
  simp only [Functor.map_comp]
  infer_instance

/-- This is blueprint `lem-weil-pbc-truncation-cohomology` in the derived category: the
truncation `τ_{≤ n} X` has no cohomology in degrees `i > n`. -/
lemma isZero_homologyFunctor_obj_truncLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj ((truncLE C n).obj X)) :=
  isZero_of_isLE _ n i hi

/-- The truncation of a bounded below object is bounded below. -/
lemma isGE_truncLE_obj (X : DerivedCategory C) (a n : ℤ) [X.IsGE a] :
    ((truncLE C n).obj X).IsGE a := by
  rw [isGE_iff]
  intro i hi
  by_cases h : i ≤ n
  · have := isIso_homologyFunctor_map_truncLEι_app X n i h
    exact (isZero_of_isGE X a i hi).of_iso
      (asIso ((homologyFunctor C i).map ((truncLEι C n).app X)))
  · exact isZero_homologyFunctor_obj_truncLE X n i (by lia)

end Cohomology

section Triangle

variable (q₀ q : ℤ) (hq : q₀ + 1 = q)

/-- The connecting morphism `H^q(Q K)[-q] ⟶ (τ_{≤ q₀}(Q K))⟦1⟧` of the truncation triangle of
the image of a complex `K`: the connecting morphism of the short exact sequence
`0 ⟶ τ_{≤ q₀} K ⟶ τ_{≤ q} K ⟶ M_q(K) ⟶ 0`, composed with the inverse of the quasi-isomorphism
`M_q(K) ⟶ H^q(K)[-q]`. -/
noncomputable def truncLEδOfComplex (K : CochainComplex C ℤ) :
    (homologySingleFunctor C q).obj (Q.obj K) ⟶ ((truncLE C q₀).obj (Q.obj K))⟦(1 : ℤ)⟧ :=
  (homologySingleFunctorFactorsApp q K).hom ≫
    inv (Q.map (K.truncLEStepToSingle q₀ q hq)) ≫
    triangleOfSESδ (K.truncLEStep_shortExact q₀ q hq) ≫
    (truncLEFactorsApp q₀ K).inv⟦(1 : ℤ)⟧'

/-- The truncation triangle of the image of a complex `K`. -/
noncomputable def truncLETriangleOfComplex (K : CochainComplex C ℤ) :
    Triangle (DerivedCategory C) :=
  Triangle.mk ((truncLEMapOfLE C q₀ q (by lia)).app (Q.obj K))
    ((truncLEToHomologySingle C q).app (Q.obj K)) (truncLEδOfComplex q₀ q hq K)

lemma truncLETriangleOfComplex_distinguished (K : CochainComplex C ℤ) :
    truncLETriangleOfComplex q₀ q hq K ∈ distTriang _ := by
  refine isomorphic_distinguished _
    (triangleOfSES_distinguished (K.truncLEStep_shortExact q₀ q hq)) _ ?_
  refine Triangle.isoMk _ _ (truncLEFactorsApp q₀ K) (truncLEFactorsApp q K)
    (homologySingleFunctorFactorsApp q K ≪≫
      (asIso (Q.map (K.truncLEStepToSingle q₀ q hq))).symm) ?_ ?_ ?_
  · change (truncLEMapOfLE C q₀ q (by lia)).app (Q.obj K) ≫ (truncLEFactorsApp q K).hom =
      (truncLEFactorsApp q₀ K).hom ≫ Q.map (K.truncLEMapOfLE q₀ q (by lia))
    rw [truncLEMapOfLE_app_Q, assoc, assoc, Iso.inv_hom_id, comp_id]
  · change (truncLEToHomologySingle C q).app (Q.obj K) ≫ (homologySingleFunctorFactorsApp q K).hom ≫
      inv (Q.map (K.truncLEStepToSingle q₀ q hq)) =
        (truncLEFactorsApp q K).hom ≫ Q.map (K.truncLEStep q₀ q hq).g
    rw [truncLEToHomologySingle_app_Q_assoc,
      ← CochainComplex.truncLEStep_g_truncLEStepToSingle K q₀ q hq, Q.map_comp, assoc,
      IsIso.hom_inv_id, comp_id]
  · change truncLEδOfComplex q₀ q hq K ≫ (truncLEFactorsApp q₀ K).hom⟦(1 : ℤ)⟧' =
      ((homologySingleFunctorFactorsApp q K).hom ≫ inv (Q.map (K.truncLEStepToSingle q₀ q hq))) ≫
        triangleOfSESδ (K.truncLEStep_shortExact q₀ q hq)
    simp only [truncLEδOfComplex, assoc, ← Functor.map_comp, Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, comp_id]

/-- The connecting morphism `H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧` of the truncation triangle, at an
object `X`, obtained by transporting `DerivedCategory.truncLEδOfComplex` along a choice of a
complex `K` with `Q.obj K ≅ X`. -/
noncomputable def truncLEδApp (X : DerivedCategory C) :
    (homologySingleFunctor C q).obj X ⟶ ((truncLE C q₀).obj X)⟦(1 : ℤ)⟧ :=
  (homologySingleFunctor C q).map (Q.objObjPreimageIso X).inv ≫
    truncLEδOfComplex q₀ q hq (Q.objPreimage X) ≫
    ((truncLE C q₀).map (Q.objObjPreimageIso X).hom)⟦(1 : ℤ)⟧'

/-- The truncation triangle `τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧`. -/
noncomputable def truncLETriangleObj (X : DerivedCategory C) : Triangle (DerivedCategory C) :=
  Triangle.mk ((truncLEMapOfLE C q₀ q (by lia)).app X)
    ((truncLEToHomologySingle C q).app X) (truncLEδApp q₀ q hq X)

lemma truncLETriangleObj_distinguished (X : DerivedCategory C) :
    truncLETriangleObj q₀ q hq X ∈ distTriang _ := by
  let e := Q.objObjPreimageIso X
  refine isomorphic_distinguished _
    (truncLETriangleOfComplex_distinguished q₀ q hq (Q.objPreimage X)) _ ?_
  refine Triangle.isoMk _ _ ((truncLE C q₀).mapIso e.symm) ((truncLE C q).mapIso e.symm)
    ((homologySingleFunctor C q).mapIso e.symm) ?_ ?_ ?_
  · exact ((truncLEMapOfLE C q₀ q (by lia)).naturality e.inv).symm
  · exact ((truncLEToHomologySingle C q).naturality e.inv).symm
  · change truncLEδApp q₀ q hq X ≫ ((truncLE C q₀).map e.inv)⟦(1 : ℤ)⟧' =
      (homologySingleFunctor C q).map e.inv ≫ truncLEδOfComplex q₀ q hq (Q.objPreimage X)
    simp only [truncLEδApp, assoc, ← Functor.map_comp, e, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, comp_id]

include hq in
lemma subsingleton_shift_truncLE_hom_homologySingle (X Y : DerivedCategory C) :
    Subsingleton (((truncLE C q₀).obj X)⟦(1 : ℤ)⟧ ⟶ (homologySingleFunctor C q).obj Y) := by
  have : TStructure.t.IsLE (((truncLE C q₀).obj X)⟦(1 : ℤ)⟧) (q₀ - 1) :=
    TStructure.t.isLE_shift _ q₀ 1 (q₀ - 1) (by lia)
  have : TStructure.t.IsGE ((homologySingleFunctor C q).obj Y) q :=
    inferInstanceAs (((singleFunctor C q).obj _).IsGE q)
  exact ⟨fun f g ↦ by
    rw [TStructure.t.zero f (q₀ - 1) q (by lia), TStructure.t.zero g (q₀ - 1) q (by lia)]⟩

/-- The connecting morphism `δ : H^q(-)[-q] ⟶ τ_{≤ q₀}(-)⟦1⟧` of the truncation triangles, a
natural transformation (blueprint `lem-weil-pbc-truncation-triangle`). -/
noncomputable def truncLEδ :
    homologySingleFunctor C q ⟶ truncLE C q₀ ⋙ shiftFunctor _ (1 : ℤ) where
  app X := truncLEδApp q₀ q hq X
  naturality X Y f := by
    have : Subsingleton ((truncLETriangleObj q₀ q hq X).obj₁⟦(1 : ℤ)⟧ ⟶
        (truncLETriangleObj q₀ q hq Y).obj₃) :=
      subsingleton_shift_truncLE_hom_homologySingle q₀ q hq X Y
    exact (comm₃_of_subsingleton (truncLETriangleObj_distinguished q₀ q hq X)
      (truncLETriangleObj_distinguished q₀ q hq Y) ((truncLE C q₀).map f)
      ((truncLE C q).map f) ((homologySingleFunctor C q).map f)
      ((truncLEMapOfLE C q₀ q (by lia)).naturality f).symm
      ((truncLEToHomologySingle C q).naturality f).symm).symm

@[simp]
lemma truncLEδ_app (X : DerivedCategory C) : (truncLEδ q₀ q hq).app X = truncLEδApp q₀ q hq X :=
  rfl

/-- The truncation triangles `τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧`, as a
functor `D(C) ⥤ Triangle D(C)` (blueprint `lem-weil-pbc-truncation-triangle`). -/
noncomputable def truncLETriangle : DerivedCategory C ⥤ Triangle (DerivedCategory C) :=
  Triangle.functorMk (truncLEMapOfLE C q₀ q (by lia)) (truncLEToHomologySingle C q)
    (truncLEδ q₀ q hq)

/-- This is blueprint `lem-weil-pbc-truncation-triangle`: the truncation triangle
`τ_{≤ q₀} X ⟶ τ_{≤ q} X ⟶ H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧` is distinguished. Its functoriality
in `X` is that of `DerivedCategory.truncLETriangle`. -/
lemma truncLETriangle_distinguished (X : DerivedCategory C) :
    (truncLETriangle q₀ q hq).obj X ∈ distTriang _ :=
  truncLETriangleObj_distinguished q₀ q hq X

/-- This is blueprint `lem-weil-pbc-truncation-triangle`, uniqueness: the connecting morphism is
the only morphism `H^q(X)[-q] ⟶ (τ_{≤ q₀} X)⟦1⟧` completing the inclusion and the projection
to a distinguished triangle. -/
lemma truncLEδ_unique (X : DerivedCategory C)
    (x : (homologySingleFunctor C q).obj X ⟶ ((truncLE C q₀).obj X)⟦(1 : ℤ)⟧)
    (hx : Triangle.mk ((truncLEMapOfLE C q₀ q (by lia)).app X)
      ((truncLEToHomologySingle C q).app X) x ∈ distTriang _) :
    x = (truncLEδ q₀ q hq).app X := by
  have : Subsingleton ((truncLETriangleObj q₀ q hq X).obj₁⟦(1 : ℤ)⟧ ⟶
      (truncLETriangleObj q₀ q hq X).obj₃) :=
    subsingleton_shift_truncLE_hom_homologySingle q₀ q hq X X
  exact mor₃_unique_of_subsingleton (truncLETriangleObj_distinguished q₀ q hq X) x hx

end Triangle

end DerivedCategory
