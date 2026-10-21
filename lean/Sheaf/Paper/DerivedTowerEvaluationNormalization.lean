/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Algebra.Homology.DiagramKFlatReplacements
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Category.ULift

/-! # Counit normalization of derived strict-tower evaluation

Source: Stacks Project, Derived Categories, Tag 06XN (dual),
`lemma-find-existence-computes`; the completed-pullback evaluation subargument
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

The index `n : ℕ` denotes positive level `n + 1`. The comparison is unique at each
level by its value on strict objectwise K-flat complexes with flat terms. The final
identity includes every transition `b ≥ a`, including identity transitions.
-/

@[expose] public section

set_option autoImplicit false

universe u uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.DerivedTowerPullback

set_option backward.isDefEq.respectTransparency false
attribute [local instance 100000] hasSheafCompose_of_preservesLimitsOfSize

-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

-- The induced functor on structured arrows is also full and essentially
-- surjective, so restricting the defining limit cone preserves its limit.
private noncomputable def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply Limits.IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp

-- Transport the defining limit cone through an equivalence of structured
-- arrow categories and the prescribed isomorphism of diagram functors.
private noncomputable def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply Limits.IsLimit.ofIsoLimit
    ((Limits.IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Limits.Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp [Category.assoc]
  rfl

-- Transfer the resolving-class computation to any chosen cochain universal pair.
private theorem counit_computes
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] (P : CochainComplex A ℤ → Prop)
    (res : ∀ X : CochainComplex A ℤ, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
      P Y ∧ QuasiIso s)
    (pres : ∀ {X Y : CochainComplex A ℤ} (s : X ⟶ Y), P X → P Y → QuasiIso s →
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s))
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))] :
    ∀ X, P X → IsIso (ε.app X) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let G := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let S : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ Y : CochainComplex A ℤ, P Y ∧ q.obj Y = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ S ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := res X
    exact ⟨q.obj Y, q.map s, ⟨Y, hY, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hinv : ∀ X Y (s : X ⟶ Y), X ∈ S → Y ∈ S →
      HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (G.map s) := by
    rintro X Y s ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ hs
    obtain ⟨s, rfl⟩ := q.map_surjective s
    have ht := pres s hX hY ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs)
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨hpw, T, δ, hT, _, hδ⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) G S hres hinv
  have : G.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso A (.up ℤ)) := hpw
  have : T.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso A (.up ℤ)) := hT
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q δ
  have hα := pointwise_precomp_full q DerivedCategory.Qh G T δ
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T δ
      (HomotopyCategory.quasiIso A (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ G ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let β : DerivedCategory.Q ⋙ T ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  have : T.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let e := Functor.leftDerivedUnique T L ε β (HomologicalComplex.quasiIso A (.up ℤ))
  intro X hX
  have := hδ (q.obj X) ⟨X, hX, rfl⟩
  have hb : IsIso (β.app X) := by
    dsimp [β, α]
    infer_instance
  have he : e.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = ε.app X := by
    simpa only [e, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app L T ε β (HomologicalComplex.quasiIso A (.up ℤ))
        (𝟙 _) X
  rw [← he]
  infer_instance


-- Equality of transformations is detected on any resolving class of complexes.
private theorem ext_on_resolutions
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {E : Type uB} [Category.{vB} E] (P : CochainComplex A ℤ → Prop)
    (res : ∀ X : CochainComplex A ℤ, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
      P Y ∧ QuasiIso s)
    {F G : DerivedCategory A ⥤ E} (α β : F ⟶ G)
    (h : ∀ X, P X → α.app (DerivedCategory.Q.obj X) = β.app (DerivedCategory.Q.obj X)) :
    α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro X
  obtain ⟨Y, s, hY, hs⟩ := res X
  have := hs
  apply (cancel_epi (F.map (DerivedCategory.Q.map s))).1
  rw [α.naturality, β.naturality, h Y hY]

private theorem comparison_on_resolutions
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {E : Type uB} [Category.{vB} E] (P : ObjectProperty (CochainComplex A ℤ))
    (res : ∀ X : CochainComplex A ℤ, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
      P Y ∧ QuasiIso s)
    (U V : DerivedCategory A ⥤ E) (H : CochainComplex A ℤ ⥤ E)
    (α : DerivedCategory.Q ⋙ U ⟶ H) (β : DerivedCategory.Q ⋙ V ⟶ H)
    (hα : ∀ X, P X → IsIso (α.app X)) (hβ : ∀ X, P X → IsIso (β.app X)) :
    ∃ v : U ≅ V, (∀ X, v.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = α.app X) ∧
      ∀ v' : U ≅ V,
        (∀ X, P X → v'.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = α.app X) → v' = v := by
  classical
  let p := HomotopyCategory.quotient A (.up ℤ)
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ P X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y, s, hY, hs⟩ := res X
    exact ⟨⟨p.obj Y, hY⟩, p.map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  obtain ⟨ff⟩ := resolvingRepresentativesFullyFaithfulWhiskering E p
    HomotopyCategory.quotient_obj_surjective (HomotopyCategory.quasiIso A (.up ℤ))
    DerivedCategory.Qh P S (fun _ ↦ Iff.rfl) hres
  let r := P.ι ⋙ DerivedCategory.Q
  let i := Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso (NatIso.prod i i))
  let c : r ⋙ U ≅ r ⋙ V := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (α.app X.obj) (hα X.obj X.property) ≪≫
      (@asIso _ _ _ _ (β.app X.obj) (hβ X.obj X.property)).symm) (by
      intro X Y s
      have := hβ X.obj X.property
      have := hβ Y.obj Y.property
      change (DerivedCategory.Q ⋙ U).map s.hom ≫ α.app Y.obj ≫ inv (β.app Y.obj) =
        (α.app X.obj ≫ inv (β.app X.obj)) ≫ (DerivedCategory.Q ⋙ V).map s.hom
      rw [← Category.assoc, α.naturality, Category.assoc, Category.assoc]
      apply congrArg (α.app X.obj ≫ ·)
      apply (cancel_mono (β.app Y.obj)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [β.naturality s.hom]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp])
  let c₂ : r.prod r ⋙ (Prod.fst _ _ ⋙ U) ≅ r.prod r ⋙ (Prod.fst _ _ ⋙ V) :=
    NatIso.ofComponents (fun X ↦ c.app X.1) (fun s ↦ c.hom.naturality s.1)
  let v₂ := ff'.preimageIso c₂
  let v : U ≅ V := NatIso.ofComponents (fun M ↦ v₂.app (M, M))
    (fun s ↦ v₂.hom.naturality (Prod.mkHom s s))
  have hv (X : CochainComplex A ℤ) (hX : P X) :
      v.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = α.app X := by
    have := hβ X hX
    have he := congrArg (fun t ↦ t.app (⟨X, hX⟩, ⟨X, hX⟩))
      (ff'.map_preimage c₂.hom)
    change v.hom.app (DerivedCategory.Q.obj X) = α.app X ≫ inv (β.app X) at he
    rw [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hvall (X : CochainComplex A ℤ) :
      v.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = α.app X := by
    obtain ⟨Y, s, hY, hs⟩ := res X
    have := hs
    apply (cancel_epi (U.map (DerivedCategory.Q.map s))).1
    have hb := β.naturality s
    dsimp only [Functor.comp_map] at hb
    rw [← Category.assoc, v.hom.naturality, Category.assoc,
      hb, ← Category.assoc, hv Y hY]
    exact (α.naturality s).symm
  refine ⟨v, hvall, ?_⟩
  intro v' hv'
  apply Iso.ext
  apply ext_on_resolutions P res
  intro X hX
  have := hβ X hX
  exact (cancel_mono (β.app X)).1 ((hv' X hX).trans (hv X hX).symm)

/-- The dependency's module category, with the standard commutative-ring forgetful map.
This transparent abbreviation shares the existing construction and its universe instances.
Source: Stacks Modules on Sites, Section 03DA
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section Evaluation

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The degreewise identity commuting levelwise pullback and evaluation of complexes.
Source: Stacks Tag 06XN, evaluation calculation before localization
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
def evaluationComplexIso (F : A ⥤ B) [F.Additive] (n : ℕ) :
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)) ⋙
        (((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)) ≅
      (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)) ⋙
        F.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex
    (Iso.refl _ : (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙
      (evaluation ℕᵒᵖ B).obj (op n) ≅ (evaluation ℕᵒᵖ A).obj (op n) ⋙ F) (.up ℤ)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]

/-- Canonical localization of any composite tower transition, with no chosen derived map.
Source: Stacks Tags 05RU and 06XN; exact evaluation of strict towers
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
noncomputable def derivedTransition (a b : ℕ) (h : a ≤ b) :
    ((evaluation ℕᵒᵖ A).obj (op b)).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _ _ _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ A).map (homOfLE h).op) (.up ℤ)) DerivedCategory.Q)

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] in
private def complexTransition (a b : ℕ) (h : a ≤ b) :
    (((evaluation ℕᵒᵖ A).obj (op b)).mapHomologicalComplex (.up ℤ)) ⟶
      (((evaluation ℕᵒᵖ A).obj (op a)).mapHomologicalComplex (.up ℤ)) :=
  NatTrans.mapHomologicalComplex ((evaluation ℕᵒᵖ A).map (homOfLE h).op) (.up ℤ)

@[reassoc]
private theorem transition_factor (a b : ℕ) (h : a ≤ b)
    (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (derivedTransition (A := A) a b h).app (DerivedCategory.Q.obj P) ≫
        ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategoryFactors.hom.app P =
      ((evaluation ℕᵒᵖ A).obj (op b)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((complexTransition (A := A) a b h).app P) := by
  unfold derivedTransition
  rw [Localization.liftNatTrans_app]
  change (_ ≫ _ ≫
    ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategoryFactors.inv.app P) ≫
      ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategoryFactors.hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

end Evaluation

section Normalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]

/-- The type of the stated comparison at a fixed level.
Source: Stacks Tag 06XN, evaluation subargument
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
abbrev Comparison (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)) (n : ℕ) :=
  Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ L

/-- The counit equation on a specified class of strict tower representatives.
Source: Stacks Tag 06XN (dual), counits on computing representatives
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

The main theorem supplies exactly the objectwise K-flat flat-term class. This equation
is `v ≫ ε = evaluation(τ)` with the canonical exact-localization factors displayed. -/
def IsNormalizedOn (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (ε : (DerivedCategory.Q (C := A)) ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ (DerivedCategory.Q (C := B)))
    (τ : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)) ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ⋙
        (DerivedCategory.Q (C := ℕᵒᵖ ⥤ B)))
    (good : CochainComplex (ℕᵒᵖ ⥤ A) ℤ → Prop) (n : ℕ)
    (v : Comparison (A := A) (B := B) L Lt n) : Prop :=
  ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, good P →
    v.hom.app ((DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)).obj P) ≫
        L.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P) ≫
        ε.app (P.asFunctor.obj (op n)) =
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (τ.app P) ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (DerivedCategory.Q (C := B)).map ((evaluationComplexIso F n).hom.app P)

private noncomputable def towerCounitAt (F : A ⥤ B) [F.Additive]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q) (n : ℕ) :
    DerivedCategory.Q ⋙ (Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory) ⟶
      ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight τ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≫
    Functor.whiskerLeft
      (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ))
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom ≫
    Functor.whiskerRight (evaluationComplexIso F n).hom DerivedCategory.Q

private noncomputable def levelCounitAt (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (n : ℕ) :
    DerivedCategory.Q ⋙ (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ L) ⟶
      ((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom L ≫
    Functor.whiskerLeft (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)) ε

omit [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)] in
private theorem levelCounit_transition (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a b : ℕ) (h : a ≤ b) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    L.map ((derivedTransition (A := A) a b h).app (DerivedCategory.Q.obj P)) ≫
        (levelCounitAt F L ε a).app P =
      (levelCounitAt F L ε b).app P ≫
        DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map ((complexTransition (A := A) a b h).app P)) := by
  change L.map _ ≫ L.map _ ≫ ε.app _ = (L.map _ ≫ ε.app _) ≫ _
  have he := ε.naturality ((complexTransition (A := A) a b h).app P)
  dsimp only [Functor.comp_map] at he
  rw [← L.map_comp_assoc, transition_factor, L.map_comp]
  simp only [Category.assoc]
  rw [he]

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)] in
private theorem complex_transition (F : A ⥤ B) [F.Additive]
    (a b : ℕ) (h : a ≤ b) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (complexTransition (A := B) a b h).app
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (evaluationComplexIso F a).hom.app P =
      (evaluationComplexIso F b).hom.app P ≫
        (F.mapHomologicalComplex (.up ℤ)).map ((complexTransition (A := A) a b h).app P) := by
  ext q
  change F.map ((P.X q).map (homOfLE h).op) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map ((P.X q).map (homOfLE h).op)
  simp only [Category.comp_id, Category.id_comp]

omit [HasDerivedCategory.{wA} A] in
private theorem towerCounit_transition (F : A ⥤ B) [F.Additive]
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    (a b : ℕ) (h : a ≤ b) (P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (derivedTransition (A := B) a b h).app (Lt.obj (DerivedCategory.Q.obj P)) ≫
        (towerCounitAt F Lt τ a).app P =
      (towerCounitAt F Lt τ b).app P ≫
        DerivedCategory.Q.map
          ((F.mapHomologicalComplex (.up ℤ)).map ((complexTransition (A := A) a b h).app P)) := by
  have hn := (derivedTransition (A := B) a b h).naturality (τ.app P)
  dsimp only [Functor.comp_obj] at hn
  dsimp only [towerCounitAt, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [← Category.assoc, ← hn, Category.assoc, transition_factor_assoc]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [complex_transition]

-- This categorical calculation is independent of the sheaf-module implementation.
private theorem normalized_evaluation_of_resolutions (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (ε : DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)
    (good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ A) ℤ))
    (res : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (s : Y ⟶ X), good Y ∧ QuasiIso s)
    (he : ∀ P, good P → ∀ n : ℕ, IsIso (ε.app (P.asFunctor.obj (op n))))
    (ht : ∀ P, good P → IsIso (τ.app P)) :
    ∃ v : ∀ n : ℕ, Comparison (A := A) (B := B) L Lt n,
      (∀ n : ℕ, IsNormalizedOn F L Lt ε τ good n (v n)) ∧
      (∀ (n : ℕ) (v' : Comparison (A := A) (B := B) L Lt n),
        IsNormalizedOn F L Lt ε τ good n v' → v' = v n) ∧
      ∀ (a b : ℕ) (h : a ≤ b) (M : DerivedCategory (ℕᵒᵖ ⥤ A)),
        (v b).hom.app M ≫ L.map ((derivedTransition (A := A) a b h).app M) =
          (derivedTransition (A := B) a b h).app (Lt.obj M) ≫ (v a).hom.app M := by
  classical
  have hc (n : ℕ) := comparison_on_resolutions good res
    (Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory)
    (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ L)
    ((((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)) ⋙
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (towerCounitAt F Lt τ n) (levelCounitAt F L ε n)
    (fun P hP ↦ by
      have := ht P hP
      dsimp only [towerCounitAt, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app]
      infer_instance)
    (fun P hP ↦ by
      have := he P hP n
      change IsIso (L.map _ ≫ ε.app (P.asFunctor.obj (op n)))
      infer_instance)
  choose v hv hu using hc
  refine ⟨v, ?_, ?_, ?_⟩
  · intro n P hP
    exact hv n P
  · intro n v' hv'
    exact hu n v' (fun P hP ↦ hv' P hP)
  · intro a b h M
    let α : Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op b)).mapDerivedCategory ⟶
        ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategory ⋙ L :=
      (v b).hom ≫ Functor.whiskerRight (derivedTransition a b h) L
    let β : Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op b)).mapDerivedCategory ⟶
        ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategory ⋙ L :=
      Functor.whiskerLeft Lt (derivedTransition a b h) ≫ (v a).hom
    have hαβ : α = β := by
      apply ext_on_resolutions good res
      intro P hP
      have := he P hP a
      have hi : IsIso ((levelCounitAt F L ε a).app P) := by
        change IsIso (L.map _ ≫ ε.app (P.asFunctor.obj (op a)))
        infer_instance
      apply (cancel_mono ((levelCounitAt F L ε a).app P)).1
      change ((v b).hom.app _ ≫ L.map _) ≫ _ =
        ((derivedTransition (A := B) a b h).app _ ≫ (v a).hom.app _) ≫ _
      rw [Category.assoc, levelCounit_transition, ← Category.assoc, hv b P,
        Category.assoc, hv a P]
      exact (towerCounit_transition F Lt τ a b h P).symm
    exact NatTrans.congr_app hαβ M

end Normalization

/-- The existing objectwise K-flat flat-term class, as a predicate on strict tower complexes.
Source: Stacks Tag 06XN applied with the diagram replacements of Tags 077J and 06YY
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
def IsGoodTower {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) : Prop :=
  (∀ k : ℕ, CochainComplex.IsAcyclicTensorKFlat (R := R) (P.asFunctor.obj (op k))) ∧
    ∀ (k : ℕ) (q : ℤ), SheafOfModules.IsFlat (R := R) ((P.X q).obj (op k))

private def untranspose {A : Type*} [Category* A] [HasZeroMorphisms A]
    (P : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := P ⋙ HomologicalComplex.eval A (.up ℤ) i
  d i j :=
    { app := fun n ↦ (P.obj n).d i j
      naturality := fun n m g ↦ (P.map g).comm i j }
  shape i j h := by ext n; exact (P.obj n).shape i j h
  d_comp_d' i j k _ _ := by ext n; exact (P.obj n).d_comp_d i j k

private def untransposeMap {A : Type*} [Category* A] [HasZeroMorphisms A]
    {P Q : ℕᵒᵖ ⥤ CochainComplex A ℤ} (p : P ⟶ Q) :
    untranspose P ⟶ untranspose Q where
  f i :=
    { app := fun n ↦ (p.app n).f i
      naturality := fun n m g ↦ congrArg (fun z ↦ z.f i) (p.naturality g) }
  comm' i j _ := by ext n; exact (p.app n).comm i j

private theorem tower_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (X : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) :
    ∃ (P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) (s : P ⟶ X),
      IsGoodTower R P ∧ QuasiIso s := by
  let e := ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ
  obtain ⟨P, p, hP, hf, hp, _⟩ :=
    CochainComplex.exists_diagram_isKFlatResolution J R (e.inverse ⋙ X.asFunctor)
  let P' := e.functor ⋙ P
  let p' : P' ⟶ X.asFunctor := Functor.whiskerLeft e.functor p
  let s : untranspose P' ⟶ X := untransposeMap p'
  refine ⟨untranspose P', s, ⟨fun n ↦ hP (e.functor.obj (op n)),
    fun n ↦ hf (e.functor.obj (op n))⟩, ?_⟩
  exact (HomologicalComplex.quasiIso_iff_evaluation s).2
    (fun n ↦ hp (e.functor.obj n))

private theorem single_resolutions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (X : CochainComplex (Modules R) ℤ) :
    ∃ (P : CochainComplex (Modules R) ℤ) (s : P ⟶ X),
      (P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) ∧ QuasiIso s := by
  let E := (evaluation ℕᵒᵖ (Modules R)).obj (op 0)
  let T := (Functor.const ℕᵒᵖ : Modules R ⥤ ℕᵒᵖ ⥤ Modules R).mapHomologicalComplex
    (.up ℤ)
  obtain ⟨P, s, hP, hs⟩ := tower_resolutions J R (T.obj X)
  exact ⟨P.asFunctor.obj (op 0), (E.mapHomologicalComplex (.up ℤ)).map s,
    ⟨hP.1 0, hP.2 0⟩, (HomologicalComplex.quasiIso_iff_evaluation s).1 hs (op 0)⟩

section RingedTopoi

variable {C D : Type u}

variable [SmallCategory C]

variable [SmallCategory D]

variable (J : GrothendieckTopology C)

variable (K : GrothendieckTopology D)

variable (R : Sheaf J CommRingCat.{u})

variable (S : Sheaf K CommRingCat.{u})

variable (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

variable (F : Modules R ⥤
        Modules S)

variable [F.Additive]

variable (adj : F ⊣ f.modules)

variable [HasDerivedCategory.{wA} (Modules R)]

variable [HasDerivedCategory.{wB} (Modules S)]

variable [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ Modules R)]

variable [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ Modules S)]

variable (L : DerivedCategory (Modules R) ⥤
        DerivedCategory (Modules S))

variable (Lt : DerivedCategory (ℕᵒᵖ ⥤ Modules R) ⥤
        DerivedCategory (ℕᵒᵖ ⥤ Modules S))

variable (ε : (DerivedCategory.Q (C := (Modules R))) ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ (DerivedCategory.Q (C := (Modules S))))

variable (τ : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ (Modules R))) ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F).mapHomologicalComplex
        (.up ℤ) ⋙
        (DerivedCategory.Q (C := ℕᵒᵖ ⥤ (Modules S))))

variable [hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]

variable [hLt : Lt.IsLeftDerivedFunctor τ
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (Modules R)) (.up ℤ))]

omit [HasDerivedCategory.{wA} (Modules R)] [HasDerivedCategory.{wB} (Modules S)]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ Modules S)] in
include adj in
private theorem single_preserves
    {X Y : CochainComplex (Modules R) ℤ} (s : X ⟶ Y)
    (hX : X.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (X.X q))
    (hY : Y.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (Y.X q))
    (hs : QuasiIso s) : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map s) := by
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let e := ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ
  let I := ULiftHom.{u} (ULift.{u} ℕᵒᵖ)
  have ht := CochainComplex.diagram_pullback_quasiIso J K R S f F adj
    ((Functor.const I).map s) (fun _ ↦ hX.1) (fun _ ↦ hY.1)
    (fun _ ↦ hX.2) (fun _ ↦ hY.2) (fun _ ↦ hs)
  exact ht (e.functor.obj (op 0))

omit [HasDerivedCategory.{wA} (Modules R)] [HasDerivedCategory.{wB} (Modules S)]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ Modules R)]
  [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ Modules S)] in
include adj in
private theorem tower_preserves
    {X Y : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ} (s : X ⟶ Y)
    (hX : IsGoodTower R X) (hY : IsGoodTower R Y) (hs : QuasiIso s) :
    QuasiIso
      ((((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F).mapHomologicalComplex
        (.up ℤ)).map s) := by
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let e := ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ
  let t := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map s
  have ht := CochainComplex.diagram_pullback_quasiIso J K R S f F adj
    (Functor.whiskerLeft e.inverse t)
    (fun j ↦ hX.1 (unop (e.inverse.obj j)))
    (fun j ↦ hY.1 (unop (e.inverse.obj j)))
    (fun j ↦ hX.2 (unop (e.inverse.obj j)))
    (fun j ↦ hY.2 (unop (e.inverse.obj j)))
    (fun j ↦ (HomologicalComplex.quasiIso_iff_evaluation s).1 hs (e.inverse.obj j))
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro j
  exact ht (e.functor.obj j)

include adj hL hLt

/-- Unique representative normalization of derived tower evaluation and all transitions.
Source: Stacks Tag 06XN, `lemma-find-existence-computes` (dual), completed-pullback
invocation, evaluation subargument Step 4
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

Here `F ⊣ f.modules` specifies the usual module pullback, namely inverse image followed
by extension of scalars, as in `diagram_pullback_quasiIso`. The two universal pairs are
arbitrary; no particular choice of derived pullback or counit is imposed.

Proof:
1. Exact evaluation has the displayed canonical localization factorization. On
complexes, evaluation commutes with levelwise `F` by the degreewise identity, including
all composite transition maps (lem-weil-tower-category-levelwise-abelian,
lem-weil-pbc-exact-functor-derived-factorization, def-weil-inverse-system).
2. Resolve strict towers by objectwise K-flat flat-term complexes using
lem-weil-pbc-diagram-kflat-replacements. Its one-object case supplies the corresponding
class for single complexes. Evaluation sends the tower class into the single class.
3. Apply lem-pur-left-derived-from-kflat-class. The two counits are invertible on
these classes. Uniqueness of universal pairs transfers this computation to the chosen
pairs `L, ε` and `Lt, τ` (equivalently use the homotopy-category localization).
4. On good representatives set `v = evaluation(τ) ≫ ε⁻¹`, with the displayed factors.
Naturality of both counits makes this a natural isomorphism on the full good class.
5. Use lem-weil-pbc-resolving-representative-whiskering with `p = id` and `q = Qh`.
Quasi-isomorphisms admit a right calculus by
lem-pc-quasi-isomorphisms-multiplicative-system. Its unary consequence follows by
pullback along the first projection and restriction along the diagonal. Thus restriction
to good representatives is fully faithful. The quotient from complexes to the homotopy
category is full and surjective on objects, so the same calculation applies to `Q`.
6. Extend the comparison and its inverse by fullness. Faithfulness proves the inverse
identities. Cancel the invertible single-level counit to get uniqueness at each level.
7. For every `b ≥ a`, compute on a good strict tower: counit naturality for its transition
and naturality of the target evaluation transition at `τ` give
`v_b ≫ L(d) ≫ ε_a = d' ≫ v_a ≫ ε_a`. Cancel `ε_a`.
8. Faithfulness extends this equality to every derived strict tower. When `a = b`
the identity transitions give the same equality, so no boundary case is omitted. -/
theorem exists_unique_normalized_evaluation :
    ∃ v : ∀ n : ℕ, Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n,
      (∀ n : ℕ, IsNormalizedOn F L Lt ε τ (IsGoodTower R) n (v n)) ∧
      (∀ (n : ℕ) (v' : Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n),
        IsNormalizedOn F L Lt ε τ (IsGoodTower R) n v' → v' = v n) ∧
      ∀ (a b : ℕ) (h : a ≤ b)
        (M : DerivedCategory (ℕᵒᵖ ⥤ (Modules R))),
        (v b).hom.app M ≫ L.map ((derivedTransition (A := (Modules R)) a b h).app M) =
          (derivedTransition (A := (Modules S)) a b h).app (Lt.obj M) ≫
            (v a).hom.app M := by
  classical
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  have : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let good : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) := IsGoodTower R
  let single : CochainComplex (Modules R) ℤ → Prop := fun P ↦
    P.IsAcyclicTensorKFlat ∧ ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)
  let Ft := (Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F
  have he := counit_computes F single (single_resolutions J R)
    (single_preserves J K R S f F adj) L ε
  have ht := counit_computes Ft good (tower_resolutions J R)
    (tower_preserves J K R S f F adj) Lt τ
  exact normalized_evaluation_of_resolutions F L Lt ε τ good (tower_resolutions J R)
    (fun P hP n ↦ he (P.asFunctor.obj (op n)) ⟨hP.1 n, hP.2 n⟩) ht

end RingedTopoi

end CategoryTheory.DerivedTowerPullback

