/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization
import WeilConjectures.CategoryTheory.StageSystem.Morphism.StageSystemAdjunction

/-! # Adjunction for the realized common-stage compact-support action

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, common finite-field
passage and final exceptional-adjunction sentence; coefficient adjunction descent.
(blueprint: lem-sf-compact-support-stage-action-adjunction)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  WeilConjectures.sfRationalScalarExtension
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer

attribute [local instance 2000] Shrink.instField

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem

universe u w u₁ v₁ u₂ v₂

open CategoryTheory AlgebraicGeometry

private theorem mate_unit
    {A : Type u₁} {B : Type u₂} {A' : Type u₁} {B' : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₁} A'] [Category.{v₂} B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (a : F ⊣ G) (a' : F' ⊣ G') (TX : A ⥤ A') (TY : B ⥤ B')
    (q : F ⋙ TY ≅ TX ⋙ F') (b : G ⋙ TX ≅ TY ⋙ G')
    (hc : ∀ L, q.hom.app (G.obj L) ≫ F'.map (b.hom.app L) ≫
      a'.counit.app (TY.obj L) = TY.map (a.counit.app L)) (K : A) :
    TX.map (a.unit.app K) ≫ b.hom.app (F.obj K) ≫
      G'.map (q.hom.app K) = a'.unit.app (TX.obj K) := by
  apply (a'.homEquiv _ _).symm.injective
  change F'.map _ ≫ a'.counit.app _ = F'.map _ ≫ a'.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  erw [a'.counit_naturality]
  rw [← Category.assoc (F'.map (b.hom.app _))]
  have ht : F'.map (b.hom.app (F.obj K)) ≫ a'.counit.app (TY.obj (F.obj K)) =
      q.inv.app (G.obj (F.obj K)) ≫ TY.map (a.counit.app (F.obj K)) := by
    rw [← hc (F.obj K), ← Category.assoc, ← Category.assoc]
    simp only [Iso.inv_hom_id_app, Category.id_comp]
  rw [ht]
  have hn := q.inv.naturality (a.unit.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (TY.map _) (TY.map _), ← TY.map_comp]
  erw [a.left_triangle_components K]
  change q.inv.app K ≫ TY.map (𝟙 (F.obj K)) ≫ q.hom.app K =
    F'.map (a'.unit.app (TX.obj K)) ≫ a'.counit.app (F'.obj (TX.obj K))
  rw [TY.map_id]
  calc
    _ = q.inv.app K ≫ q.hom.app K :=
      congrArg (fun t ↦ q.inv.app K ≫ t) (Category.id_comp (q.hom.app K))
    _ = 𝟙 _ := q.inv_hom_id_app K
    _ = _ := (a'.left_triangle_components (TX.obj K)).symm

private theorem stage_left_adjoint
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T)
    (G : ∀ i, D i ⥤ C i) (a : ∀ i, F.Φ i ⊣ G i)
    (b : ∀ {i j} (h : i ≤ j), G i ⋙ S.T h ≅ T.T h ⋙ G j)
    (hc : ∀ {i j} (h : i ≤ j) (L : D i),
      (F.β h).hom.app ((G i).obj L) ≫ (F.Φ j).map ((b h).hom.app L) ≫
        (a j).counit.app ((T.T h).obj L) = (T.T h).map ((a i).counit.app L)) :
    F.functor.IsLeftAdjoint := by
  let R : T.Morphism S :=
    { Φ := G
      β := b
      coh := by
        intro i j k h h' L
        apply ((a k).homEquiv _ _).symm.injective
        change (F.Φ k).map _ ≫ (a k).counit.app _ =
          (F.Φ k).map _ ≫ (a k).counit.app _
        simp only [Functor.map_comp, Category.assoc]
        erw [(a k).counit_naturality]
        apply (cancel_epi ((T.T h').map ((F.β h).hom.app ((G i).obj L)) ≫
          (F.β h').hom.app ((S.T h).obj ((G i).obj L)))).1
        simp only [Category.assoc]
        have hn := (F.β h').hom.naturality ((b h).hom.app L)
        dsimp only [Functor.comp_map] at hn
        have hα := (T.assoc h h').hom.naturality ((a i).counit.app L)
        dsimp only [Functor.comp_map] at hα
        calc
          _ = (T.T h').map ((F.β h).hom.app ((G i).obj L)) ≫
              (T.T h').map ((F.Φ j).map ((b h).hom.app L)) ≫
              (F.β h').hom.app ((G j).obj ((T.T h).obj L)) ≫
              (F.Φ k).map ((b h').hom.app ((T.T h).obj L)) ≫
              (a k).counit.app ((T.T h').obj ((T.T h).obj L)) ≫
              (T.assoc h h').hom.app L := by rw [reassoc_of% hn]
          _ = (T.T h').map ((F.β h).hom.app ((G i).obj L)) ≫
              (T.T h').map ((F.Φ j).map ((b h).hom.app L)) ≫
              (T.T h').map ((a j).counit.app ((T.T h).obj L)) ≫
              (T.assoc h h').hom.app L := by rw [reassoc_of% (hc h' ((T.T h).obj L))]
          _ = (T.T h').map ((T.T h).map ((a i).counit.app L)) ≫
              (T.assoc h h').hom.app L := by
            rw [← (T.T h').map_comp_assoc, ← (T.T h').map_comp_assoc,
              Category.assoc, hc]
          _ = (T.assoc h h').hom.app ((F.Φ i).obj ((G i).obj L)) ≫
              (T.T (h.trans h')).map ((a i).counit.app L) := hα
          _ = (T.assoc h h').hom.app ((F.Φ i).obj ((G i).obj L)) ≫
              (F.β (h.trans h')).hom.app ((G i).obj L) ≫
              (F.Φ k).map ((b (h.trans h')).hom.app L) ≫
              (a k).counit.app ((T.T (h.trans h')).obj L) := by rw [hc]
          _ = _ := by rw [← reassoc_of% (F.coh h h' ((G i).obj L))] }
  let unit : StageSystem.Morphism.Hom (StageSystem.Morphism.id S) (F.comp R) :=
    { τ := fun i ↦ (a i).unit
      comm := by
        intro i j h K
        simp only [StageSystem.Morphism.comp_β_hom_app,
          StageSystem.Morphism.id_β_hom_app]
        exact (mate_unit (a i) (a j) (S.T h) (T.T h) (F.β h) (b h) (hc h) K).trans
          (Category.id_comp _).symm }
  let counit : StageSystem.Morphism.Hom (R.comp F) (StageSystem.Morphism.id T) :=
    { τ := fun i ↦ (a i).counit
      comm := by
        intro i j h L
        simp only [StageSystem.Morphism.comp_β_hom_app,
          StageSystem.Morphism.id_β_hom_app]
        exact (Category.comp_id _).trans ((hc h L).symm.trans
          (Category.assoc _ _ _).symm) }
  exact (StageSystem.Morphism.adjunction F R a unit counit (fun _ ↦ rfl)
    (fun _ ↦ rfl)).isLeftAdjoint

private def adjunction_cast
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    {F F' : A ⥤ B} {G : B ⥤ A} (h : F = F') (a : F' ⊣ G) : F ⊣ G :=
  h.symm ▸ a

private def comparison_cast
    {A : Type u₁} {B : Type u₂} {A' : Type u₁} {B' : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₁} A'] [Category.{v₂} B']
    {G : B ⥤ A} {G' : B' ⥤ A'}
    {TX TX' : A ⥤ A'} {TY TY' : B ⥤ B'}
    (hx : TX = TX') (hy : TY = TY') (b : G ⋙ TX' ≅ TY' ⋙ G') :
    G ⋙ TX ≅ TY ⋙ G' := by
  subst TX' TY'
  exact b

private theorem comparison_cast_counit
    {A : Type u₁} {B : Type u₂} {A' : Type u₁} {B' : Type u₂}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₁} A'] [Category.{v₂} B']
    {F F₀ : A ⥤ B} {G : B ⥤ A} {F' F₁ : A' ⥤ B'} {G' : B' ⥤ A'}
    {TX TX' : A ⥤ A'} {TY TY' : B ⥤ B'}
    (hF : F = F₀) (hF' : F' = F₁) (hx : TX = TX') (hy : TY = TY')
    (a : F₀ ⊣ G) (a' : F₁ ⊣ G')
    (q : F ⋙ TY ≅ TX ⋙ F') (q' : F₀ ⋙ TY' ≅ TX' ⋙ F₁)
    (hq : HEq q q') (b : G ⋙ TX' ≅ TY' ⋙ G')
    (hc : ∀ L, q'.hom.app (G.obj L) ≫ F₁.map (b.hom.app L) ≫
      a'.counit.app (TY'.obj L) = TY'.map (a.counit.app L)) (L : B) :
    q.hom.app (G.obj L) ≫ F'.map ((comparison_cast hx hy b).hom.app L) ≫
      (adjunction_cast hF' a').counit.app (TY.obj L) =
        TY.map ((adjunction_cast hF a).counit.app L) := by
  subst F₀ F₁ TX' TY'
  cases eq_of_heq hq
  exact hc L

namespace WeilConjectures.LocallyFiniteAdicCompactSupport

private noncomputable abbrev stageField (l : ℕ) [Fact l.Prime] (Ω : Type)
    [Field Ω] [Algebra (Padic l) Ω]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    ConstructibleExceptionalCoefficients.FieldStage.{u} l where
  carrier := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E

set_option maxHeartbeats 400000 in
-- The two finite-stage presentations require normalizing transported field instances.
private theorem finite_stage_left_adjoint
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [IsAlgClosure (Padic l) (ULift.{u} Ω)]
    (X Y : Scheme.{u})
    (F : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (O : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      ConstructibleExceptionalCoefficients.Operation l (ULift.{u} Ω) X Y
        (.rational (stageField l Ω E)))
    (d : ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L),
      ConstructibleExceptionalCoefficients.CounitFieldComparison l (ULift.{u} Ω)
        (O E) (O L)
        (ConstructibleExceptionalCoefficients.rationalScalar l (ULift.{u} Ω)
          (stageField l Ω E) (stageField l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X)
        (ConstructibleExceptionalCoefficients.rationalScalar l (ULift.{u} Ω)
          (stageField l Ω E) (stageField l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Y))
    (hf : ∀ E, HEq (F.Φ E) (O E).F)
    (hs : ∀ E L h, HEq (F.β h) (d E L h).q) : F.functor.IsLeftAdjoint := by
  let : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      Category.{u + 2} (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :=
    fun E ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω X E
  let : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
      Category.{u + 2} (GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :=
    fun E ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory l Ω Y E
  let G (E : AlgebraicallyClosedCoefficients.Index l Ω) :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E ⥤
        GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E := by
    have g := (O E).G
    dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory,
      ConstructibleExceptionalCoefficients.C, ConstructibleExceptionalCoefficients.category,
      stageField] at g ⊢
    exact g
  have hF (E : AlgebraicallyClosedCoefficients.Index l Ω) := by
    have hh := hf E
    dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory,
      ConstructibleExceptionalCoefficients.C, ConstructibleExceptionalCoefficients.category,
      stageField] at hh
    exact eq_of_heq hh
  let a (E : AlgebraicallyClosedCoefficients.Index l Ω) :
      F.Φ E ⊣ G E := by
    have aa := (O E).adjunction
    dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory,
      ConstructibleExceptionalCoefficients.C, ConstructibleExceptionalCoefficients.category,
      stageField] at aa
    dsimp only [G, GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory,
      ConstructibleExceptionalCoefficients.C, ConstructibleExceptionalCoefficients.category,
      stageField]
    exact adjunction_cast (hF E) aa
  have ht (Z : Scheme.{u}) (E L : AlgebraicallyClosedCoefficients.Index l Ω)
      (h : E ≤ L) :
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h =
        ConstructibleExceptionalCoefficients.rationalScalar l (ULift.{u} Ω)
          (stageField l Ω E) (stageField l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) Z := by
    unfold GeneralAlgebraicallyClosedCoefficients.stageSystem
    exact (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
      l Ω Z).exists.choose_spec.1 E L h
  let b {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L) :=
    comparison_cast (ht X E L h) (ht Y E L h)
      (d E L h).b
  apply stage_left_adjoint F G a b
  intro E L h K
  let d := d E L h
  let := d.shiftX
  let := d.shiftY
  exact comparison_cast_counit (hF E) (hF L) (ht X E L h) (ht Y E L h)
    (O E).adjunction
    (O L).adjunction
    (F.β h) d.q (hs E L h) d.b d.comparison.counit K

/-- The common-stage action specified by the normalized finite coefficient adjunctions
has a right adjoint, on the original unlifted coefficient category.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, common finite-field
passage and final exceptional-adjunction sentence; the coefficient construction's rational
adjunctions and scalar counit comparisons.
(blueprint: lem-sf-compact-support-stage-action-adjunction)

Proof: for each finite subfield E of PadicAlgCl, use the rational operation in P at
finiteField E. Its left functor is S.system.Φ E by S.finite. Its right functor is the right
adjoint recorded by that operation. For E ≤ L use P.fields.rationalComparison: its q is
S.system.β by S.scalar, and its b is the right-functor transition. The coefficient coherence
theorem gives the tower equation for b with the same tensor associators as the published
stage systems. Thus these right functors descend to the Y-to-X pair-category functor.
The counit equation of each coefficient comparison, and the unit equation obtained by
transposing it, say that the finite units and counits are compatible with these transitions.
Descend them and apply StageSystem.Morphism.adjunction. Its triangle identities are the
finite-stage triangle identities included into the pair category. The construction retains
all stages and applies to identity extensions, zero objects and empty schemes. The lifted
auxiliary closure is used only to obtain P's rational operations, whose categories use the
actual finite subfields of the unlifted PadicAlgCl; no lift of the output category occurs. -/
theorem compactSupport_stageAction_isLeftAdjoint
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : ConstructibleExceptionalCoefficients.CoefficientConstruction l
      (ULift.{u} (PadicAlgCl l)) D hl (f := f)) (c : Compactification f)
    (S : StageAction l D hl P c) : S.system.functor.IsLeftAdjoint := by
  exact finite_stage_left_adjoint l (PadicAlgCl l) X Y S.system
    (fun E ↦ P.ring.operation c (.rational (finiteField l E)))
    (fun E L h ↦ P.fields.rationalComparison c (finiteField l E) (finiteField l L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l (PadicAlgCl l) E L h))
    S.finite S.scalar

end WeilConjectures.LocallyFiniteAdicCompactSupport
