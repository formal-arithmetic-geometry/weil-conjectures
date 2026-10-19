/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Adjoint chain maps on restriction kernels: maps and homotopies

Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67; Stacks Project, Derived Categories, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence).
-/

@[expose] public section

noncomputable section

universe u v u' v' w w' w₀ wQ wQc wQd

open CategoryTheory CategoryTheory.Limits CategoryTheory.ShortComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable (Jc : GrothendieckTopology C) (Jd : GrothendieckTopology D)
variable [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]

/-- A monomorphic pair of objects in a site. Source: Milne, Section 9, Theorem 9.4
(blueprint: lem-pur-support-pair-chain-coherence). -/
structure SupportPair where
  /-- The subobject on which sections are restricted. -/
  V : C
  /-- the ambient object -/
  T : C
  /-- The inclusion of the restriction subobject. -/
  m : V ⟶ T
  /-- the inclusion is a monomorphism -/
  mono_m : Mono m

attribute [instance] SupportPair.mono_m

/-- The section functor of sheaves of abelian groups at an object of a site.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def sectionFunctor (J : GrothendieckTopology C) (X : C) :
    Sheaf J AddCommGrpCat.{w₀} ⥤ AddCommGrpCat.{w₀} :=
  (sheafSections J AddCommGrpCat.{w₀}).obj (Opposite.op X)

/-- Evaluation preserves zero maps. Source: Milne, Section 9, Theorem 9.4
(blueprint: lem-pur-support-pair-chain-coherence). -/
instance sectionFunctorPreservesZeroMorphisms (J : GrothendieckTopology C) (X : C) :
    (sectionFunctor J X).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- The restriction map of sections along a morphism of site objects.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def sectionRestriction (J : GrothendieckTopology C) {V T : C} (m : V ⟶ T) :
    sectionFunctor J T ⟶ sectionFunctor J V :=
  (sheafSections J AddCommGrpCat.{w₀}).map m.op

/-- The restriction-kernel complex of a sheaf complex for a pair.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportKernel (J : GrothendieckTopology C) (P : SupportPair (C := C))
    (I : HomologicalComplex (Sheaf J AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)) :
    HomologicalComplex AddCommGrpCat.{w₀} (ComplexShape.up ℤ) :=
  kernel ((NatTrans.mapHomologicalComplex
    (sectionRestriction J P.m) (ComplexShape.up ℤ)).app I)

/-- The three-term restriction diagram associated to a pair and a sheaf complex.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportDiagram (J : GrothendieckTopology C) (P : SupportPair (C := C))
    (I : HomologicalComplex (Sheaf J AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)) :
    ShortComplex (HomologicalComplex AddCommGrpCat.{w₀} (ComplexShape.up ℤ)) :=
  { f := kernel.ι ((NatTrans.mapHomologicalComplex
      (sectionRestriction J P.m) (ComplexShape.up ℤ)).app I)
    g := (NatTrans.mapHomologicalComplex (sectionRestriction J P.m)
      (ComplexShape.up ℤ)).app I
    zero := by simp }

/-- A complex is bounded below when it vanishes in all sufficiently negative degrees.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def BoundedBelow {A : Type w} [Category.{w'} A] [HasZeroMorphisms A] (I :
    HomologicalComplex A (ComplexShape.up ℤ)) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n → IsZero (I.X i)

/-- The degreewise adjoint of a chain map under an adjunction.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def degreewiseAdjoint {A : Type w} {B : Type w'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [L.Additive]
    {I : HomologicalComplex A (ComplexShape.up ℤ)}
    {J : HomologicalComplex B (ComplexShape.up ℤ)}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) (n : ℤ) :
    I.X n ⟶ R.obj (J.X n) :=
  (adj.homEquiv (I.X n) (J.X n)) (h.f n)

/-- The component equations characterizing the map induced by an adjoint chain map.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportPairMapCondition
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    {I : HomologicalComplex (Sheaf Jc AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)}
    {K : HomologicalComplex (Sheaf Jd AddCommGrpCat.{w₀}) (ComplexShape.up ℤ)}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K) : Prop :=
  (∀ n : ℤ, φ.τ₂.f n =
    (sectionFunctor Jc P.T).map (degreewiseAdjoint L
      (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) adj h n) ≫
      (sectionRestriction Jd t).app (K.X n)) ∧
  (∀ n : ℤ, φ.τ₃.f n =
    (sectionFunctor Jc P.V).map (degreewiseAdjoint L
      (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) adj h n) ≫
      (sectionRestriction Jd s).app (K.X n))

/-- The standard derived localization used for the representative clause.
Source: Milne, Section 9, Theorem 9.4; Stacks, Tag 070I
(blueprint: lem-pur-support-pair-chain-coherence). -/
def standardDerivedQ {A : Type w} [Category.{w'} A] [Abelian A]
    [HasDerivedCategory.{wQ} A] : CochainComplex A ℤ ⥤ DerivedCategory A :=
  DerivedCategory.Q

/-- The ordinary diagram map induced by a map of sheaf complexes, specified by its
section components. Source: Milne, Section 9, Theorem 9.4, pair functoriality
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportOrdinaryMapCondition (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ} (g : I ⟶ K)
    (α : supportDiagram J P I ⟶ supportDiagram J P K) : Prop :=
  α.τ₂ = ((sectionFunctor J P.T).mapHomologicalComplex (ComplexShape.up ℤ)).map g ∧
  α.τ₃ = ((sectionFunctor J P.V).mapHomologicalComplex (ComplexShape.up ℤ)).map g

/-- Equality on each of the three cohomology groups, in every integer degree.
Source: Milne, Section 9, Theorem 9.4, and the node's Step 5
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportCohomologyEqual
    {S T : ShortComplex (CochainComplex AddCommGrpCat.{w₀} ℤ)} (φ ψ : S ⟶ T) : Prop :=
  ∀ n : ℤ,
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₁ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₁ ∧
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₂ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₂ ∧
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₃ =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map ψ.τ₃

/-- The three component maps give identifications on cohomology in every degree.
Source: Milne, Section 9, Theorem 9.4, and the node's Step 5
(blueprint: lem-pur-support-pair-chain-coherence). -/
def supportCohomologyIsIso
    {S T : ShortComplex (CochainComplex AddCommGrpCat.{w₀} ℤ)} (φ : S ⟶ T) : Prop :=
  ∀ n : ℤ,
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₁) ∧
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₂) ∧
    IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w₀} (ComplexShape.up ℤ) n).map φ.τ₃)

private instance sectionFunctor_additive (J : GrothendieckTopology C) (X : C) :
    (sectionFunctor J X).Additive where

private instance pairPushforward_additive (u : C ⥤ D) [u.IsContinuous Jc Jd] :
    (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd).Additive where

private def chainAdjoint {A : Type w} {B : Type w'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [L.Additive] [R.Additive]
    {I : CochainComplex A ℤ} {K : CochainComplex B ℤ}
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K) :
    I ⟶ (R.mapHomologicalComplex (.up ℤ)).obj K where
  f n := degreewiseAdjoint L R adj h n
  comm' i j _ := by
    symm
    change I.d i j ≫ adj.homEquiv _ _ (h.f j) =
      adj.homEquiv _ _ (h.f i) ≫ R.map (K.d i j)
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    exact congrArg (adj.homEquiv _ _) (h.comm i j).symm

private def pairSectionMap
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (b : I ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd).mapHomologicalComplex
       (.up ℤ)).obj K)
    {X : C} {Y : D} (t : Y ⟶ u.obj X) :
    ((sectionFunctor Jc X).mapHomologicalComplex (.up ℤ)).obj I ⟶
      ((sectionFunctor Jd Y).mapHomologicalComplex (.up ℤ)).obj K :=
  ((sectionFunctor Jc X).mapHomologicalComplex (.up ℤ)).map b ≫
    (NatTrans.mapHomologicalComplex (sectionRestriction Jd t) (.up ℤ)).app K

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
set_option backward.isDefEq.respectTransparency false in
private lemma pairDegree_square
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {F : Sheaf Jc AddCommGrpCat.{w₀}} {G : Sheaf Jd AddCommGrpCat.{w₀}}
    (b : F ⟶ (u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd).obj G) :
    F.obj.map P.m.op ≫ b.hom.app (Opposite.op P.V) ≫ G.obj.map s.op =
      (b.hom.app (Opposite.op P.T) ≫ G.obj.map t.op) ≫ G.obj.map P'.m.op := by
  rw [← Category.assoc, b.hom.naturality P.m.op]
  change (b.hom.app (Opposite.op P.T) ≫ G.obj.map (u.map P.m).op) ≫ G.obj.map s.op =
    (b.hom.app (Opposite.op P.T) ≫ G.obj.map t.op) ≫ G.obj.map P'.m.op
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp, square]

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
set_option backward.isDefEq.respectTransparency false in
private lemma pairSectionMap_square
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (b : I ⟶ ((u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd).mapHomologicalComplex
       (.up ℤ)).obj K) :
    (supportDiagram Jc P I).g ≫ pairSectionMap Jc Jd u b s =
      pairSectionMap Jc Jd u b t ≫ (supportDiagram Jd P' K).g := by
  apply HomologicalComplex.hom_ext
  intro n
  exact pairDegree_square Jc Jd u P P' t s square (b.f n)

private def kernelDiagramMap
    {A : Type w} [Category.{w'} A] [HasZeroMorphisms A] [HasKernels A]
    {X Y X' Y' : A} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (p : X ⟶ X') (q : Y ⟶ Y') (sq : f ≫ q = p ≫ f') :
    ShortComplex.mk (kernel.ι f) f (kernel.condition f) ⟶
      ShortComplex.mk (kernel.ι f') f' (kernel.condition f') where
  τ₁ := kernel.map f f' p q sq
  τ₂ := p
  τ₃ := q
  comm₁₂ := by simp
  comm₂₃ := sq.symm

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
private lemma pairMap_existsUnique
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K) :
    ∃! φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K,
      supportPairMapCondition Jc Jd u L adj P P' t s h φ := by
  let b := chainAdjoint L _ adj h
  let p := pairSectionMap Jc Jd u b t
  let q := pairSectionMap Jc Jd u b s
  refine ⟨kernelDiagramMap _ _ p q (pairSectionMap_square Jc Jd u P P' t s square b),
    ⟨fun n ↦ rfl, fun n ↦ rfl⟩, ?_⟩
  intro ψ hψ
  have h₂ : ψ.τ₂ = p := HomologicalComplex.hom_ext _ _ hψ.1
  have h₃ : ψ.τ₃ = q := HomologicalComplex.hom_ext _ _ hψ.2
  let : Mono (supportDiagram Jd P' K).f :=
    inferInstanceAs (Mono (kernel.ι _))
  apply ShortComplex.hom_ext
  · apply (cancel_mono (supportDiagram Jd P' K).f).1
    simpa [kernelDiagramMap, supportDiagram, h₂] using ψ.comm₁₂
  · exact h₂
  · exact h₃

set_option backward.isDefEq.respectTransparency false in
private def chainAdjointHomotopy {A : Type w} {B : Type w'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R) [L.Additive] [R.Additive]
    {I : CochainComplex A ℤ} {K : CochainComplex B ℤ}
    {h h' : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K}
    (z : _root_.Homotopy h h') :
    _root_.Homotopy (chainAdjoint L R adj h) (chainAdjoint L R adj h') where
  hom i j := adj.homEquiv _ _ (z.hom i j)
  zero i j hij := by rw [z.zero i j hij]; exact adj.homAddEquiv_zero _ _
  comm i := by
    have hz := z.comm i
    dsimp only [dNext, prevD, AddMonoidHom.mk', AddMonoidHom.coe_mk,
      ZeroHom.coe_mk] at hz
    simp only [Functor.mapHomologicalComplex_obj_d] at hz
    change (adj.homEquiv _ _ (h.f i)) = _
    rw [hz, adj.homAddEquiv_add, adj.homAddEquiv_add,
      adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    rfl

private def pairSectionHomotopy
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    {h h' : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K}
    (z : _root_.Homotopy h h') {X : C} {Y : D} (t : Y ⟶ u.obj X) :
    _root_.Homotopy (pairSectionMap Jc Jd u (chainAdjoint L _ adj h) t)
      (pairSectionMap Jc Jd u (chainAdjoint L _ adj h') t) :=
  ((sectionFunctor Jc X).mapHomotopy (chainAdjointHomotopy L _ adj z)).compRight
    ((NatTrans.mapHomologicalComplex (sectionRestriction Jd t) (.up ℤ)).app K)

private def kernelDegreeLift
    {A : Type w} [Category.{w'} A] [Abelian A]
    {X Y Z : CochainComplex A ℤ} (g : X ⟶ Y) (i j : ℤ)
    (a : Z.X i ⟶ X.X j) (ha : a ≫ g.f j = 0) : Z.X i ⟶ (kernel g).X j :=
  kernel.lift (g.f j) a ha ≫
    inv (kernelComparison g (HomologicalComplex.eval A (.up ℤ) j))

set_option backward.isDefEq.respectTransparency false in
private lemma kernelDegreeLift_ι
    {A : Type w} [Category.{w'} A] [Abelian A]
    {X Y Z : CochainComplex A ℤ} (g : X ⟶ Y) (i j : ℤ)
    (a : Z.X i ⟶ X.X j) (ha : a ≫ g.f j = 0) :
    kernelDegreeLift g i j a ha ≫ (kernel.ι g).f j = a := by
  dsimp only [kernelDegreeLift]
  change (kernel.lift _ a ha ≫ inv (kernelComparison g _)) ≫
    (HomologicalComplex.eval A (.up ℤ) j).map (kernel.ι g) = a
  rw [Category.assoc,
    ← kernelComparison_comp_ι g (HomologicalComplex.eval A (.up ℤ) j),
    IsIso.inv_hom_id_assoc]
  exact kernel.lift_ι (g.f j) a ha

set_option backward.isDefEq.respectTransparency false in
private def kernelMapHomotopy
    {A : Type w} [Category.{w'} A] [Abelian A]
    {X Y X' Y' : CochainComplex A ℤ} (g : X ⟶ Y) (g' : X' ⟶ Y')
    {p p' : X ⟶ X'} {q q' : Y ⟶ Y'}
    (sq : g ≫ q = p ≫ g') (sq' : g ≫ q' = p' ≫ g')
    (H : _root_.Homotopy p p') (H' : _root_.Homotopy q q')
    (compat : ∀ i j, H.hom i j ≫ g'.f j = g.f i ≫ H'.hom i j) :
    _root_.Homotopy (kernel.map g g' p q sq) (kernel.map g g' p' q' sq') where
  hom i j := kernelDegreeLift g' i j ((kernel.ι g).f i ≫ H.hom i j) (by
    rw [Category.assoc, compat, ← Category.assoc]
    have hz := congrArg (fun f ↦ f.f i) (kernel.condition g)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    rw [hz, zero_comp])
  zero i j hij := by
    apply (cancel_mono ((kernel.ι g').f j)).1
    simp [kernelDegreeLift_ι, H.zero i j hij]
  comm i := by
    change (kernel.map g g' p q sq).f i =
      (kernel g).d i ((ComplexShape.up ℤ).next i) ≫
          kernelDegreeLift g' _ _ _ _ +
        kernelDegreeLift g' _ _ _ _ ≫
          (kernel g').d ((ComplexShape.up ℤ).prev i) i +
        (kernel.map g g' p' q' sq').f i
    apply (cancel_mono ((kernel.ι g').f i)).1
    simp only [Preadditive.add_comp, Category.assoc, kernelDegreeLift_ι]
    rw [← (kernel.ι g').comm]
    simp only [← Category.assoc, kernelDegreeLift_ι]
    have hp := congrArg (fun f ↦ f.f i) (kernel.lift_ι g' (kernel.ι g ≫ p)
      (by simp [← sq]))
    have hp' := congrArg (fun f ↦ f.f i) (kernel.lift_ι g' (kernel.ι g ≫ p')
      (by simp [← sq']))
    simp only [HomologicalComplex.comp_f] at hp hp'
    rw [hp, hp']
    have hh : p.f i = X.d i ((ComplexShape.up ℤ).next i) ≫
        H.hom ((ComplexShape.up ℤ).next i) i +
      H.hom i ((ComplexShape.up ℤ).prev i) ≫ X'.d ((ComplexShape.up ℤ).prev i) i +
        p'.f i := H.comm i
    rw [hh]
    simp only [Preadditive.comp_add, ← Category.assoc, (kernel.ι g).comm]

private lemma boundedBelow_isKInjective
    {A : Type w} [Category.{w'} A] [Abelian A]
    (K : CochainComplex A ℤ) (hK : BoundedBelow K) (hinj : ∀ n, Injective (K.X n)) :
    K.IsKInjective := by
  obtain ⟨d, hd⟩ := hK
  let : K.IsStrictlyGE d := (K.isStrictlyGE_iff d).2 hd
  let := hinj
  exact CochainComplex.isKInjective_of_injective K d

private lemma derived_rep
    {A : Type w} [Category.{w'} A] [Abelian A] [HasDerivedCategory.{wQ} A]
    (I K : CochainComplex A ℤ) [K.IsKInjective]
    (a : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj K) :
    ∃ h : I ⟶ K, DerivedCategory.Q.map h = a := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨h, hh⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) K).surjective
      (e.hom.app I ≫ a ≫ e.inv.app K)
  obtain ⟨h, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective h
  refine ⟨h, ?_⟩
  have he := DerivedCategory.quotientCompQhIso_hom_naturality h
  rw [hh] at he
  simpa [e] using he.symm

private lemma derived_homotopy
    {A : Type w} [Category.{w'} A] [Abelian A] [HasDerivedCategory.{wQ} A]
    {I K : CochainComplex A ℤ} [K.IsKInjective]
    (f g : I ⟶ K) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (_root_.Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ K).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app K)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]

private def pairMap
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K) :
    supportDiagram Jc P I ⟶ supportDiagram Jd P' K :=
  kernelDiagramMap _ _
    (pairSectionMap Jc Jd u (chainAdjoint L _ adj h) t)
    (pairSectionMap Jc Jd u (chainAdjoint L _ adj h) s)
    (pairSectionMap_square Jc Jd u P P' t s square _)

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
private lemma pairMap_condition
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K) :
    supportPairMapCondition Jc Jd u L adj P P' t s h
      (pairMap Jc Jd u L adj P P' t s square h) :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
private lemma pairMap_eq
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
    (hφ : supportPairMapCondition Jc Jd u L adj P P' t s h φ) :
    φ = pairMap Jc Jd u L adj P P' t s square h := by
  obtain ⟨ψ, _, hu⟩ := pairMap_existsUnique Jc Jd u L adj P P' t s square h
  exact (hu φ hφ).trans (hu _ (pairMap_condition Jc Jd u L adj P P' t s square h)).symm

private def pairMapKernelHomotopy
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    {h h' : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K}
    (z : _root_.Homotopy h h') :
    _root_.Homotopy (pairMap Jc Jd u L adj P P' t s square h).τ₁
      (pairMap Jc Jd u L adj P P' t s square h').τ₁ :=
  kernelMapHomotopy _ _
    (pairSectionMap_square Jc Jd u P P' t s square _)
    (pairSectionMap_square Jc Jd u P P' t s square _)
    (pairSectionHomotopy Jc Jd u L adj z t)
    (pairSectionHomotopy Jc Jd u L adj z s)
    (fun i j ↦ (pairDegree_square Jc Jd u P P' t s square
      (adj.homEquiv _ _ (z.hom i j))).symm)

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
private lemma pairMap_cohomologyEqual
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    {h h' : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K}
    (z : _root_.Homotopy h h')
    (φ ψ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
    (hφ : supportPairMapCondition Jc Jd u L adj P P' t s h φ)
    (hψ : supportPairMapCondition Jc Jd u L adj P P' t s h' ψ) :
    supportCohomologyEqual φ ψ := by
  rw [pairMap_eq Jc Jd u L adj P P' t s square h φ hφ,
    pairMap_eq Jc Jd u L adj P P' t s square h' ψ hψ]
  intro n
  exact ⟨(pairMapKernelHomotopy Jc Jd u L adj P P' t s square z).homologyMap_eq n,
    (pairSectionHomotopy Jc Jd u L adj z t).homologyMap_eq n,
    (pairSectionHomotopy Jc Jd u L adj z s).homologyMap_eq n⟩

private def ordinaryMap
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ} (g : I ⟶ K) :
    supportDiagram J P I ⟶ supportDiagram J P K :=
  kernelDiagramMap _ _
    (((sectionFunctor J P.T).mapHomologicalComplex (.up ℤ)).map g)
    (((sectionFunctor J P.V).mapHomologicalComplex (.up ℤ)).map g)
    ((NatTrans.mapHomologicalComplex (sectionRestriction J P.m) (.up ℤ)).naturality g).symm

private lemma diagramMap_ext
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ}
    {S : ShortComplex (CochainComplex AddCommGrpCat.{w₀} ℤ)}
    (φ ψ : S ⟶ supportDiagram J P I) (h₂ : φ.τ₂ = ψ.τ₂) (h₃ : φ.τ₃ = ψ.τ₃) :
    φ = ψ := by
  let : Mono (supportDiagram J P I).f := inferInstanceAs (Mono (kernel.ι _))
  apply ShortComplex.hom_ext
  · apply (cancel_mono (supportDiagram J P I).f).1
    rw [φ.comm₁₂, ψ.comm₁₂, h₂]
  · exact h₂
  · exact h₃

private lemma ordinaryMap_comp
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K M : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ}
    (g : I ⟶ K) (h : K ⟶ M) :
    ordinaryMap J P (g ≫ h) = ordinaryMap J P g ≫ ordinaryMap J P h := by
  apply diagramMap_ext J P
  · exact ((sectionFunctor J P.T).mapHomologicalComplex (.up ℤ)).map_comp g h
  · exact ((sectionFunctor J P.V).mapHomologicalComplex (.up ℤ)).map_comp g h

private lemma ordinaryMap_id
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    (I : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ) :
    ordinaryMap J P (𝟙 I) = 𝟙 _ := by
  apply diagramMap_ext J P
  · exact ((sectionFunctor J P.T).mapHomologicalComplex (.up ℤ)).map_id I
  · exact ((sectionFunctor J P.V).mapHomologicalComplex (.up ℤ)).map_id I

private lemma ordinaryMap_cohomologyEqual
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ}
    {g g' : I ⟶ K} (z : _root_.Homotopy g g') :
    supportCohomologyEqual (ordinaryMap J P g) (ordinaryMap J P g') := by
  let H₂ := (sectionFunctor J P.T).mapHomotopy z
  let H₃ := (sectionFunctor J P.V).mapHomotopy z
  have compat : ∀ i j, H₂.hom i j ≫ (supportDiagram J P K).g.f j =
      (supportDiagram J P I).g.f i ≫ H₃.hom i j := by
    intro i j
    exact ((z.hom i j).hom.naturality P.m.op).symm
  let H₁ := kernelMapHomotopy _ _
    ((NatTrans.mapHomologicalComplex (sectionRestriction J P.m) (.up ℤ)).naturality g).symm
    ((NatTrans.mapHomologicalComplex (sectionRestriction J P.m) (.up ℤ)).naturality g').symm
    H₂ H₃ compat
  intro n
  exact ⟨H₁.homologyMap_eq n, H₂.homologyMap_eq n, H₃.homologyMap_eq n⟩

private lemma ordinaryMap_cohomologyIsIso
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ}
    (e : _root_.HomotopyEquiv I K) :
    supportCohomologyIsIso (ordinaryMap J P e.hom) := by
  have h₁ := ordinaryMap_cohomologyEqual J P e.homotopyHomInvId
  have h₂ := ordinaryMap_cohomologyEqual J P e.homotopyInvHomId
  rw [ordinaryMap_comp, ordinaryMap_id] at h₁ h₂
  intro n
  have hi {X Y : CochainComplex AddCommGrpCat.{w₀} ℤ}
      (f : X ⟶ Y) (g : Y ⟶ X)
      (hf : (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map (f ≫ g) =
        (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map (𝟙 X))
      (hg : (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map (g ≫ f) =
        (HomologicalComplex.homologyFunctor _ (.up ℤ) n).map (𝟙 Y)) :
      IsIso ((HomologicalComplex.homologyFunctor _ (.up ℤ) n).map f) := by
    refine ⟨⟨(HomologicalComplex.homologyFunctor _ (.up ℤ) n).map g, ?_, ?_⟩⟩
    · simpa only [Functor.map_comp, Functor.map_id] using hf
    · simpa only [Functor.map_comp, Functor.map_id] using hg
  exact ⟨hi _ _ (h₁ n).1 (h₂ n).1,
    hi _ _ (h₁ n).2.1 (h₂ n).2.1, hi _ _ (h₁ n).2.2 (h₂ n).2.2⟩

private lemma ordinaryMap_derivedIsIso
    (J : GrothendieckTopology C) (P : SupportPair (C := C))
    [HasSheafify J AddCommGrpCat.{w₀}]
    [HasDerivedCategory.{wQ} (Sheaf J AddCommGrpCat.{w₀})]
    {I K : CochainComplex (Sheaf J AddCommGrpCat.{w₀}) ℤ}
    (hI : BoundedBelow I) (hK : BoundedBelow K)
    (hinjI : ∀ n, Injective (I.X n)) (hinjK : ∀ n, Injective (K.X n))
    (g : I ⟶ K) (hg : IsIso (standardDerivedQ.map g)) :
    supportCohomologyIsIso (ordinaryMap J P g) := by
  have : I.IsKInjective := boundedBelow_isKInjective I hI hinjI
  have : K.IsKInjective := boundedBelow_isKInjective K hK hinjK
  have : _root_.QuasiIso g :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 hg
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).1 inferInstance
  rw [← he]
  exact ordinaryMap_cohomologyIsIso J P e

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}] in
set_option backward.isDefEq.respectTransparency false in
private lemma pairMap_composite_condition
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd) [L.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    {I I' : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K K' : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    (g : I' ⟶ I) (g' : K ⟶ K')
    (h : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ K)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
    (hφ : supportPairMapCondition Jc Jd u L adj P P' t s h φ) :
    supportPairMapCondition Jc Jd u L adj P P' t s
      ((L.mapHomologicalComplex (.up ℤ)).map g ≫ h ≫ g')
      (ordinaryMap Jc P g ≫ φ ≫ ordinaryMap Jd P' g') := by
  have eqn (X : C) (Y : D) (f : Y ⟶ u.obj X) (n : ℤ) :
      (sectionFunctor Jc X).map (g.f n) ≫
        ((sectionFunctor Jc X).map (degreewiseAdjoint L _ adj h n) ≫
          (sectionRestriction Jd f).app (K.X n)) ≫
            (sectionFunctor Jd Y).map (g'.f n) =
      (sectionFunctor Jc X).map
          (degreewiseAdjoint L _ adj
            ((L.mapHomologicalComplex (.up ℤ)).map g ≫ h ≫ g') n) ≫
          (sectionRestriction Jd f).app (K'.X n) := by
    simp only [degreewiseAdjoint, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, adj.homEquiv_naturality_left,
      adj.homEquiv_naturality_right, Functor.map_comp, Category.assoc]
    change _ ≫ _ ≫ (K.X n).obj.map f.op ≫ (g'.f n).hom.app (Opposite.op Y) =
      _ ≫ _ ≫ (g'.f n).hom.app (Opposite.op (u.obj X)) ≫ (K'.X n).obj.map f.op
    rw [(g'.f n).hom.naturality f.op]
  constructor
  · intro n
    simpa only [ShortComplex.comp_τ₂, HomologicalComplex.comp_f,
      ordinaryMap, kernelDiagramMap, Functor.mapHomologicalComplex_map_f, hφ.1 n] using
      eqn P.T P'.T t n
  · intro n
    simpa only [ShortComplex.comp_τ₃, HomologicalComplex.comp_f,
      ordinaryMap, kernelDiagramMap, Functor.mapHomologicalComplex_map_f, hφ.2 n] using
      eqn P.V P'.V s n

set_option linter.unusedVariables false in
/--
Source: Milne, *Lectures on Étale Cohomology*, Section 9, Theorem 9.4,
pp. 65--67, pair functoriality; Stacks Project, Derived Categories, Tag 070I.
(blueprint: lem-pur-support-pair-chain-coherence)

Step 1. Take the degreewise adjoint of `h`. Naturality in both sheaf variables
makes it a chain map. Since the right adjoint is the actual precomposition
functor, its evaluations commute with restriction; use `square` to obtain
commuting T- and V-component chain maps.
Step 2. The universal property of the kernel supplies the unique first
component, giving the unique diagram map with those section components.
Step 3. Adjoin each component of the degree -1 homotopy `z`, evaluate, and
restrict along `t,s`. Naturality makes these degree -1 maps compatible with
restriction, so they restrict to the kernel. The homotopy equation passes
through the adjunction, giving the three cochain homotopies below, compatible
with inclusion and restriction. They induce equal maps on all cohomology groups.
Step 4. Bounded-below injective complexes are K-injective by
`CochainComplex.isKInjective_of_injective`. The K-injective comparison
`CochainComplex.IsKInjective.Qh_map_bijective` supplies representatives of every
derived morphism and homotopies between any two representatives of the same one.
Step 5. The adjoint of the composite `L.map g ≫ h ≫ g'`
is `R(g')` composed with the adjoint of `h` and with `g`. Thus the diagram map
of `L.map g ≫ h ≫ g'` is the composite of the ordinary diagram maps and the
map of `h`. A derived isomorphism between bounded-below injective complexes
has a chain representative and a homotopy inverse by the same K-injective
comparison. Evaluation and the kernel construction preserve these homotopies.
Consequently the ordinary diagram maps of `g,g'` induce the canonical
cohomology identifications. Step 3 makes them independent of the representatives
of the given derived identifications. The last equality says exactly that
transport by those identifications preserves the maps induced by `a`.
-/
theorem supportPairChainCoherence
    (u : C ⥤ D) [u.IsContinuous Jc Jd]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (adj : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasDerivedCategory.{wQc} (Sheaf Jc AddCommGrpCat.{w₀})]
    [HasDerivedCategory.{wQd} (Sheaf Jd AddCommGrpCat.{w₀})]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (square : s ≫ u.map P.m = P'.m ≫ t) :
    ∀ (I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
      (K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ),
      (∀ h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K,
        (∃! φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K,
          supportPairMapCondition Jc Jd u L adj P P' t s h φ) ∧
        (∀ (h' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
            (z : _root_.Homotopy h h'),
          ∃ (φ φ' : supportDiagram Jc P I ⟶ supportDiagram Jd P' K),
            supportPairMapCondition Jc Jd u L adj P P' t s h φ ∧
            supportPairMapCondition Jc Jd u L adj P P' t s h' φ' ∧
            ∃ (H₁ : _root_.Homotopy φ.τ₁ φ'.τ₁)
              (H₂ : _root_.Homotopy φ.τ₂ φ'.τ₂)
              (H₃ : _root_.Homotopy φ.τ₃ φ'.τ₃),
              ∀ i j : ℤ,
                H₁.hom i j ≫ (supportDiagram Jd P' K).f.f j =
                  (supportDiagram Jc P I).f.f i ≫ H₂.hom i j ∧
                H₂.hom i j ≫ (supportDiagram Jd P' K).g.f j =
                  (supportDiagram Jc P I).g.f i ≫ H₃.hom i j ∧
                H₂.hom i j = (sectionFunctor Jc P.T).map
                  ((adj.homEquiv (I.X i) (K.X j)) (z.hom i j)) ≫
                    (sectionRestriction Jd t).app (K.X j) ∧
                H₃.hom i j = (sectionFunctor Jc P.V).map
                  ((adj.homEquiv (I.X i) (K.X j)) (z.hom i j)) ≫
                    (sectionRestriction Jd s).app (K.X j))) ∧
      (∀ (hI : BoundedBelow I) (hK : BoundedBelow K)
          (hinjI : ∀ n : ℤ, Injective (I.X n))
          (hinjK : ∀ n : ℤ, Injective (K.X n)),
        (∀ a : (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj
              ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).obj K,
          ∃ h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K,
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h = a) ∧
        (∀ (h₁ h₂ : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K),
          (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h₁ =
              (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h₂ →
            Nonempty (_root_.Homotopy h₁ h₂) ∧
            ∀ (φ ψ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K),
              supportPairMapCondition Jc Jd u L adj P P' t s h₁ φ →
              supportPairMapCondition Jc Jd u L adj P P' t s h₂ ψ →
              supportCohomologyEqual φ ψ) ∧
        (∀ (I' : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ)
            (K' : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ)
            (hI' : BoundedBelow I') (hK' : BoundedBelow K')
            (hinjI' : ∀ n : ℤ, Injective (I'.X n))
            (hinjK' : ∀ n : ℤ, Injective (K'.X n))
            (g : I' ⟶ I) (g' : K ⟶ K'),
          IsIso ((standardDerivedQ (A := Sheaf Jc AddCommGrpCat.{w₀})).map g) →
          IsIso ((standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map g') →
          ∀ (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
            (h' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I' ⟶ K'),
            (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h' =
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map
                  ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map h ≫
                (standardDerivedQ (A := Sheaf Jd AddCommGrpCat.{w₀})).map g' →
            ∀ (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
              (ψ : supportDiagram Jc P I' ⟶ supportDiagram Jd P' K'),
              supportPairMapCondition Jc Jd u L adj P P' t s h φ →
              supportPairMapCondition Jc Jd u L adj P P' t s h' ψ →
              ∃ (α : supportDiagram Jc P I' ⟶ supportDiagram Jc P I)
                (β : supportDiagram Jd P' K ⟶ supportDiagram Jd P' K'),
                supportOrdinaryMapCondition Jc P g α ∧
                supportOrdinaryMapCondition Jd P' g' β ∧
                supportCohomologyIsIso α ∧ supportCohomologyIsIso β ∧
                supportCohomologyEqual (α ≫ φ ≫ β) ψ)) := by
  intro I K
  constructor
  · intro h
    refine ⟨pairMap_existsUnique Jc Jd u L adj P P' t s square h, ?_⟩
    intro h' z
    refine ⟨pairMap Jc Jd u L adj P P' t s square h,
      pairMap Jc Jd u L adj P P' t s square h',
      pairMap_condition Jc Jd u L adj P P' t s square h,
      pairMap_condition Jc Jd u L adj P P' t s square h',
      pairMapKernelHomotopy Jc Jd u L adj P P' t s square z,
      pairSectionHomotopy Jc Jd u L adj z t,
      pairSectionHomotopy Jc Jd u L adj z s, ?_⟩
    intro i j
    refine ⟨?_, ?_, rfl, rfl⟩
    · exact kernelDegreeLift_ι _ _ _ _ _
    · exact (pairDegree_square Jc Jd u P P' t s square
        (adj.homEquiv _ _ (z.hom i j))).symm
  · intro hI hK hinjI hinjK
    have : K.IsKInjective := boundedBelow_isKInjective K hK hinjK
    refine ⟨fun a ↦ derived_rep (A := Sheaf Jd AddCommGrpCat.{w₀}) _ _ a, ?_, ?_⟩
    · intro h₁ h₂ he
      obtain ⟨z⟩ := derived_homotopy h₁ h₂ he
      exact ⟨⟨z⟩, fun φ ψ hφ hψ ↦
        pairMap_cohomologyEqual Jc Jd u L adj P P' t s square z φ ψ hφ hψ⟩
    · intro I' K' hI' hK' hinjI' hinjK' g g' hg hg' h h' he φ ψ hφ hψ
      have : K'.IsKInjective := boundedBelow_isKInjective K' hK' hinjK'
      have he' : standardDerivedQ.map
          ((L.mapHomologicalComplex (.up ℤ)).map g ≫ h ≫ g') =
          standardDerivedQ.map h' := by
        simpa only [Functor.map_comp, Category.assoc] using he.symm
      obtain ⟨z⟩ := derived_homotopy _ _ he'
      refine ⟨ordinaryMap Jc P g, ordinaryMap Jd P' g', ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
        ordinaryMap_derivedIsIso Jc P hI' hI hinjI' hinjI g hg,
        ordinaryMap_derivedIsIso Jd P' hK hK' hinjK hinjK' g' hg', ?_⟩
      exact pairMap_cohomologyEqual Jc Jd u L adj P P' t s square z _ ψ
        (pairMap_composite_condition Jc Jd u L adj P P' t s g g' h φ hφ) hψ

end CategoryTheory
