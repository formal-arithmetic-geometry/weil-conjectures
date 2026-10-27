/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.ColimitSites
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Presentations of inverse limits of qcqs etale topoi

Source: Stacks Project, Sites, Tags 09YL and 0A35; ILO XX 4.4, printed p.373
(blueprint: def-per-qcqs-etale-limit-presentation).

The cocycle equations use direct-image 2-morphisms. Invertibility and the composition
cocycle force the unit equation. All comparisons use scheme pullback pasting, including
in the definition of reindexing comparisons. No limit scheme is part of these data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u e v e' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.QcqsEtaleLimit

/-- The qcqs objects of the existing small etale site, as an object property.
Source: Stacks, Tag 03Q4; ILO XX 4.4 (blueprint: def-per-qcqs-etale-limit-presentation). -/
def qcqs (Y : Scheme.{u}) : ObjectProperty Y.Etale :=
  fun U ↦ CompactSpace U.left ∧ QuasiSeparatedSpace U.left

/-- A pseudocone of geometric morphisms into the etale topoi of `D`.
The displayed equation is the composition cocycle using canonical pullback pasting;
invertibility makes its identity case the unit axiom.
Source: ILO XX 4.4; Sites, Tag 00XA (blueprint: def-per-qcqs-etale-limit-presentation). -/
structure ToposCone {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u})
    (E : Type e) [Category.{v} E] where
  projection (i : I) : GeometricMorphism E
    (Sheaf (D.obj i).smallEtaleTopology (Type (u + 1)))
  comparison {i j : I} (a : i ⟶ j) :
    (projection i).direct ⋙ Etale.lowerStar (Type (u + 1)) (D.map a) ≅
      (projection j).direct
  cocycle {i j k : I} (a : i ⟶ j) (b : j ⟶ k) (M : E) :
    (Etale.lowerStar (Type (u + 1)) (D.map b)).map ((comparison a).hom.app M) ≫
        (comparison b).hom.app M =
      (Etale.lowerStarComp (Type (u + 1)) (D.map a) (D.map b)
        (D.map (a ≫ b)) (D.map_comp a b)).hom.app ((projection i).direct.obj M) ≫
          (comparison (a ≫ b)).hom.app M

/-- A factorization of a pseudocone, including compatibility with every comparison.
Source: ILO XX 4.4, projective-limit topos (blueprint: def-per-qcqs-etale-limit-presentation).
-/
structure Factorization {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}}
    {L : Type e} [Category.{v} L] (p : ToposCone D L)
    {E : Type e'} [Category.{v'} E] (q : ToposCone D E) where
  morphism : GeometricMorphism E L
  iso (i : I) : morphism.direct ⋙ (p.projection i).direct ≅ (q.projection i).direct
  compatibility {i j : I} (a : i ⟶ j) (M : E) :
    (Etale.lowerStar (Type (u + 1)) (D.map a)).map ((iso i).hom.app M) ≫
        (q.comparison a).hom.app M =
      (p.comparison a).hom.app (morphism.direct.obj M) ≫ (iso j).hom.app M

/-- The 2-limit universal property: essential surjectivity on cones and unique lifting
of all compatible 2-morphisms, including noninvertible ones. The functor on 2-morphisms
is composition with the projections, so identities and composition are the usual ones.
Source: ILO XX 4.4 (blueprint: def-per-qcqs-etale-limit-presentation). -/
def IsToposLimit {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}}
    {L : Type e} [Category.{v} L] (p : ToposCone D L) : Prop :=
  (∀ (E : Type (u + 2)) [Category.{u + 1} E], IsGrothendieckTopos.{u + 1} E →
    ∀ q : ToposCone D E, Nonempty (Factorization p q)) ∧
  (∀ (E : Type (u + 2)) [Category.{u + 1} E], IsGrothendieckTopos.{u + 1} E →
    ∀ (f g : GeometricMorphism E L)
      (τ : ∀ i : I, f.direct ⋙ (p.projection i).direct ⟶
        g.direct ⋙ (p.projection i).direct),
      (∀ (i j : I) (a : i ⟶ j) (M : E),
        (Etale.lowerStar (Type (u + 1)) (D.map a)).map ((τ i).app M) ≫
            (p.comparison a).hom.app (g.direct.obj M) =
          (p.comparison a).hom.app (f.direct.obj M) ≫ (τ j).app M) →
      ∃! t : f.direct ⟶ g.direct,
        ∀ i : I, Functor.whiskerRight t (p.projection i).direct = τ i)

/-- A geometric-point cone, using separably closed fields as in ILO XX 4.4.
The identifications are natural isomorphisms with the existing pointed-etale stalks.
Source: ILO XX 4.4; Stacks, Tag 04FM (blueprint: def-per-qcqs-etale-limit-presentation). -/
structure GeometricPointCone {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) where
  cone : ToposCone D (Type (u + 1))
  field (i : I) : Type u
  fieldStructure (i : I) : Field (field i)
  separablyClosed (i : I) : @IsSepClosed (field i) (fieldStructure i)
  point (i : I) : Spec (.of (field i)) ⟶ D.obj i
  stalk (i : I) :
    (cone.projection i).inverse ≅
      (@Scheme.pointSmallEtale _ (field i) (fieldStructure i) (separablyClosed i)
        (point i)).sheafFiber (A := Type (u + 1))

/-- A strict small-site presentation, with its evaluation into actual qcqs etale objects,
canonical pullback comparisons, stage coverings, colimit coverings, and normalized projections.
The normalization says directly that projection direct image is restriction of sections.
Source: Stacks, Tags 09YL, 0A35; ILO XX 4.4
(blueprint: def-per-qcqs-etale-limit-presentation). -/
structure Presentation {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) where
  stages : Iᵒᵖ ⥤ Cat.{u + 1, u + 1}
  evaluation (i : I) : stages.obj (op i) ≌ (qcqs (D.obj i)).FullSubcategory
  pullbackComparison {i j : I} (a : i ⟶ j) :
    (evaluation j).functor ⋙ (qcqs (D.obj j)).ι ⋙
        MorphismProperty.Over.pullback @Etale ⊤ (D.map a) ≅
      (stages.map a.op).toFunctor ⋙ (evaluation i).functor ⋙ (qcqs (D.obj i)).ι
  pullbackCocycle {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
      (U : stages.obj (op k)) :
    HEq ((pullbackComparison (a ≫ b)).app U)
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)).app
          (((evaluation k).functor ⋙ (qcqs (D.obj k)).ι).obj U) ≪≫
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map a)).mapIso
          ((pullbackComparison b).app U) ≪≫
        (pullbackComparison a).app ((stages.map b.op).toFunctor.obj U))
  stageCover (i : I) : Precoverage (stages.obj (op i))
  stageCover_iff (i : I) (U : stages.obj (op i)) (R : Presieve U) :
    R ∈ stageCover i U ↔ Finite R.uncurry ∧
      Sieve.generate (R.map ((evaluation i).functor ⋙ (qcqs (D.obj i)).ι)) ∈
        (D.obj i).smallEtaleTopology
          (((evaluation i).functor ⋙ (qcqs (D.obj i)).ι).obj U)
  colimit : Cocone stages
  objectsColimit : IsColimit (Cat.objects.mapCocone colimit)
  arrowsColimit : IsColimit (Cat.arrows.mapCocone colimit)
  cover : Precoverage colimit.pt
  cover_iff (U : colimit.pt) (R : Presieve U) :
    R ∈ cover U ↔ ∃ (i : I) (V : stages.obj (op i)) (S : Presieve V)
      (h : (colimit.ι.app (op i)).toFunctor.obj V = U),
      S ∈ stageCover i V ∧ h ▸ S.map (colimit.ι.app (op i)).toFunctor = R
  coverIsos : cover.HasIsos
  coverComposition : cover.IsStableUnderFiniteComposition
  coverBaseChange : cover.IsStableUnderFiniteBaseChange
  coverPullbacks : cover.HasPullbacks
  finiteLimits : HasFiniteLimits colimit.pt
  terminal (i : I) (U : stages.obj (op i)) (h : IsTerminal U) :
    IsTerminal ((colimit.ι.app (op i)).toFunctor.obj U)
  projections : ToposCone D (Sheaf cover.toGrothendieck (Type (u + 1)))
  restriction (i : I) :
    (projections.projection i).direct ⋙
        sheafToPresheaf (D.obj i).smallEtaleTopology (Type (u + 1)) ⋙
          (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
            (((evaluation i).functor ⋙ (qcqs (D.obj i)).ι).op) ≅
      sheafToPresheaf cover.toGrothendieck (Type (u + 1)) ⋙
        (Functor.whiskeringLeft _ _ (Type (u + 1))).obj
          (colimit.ι.app (op i)).toFunctor.op
  restriction_compatibility {i j : I} (a : i ⟶ j)
      (M : Sheaf cover.toGrothendieck (Type (u + 1))) (U : stages.obj (op j)) :
    Arrow.mk
      (((projections.comparison a).hom.app M).hom.app
          (op (((evaluation j).functor ⋙ (qcqs (D.obj j)).ι).obj U)) ≫
        ((restriction j).hom.app M).app (op U)) =
      Arrow.mk
        (((projections.projection i).direct.obj M).obj.map
            ((pullbackComparison a).inv.app U).op ≫
          ((restriction i).hom.app M).app (op ((stages.map a.op).toFunctor.obj U)))

/-- The canonical comparison after reindexing and an isomorphism of scheme diagrams.
`equivalence.functor` is its direct-image functor. The equation includes the scheme
isomorphism, its naturality square, both pullback-pasting comparisons, and the cone cocycles.
Source: ILO XX 4.4; Stacks, Tags 09YL, 0A35
(blueprint: def-per-qcqs-etale-limit-presentation). -/
structure Comparison {I J : Type u} [SmallCategory I] [SmallCategory J]
    {D : I ⥤ Scheme.{u}} {D' : J ⥤ Scheme.{u}}
    {L : Type e} [Category.{v} L] (p : ToposCone D L)
    {L' : Type e'} [Category.{v'} L'] (p' : ToposCone D' L')
    (r : J ⥤ I) (ε : D' ≅ r ⋙ D) where
  equivalence : L' ≌ L
  iso (j : J) :
    equivalence.functor ⋙ (p.projection (r.obj j)).direct ≅
      (p'.projection j).direct ⋙ Etale.lowerStar (Type (u + 1)) (ε.hom.app j)
  compatibility {j k : J} (a : j ⟶ k) (M : L') :
    (Etale.lowerStar (Type (u + 1)) (D.map (r.map a))).map ((iso j).hom.app M) ≫
        (Etale.lowerStarComp (Type (u + 1)) (ε.hom.app j) (D.map (r.map a))).hom.app
          ((p'.projection j).direct.obj M) ≫
        (Etale.lowerStarComp (Type (u + 1)) (D'.map a) (ε.hom.app k)
          (ε.hom.app j ≫ D.map (r.map a)) (ε.hom.naturality a).symm).inv.app
            ((p'.projection j).direct.obj M) ≫
        (Etale.lowerStar (Type (u + 1)) (ε.hom.app k)).map
          ((p'.comparison a).hom.app M) =
      (p.comparison (r.map a)).hom.app (equivalence.functor.obj M) ≫ (iso k).hom.app M

/-- Uniqueness up to a unique invertible 2-morphism of a compatible comparison.
Source: ILO XX 4.4, canonical equivalences of projective limits
(blueprint: def-per-qcqs-etale-limit-presentation). -/
def Comparison.IsCanonical {I J : Type u} [SmallCategory I] [SmallCategory J]
    {D : I ⥤ Scheme.{u}} {D' : J ⥤ Scheme.{u}}
    {L : Type e} [Category.{v} L] {p : ToposCone D L}
    {L' : Type e'} [Category.{v'} L'] {p' : ToposCone D' L'}
    {r : J ⥤ I} {ε : D' ≅ r ⋙ D} (c : Comparison p p' r ε) : Prop :=
  ∀ c' : Comparison p p' r ε,
    ∃! t : c.equivalence.functor ⟶ c'.equivalence.functor,
      IsIso t ∧ ∀ j : J,
        Functor.whiskerRight t (p.projection (r.obj j)).direct ≫ (c'.iso j).hom =
          (c.iso j).hom

end AlgebraicGeometry.QcqsEtaleLimit
