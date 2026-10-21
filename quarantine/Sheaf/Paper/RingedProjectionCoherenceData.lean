/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Tensor and composition coherence of ringed-topos projection maps

Source: Stacks Project, Cohomology on Sites, Tag 0B56,
`equation-projection-formula-map`; Categories, Tag 0DV0, `lemma-compose-counits`
(blueprint: lem-sfb-ringed-projection-tensor-composition).

We use the recorded ringed-site tensor models, their canonical tensor comparisons,
and `RingedTensorEdge.projection`. Associators and symmetries below are specified
on flat K-flat representatives. A section comparison is specified by the given
ringed isomorphism on underlying sheaves, ordinary modules, and representatives.
(blueprint: def-sfb-ringed-projection-coherence-data).

The composite adjunction is the normal form of the canonical pullback/direct-image
comparisons: its tensor map is the composite of the two canonical tensor maps.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.ProjectionCoherence

/-- The recorded direct-sum total tensor, abbreviated only to keep representative
normalizations readable. Source: Stacks 06YN and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
abbrev total (A : RingedTensorCorner.{u, w})
    (P Q : CochainComplex A.mateModules ℤ) :=
  CochainComplex.mapBifunctor P Q A.mateTensor

/-- The ordinary associator of the signed total tensor: it reassociates pure tensors
without a sign. Source: Stacks 06YN, 07A4 and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def totalAssociator (A : RingedTensorCorner.{u, w})
    (P Q T : CochainComplex A.mateModules ℤ) :
    total A (total A P Q) T ≅ total A P (total A Q T) := by
  letI := monoidalCategory A.ring
  letI := symmetricCategory A.ring
  letI := ringedTensorPreadditive A.ring
  letI : MonoidalClosed A.mateModules := Classical.choice (tensorClosed A.ring).2.1
  letI : HasColimitsOfSize.{0, 0} A.mateModules := hasColimitsOfSizeShrink.{0, 0, u, u} _
  exact HomologicalComplex.associator P Q T

/-- The Koszul symmetry of the same total tensor. On a summand of bidegree `(p,q)`
it interchanges factors with sign `(-1)^(p*q)`. Source: Stacks 06YN and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def totalSymmetry (A : RingedTensorCorner.{u, w})
    (P Q : CochainComplex A.mateModules ℤ) : total A P Q ≅ total A Q P := by
  letI := monoidalCategory A.ring
  letI := symmetricCategory A.ring
  letI := ringedTensorPreadditive A.ring
  letI : MonoidalClosed A.mateModules := Classical.choice (tensorClosed A.ring).2.1
  letI : HasColimitsOfSize.{0, 0} A.mateModules := hasColimitsOfSizeShrink.{0, 0, u, u} _
  exact CochainComplex.Monoidal.braiding P Q

/-- The canonical associator and symmetry of a derived tensor model. They are natural
in every variable, and the equations specify their data on every flat K-flat
representative, rather than assuming any projection coherence. Since every derived
object is isomorphic to a flat K-flat representative (Stacks 06YS), naturality and
these equations determine their components on all derived objects.
Source: Stacks 06YS, 06YU and 07A4; the canonical constraints used in 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure TensorConstraints (A : RingedTensorCorner.{u, w}) (a : RingedTensorModel A) where
  associator : ∀ E F G : A.mateDerived,
    A.tensor.obj (A.tensor.obj (E, F), G) ≅ A.tensor.obj (E, A.tensor.obj (F, G))
  symmetry : ∀ E F : A.mateDerived, A.tensor.obj (E, F) ≅ A.tensor.obj (F, E)
  associator_naturality : ∀ {E E' F F' G G' : A.mateDerived}
    (x : E ⟶ E') (y : F ⟶ F') (z : G ⟶ G'),
    A.tensor.map (Prod.mkHom (A.tensor.map (Prod.mkHom x y)) z) ≫
        (associator E' F' G').hom =
      (associator E F G).hom ≫ A.tensor.map (Prod.mkHom x (A.tensor.map (Prod.mkHom y z)))
  symmetry_naturality : ∀ {E E' F F' : A.mateDerived} (x : E ⟶ E') (y : F ⟶ F'),
    A.tensor.map (Prod.mkHom x y) ≫ (symmetry E' F').hom =
      (symmetry E F).hom ≫ A.tensor.map (Prod.mkHom y x)
  associator_representative : ∀ (P Q T : CochainComplex A.mateModules ℤ)
    (hp : A.mateFlat P) (hq : A.mateFlat Q) (ht : A.mateFlat T),
    ∃ (hpq : A.mateFlat (total A P Q)) (hqt : A.mateFlat (total A Q T)),
      a.representative.hom.app (⟨total A P Q, hpq⟩, ⟨T, ht⟩) ≫
        A.tensor.map (Prod.mkHom (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))
          (𝟙 (DerivedCategory.Q.obj T))) ≫
        (associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj T)).hom =
      DerivedCategory.Q.map (totalAssociator A P Q T).hom ≫
        a.representative.hom.app (⟨P, hp⟩, ⟨total A Q T, hqt⟩) ≫
        A.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
          (a.representative.hom.app (⟨Q, hq⟩, ⟨T, ht⟩)))
  symmetry_representative : ∀ (P Q : CochainComplex A.mateModules ℤ)
    (hp : A.mateFlat P) (hq : A.mateFlat Q),
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
        (symmetry (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (totalSymmetry A P Q).hom ≫
        a.representative.hom.app (⟨Q, hq⟩, ⟨P, hp⟩)

/-- The projection mate for the composite in the canonical comparison normal form.
This is defined by transposing the composite tensor comparison followed by the
composite counit; it is not defined as the two projection maps whose equality is asserted.
Source: Stacks 0B56 and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def compositeProjection {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z)
    (E : X.mateDerived) (Q : Z.mateDerived) :
    Z.tensor.obj (g.right.obj (f.right.obj E), Q) ⟶
      g.right.obj (f.right.obj (X.tensor.obj (E, f.left.obj (g.left.obj Q)))) :=
  (g.derivedAdjunction.comp f.derivedAdjunction).homEquiv _ _
    (f.left.map ((g.tensorComparison c b).hom.app (g.right.obj (f.right.obj E), Q)) ≫
      (f.tensorComparison b a).hom.app
        (g.left.obj (g.right.obj (f.right.obj E)), g.left.obj Q) ≫
      X.tensor.map (Prod.mkHom
        ((g.derivedAdjunction.comp f.derivedAdjunction).counit.app E)
        (𝟙 (f.left.obj (g.left.obj Q)))))

/-- Ordinary comparisons presenting a chosen ringed-topos composite `h = g f`.
The insertion equation fixes the module comparison from the underlying geometric
comparison and the structural ring maps. It is not a tensor or projection equation.
Source: Stacks 0D6D, 0D6E and 0FPI
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Composition {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X) where
  sets : h.inverse ≅ g.inverse ⋙ f.inverse
  modules : h.pullback ≅ g.pullback ⋙ f.pullback
  insertion : ∀ M : Z.mateModules,
    h.insertion M ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose Z.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj Z.ring) ⋙
          sheafCompose Z.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
        f.inverse.map (g.insertion M) ≫ f.insertion (g.pullback.obj M)

/-- The defining K-flat normalization of the canonical derived composition comparison.
Source: Stacks 0D6D and 0FPI
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Composition.Normalized {X Y Z : RingedTensorCorner.{u, w}}
    {f : RingedTensorEdge Y X} {g : RingedTensorEdge Z Y} {h : RingedTensorEdge Z X}
    (s : Composition f g h) (l : h.left ≅ g.left ⋙ f.left) : Prop :=
  ∀ (P : CochainComplex Z.mateModules ℤ), Z.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) ≫
        f.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison f.pullback f.left f.epsilon
          ((g.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      derivedPullbackComplexComparison h.pullback h.left h.epsilon P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

/-- The adjunction-compatible direct-image composition comparison. Its conjugate
is the specified pullback composition comparison, so the composite counit is fixed.
Source: Stacks 0D6E and 0FPI; Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def compositionRight {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X)
    (l : h.left ≅ g.left ⋙ f.left) : h.right ≅ f.right ⋙ g.right :=
  conjugateIsoEquiv h.derivedAdjunction (g.derivedAdjunction.comp f.derivedAdjunction) l.symm

/-- An ordinary ringed-topos comparison with the identity morphism. The insertion
condition includes compatibility with the structural ring map.
Source: Stacks 0D6D, 0FPI and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Identity {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X) where
  sets : h.inverse ≅ 𝟭 (Sheaf X.topology (Type u))
  modules : h.pullback ≅ 𝟭 X.mateModules
  insertion : ∀ M : X.mateModules,
    h.insertion M ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M)

/-- The identity pullback comparison, specified on all flat K-flat representatives.
Source: Stacks 0D6D, 0FPI and 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Identity.Normalized {X : RingedTensorCorner.{u, w}} {h : RingedTensorEdge X X}
    (s : Identity h) (l : h.left ≅ 𝟭 X.mateDerived) : Prop :=
  ∀ (P : CochainComplex X.mateModules ℤ), X.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) =
      derivedPullbackComplexComparison h.pullback h.left h.epsilon P ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

/-- The direct-image identity comparison adjunction-conjugate to its pullback comparison.
Source: Stacks 0FPI and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def identityRight {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X)
    (l : h.left ≅ 𝟭 X.mateDerived) : h.right ≅ 𝟭 X.mateDerived :=
  conjugateIsoEquiv h.derivedAdjunction Adjunction.id l.symm

/-- The identity projection after the canonical identity-functor comparisons.
Its transpose is the identity tensor comparison followed by the identity counit.
Source: Stacks 0B56 and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def identityProjection (X : RingedTensorCorner.{u, w}) (E Q : X.mateDerived) :
    X.tensor.obj (E, Q) ⟶ X.tensor.obj (E, Q) :=
  (Adjunction.id (C := X.mateDerived)).homEquiv _ _ (𝟙 (X.tensor.obj (E, Q)))

/-- A specified ringed isomorphism `p i ≅ id`, including its ordinary module map.
The insertion equation is the compatibility with the structural ring maps, written
on generalized module elements. It assumes no derived tensor or projection equation.
Source: Stacks 0D6D, 0FPI and the section specialization of 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
structure Section {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W) where
  sets : p.inverse ⋙ i.inverse ≅ 𝟭 (Sheaf X.topology (Type u))
  modules : p.pullback ⋙ i.pullback ≅ 𝟭 X.mateModules
  insertion : ∀ M : X.mateModules,
    i.inverse.map (p.insertion M) ≫ i.insertion (p.pullback.obj M) ≫
        (toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
          RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).map
            (modules.hom.app M) =
      sets.hom.app ((toSheaf ((sheafCompose X.topology (forget₂ CommRingCat.{u}
        RingCat.{u})).obj X.ring) ⋙
          sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat.{u})).obj M)

/-- The normalization defining the canonical derived pullback comparison for a section.
Source: Stacks 0D6D and 0FPI; section specialization of 0B56
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def Section.Normalized {X W : RingedTensorCorner.{u, w}}
    {i : RingedTensorEdge W X} {p : RingedTensorEdge X W} (s : Section i p)
    (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived) : Prop :=
  ∀ (P : CochainComplex X.mateModules ℤ), X.mateFlat P →
    l.hom.app (DerivedCategory.Q.obj P) =
      i.left.map (derivedPullbackComplexComparison p.pullback p.left p.epsilon P) ≫
        derivedPullbackComplexComparison i.pullback i.left i.epsilon
          ((p.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)).hom.app P)

/-- The direct-image comparison corresponding to the specified pullback comparison.
Conjugation fixes it through the adjunctions, including their counits.
Source: Stacks 0FPI and Categories 0DV0
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def sectionRight {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
    (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived) :
    i.right ⋙ p.right ≅ 𝟭 X.mateDerived :=
  conjugateIsoEquiv (p.derivedAdjunction.comp i.derivedAdjunction) Adjunction.id l.symm

/-- The left-ordered projection is the existing projection mate conjugated by the
canonical symmetries. Neither projection map is inverted.
Source: Stacks 0B56, factor order in the section specialization
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def leftProjection {X Y : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (a : RingedTensorModel X) (b : RingedTensorModel Y)
    (tx : TensorConstraints X a) (ty : TensorConstraints Y b)
    (M : Y.mateDerived) (V : X.mateDerived) :
    Y.tensor.obj (M, f.right.obj V) ⟶ f.right.obj (X.tensor.obj (f.left.obj M, V)) :=
  (ty.symmetry M (f.right.obj V)).hom ≫ f.projection b a V M ≫
    f.right.map (tx.symmetry V (f.left.obj M)).hom

/-- The displayed section composite, with every symmetry and comparison inserted.
Source: Stacks 0B56, the canonical section specialization
(blueprint: lem-sfb-ringed-projection-tensor-composition). -/
def sectionComposite {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
    (a : RingedTensorModel X) (b : RingedTensorModel W)
    (tx : TensorConstraints X a) (tw : TensorConstraints W b)
    (l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived) (M V : X.mateDerived) :
    X.tensor.obj (M, V) ⟶ X.tensor.obj (M, V) :=
  X.tensor.map (Prod.mkHom (𝟙 M) ((sectionRight i p l).inv.app V)) ≫
    leftProjection p b a tw tx M (i.right.obj V) ≫
    p.right.map (leftProjection i a b tx tw (p.left.obj M) V) ≫
    (sectionRight i p l).hom.app (X.tensor.obj (i.left.obj (p.left.obj M), V)) ≫
    X.tensor.map (Prod.mkHom (l.hom.app M) (𝟙 V))

end SheafOfModules.ProjectionCoherence
