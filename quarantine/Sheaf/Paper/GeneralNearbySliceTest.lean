/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# General specialization slices test the ordinary nearby comparison

Source: Orgogozo, Modifications et cycles proches sur une base générale,
Lemma 3.1.1, printed p. 6, first proof paragraph and displayed sliced comparison;
ILO, Exposé XI §§1.8--1.12, 4.1--4.4
(blueprint: lem-trf-general-nearby-slice-test).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- A geometric specialization, with the entire generic strict localization.
Source: Orgogozo, §1 and Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
structure SliceSpecialization (S : Scheme.{u}) where
  A : Type u
  B : Type u
  [fieldA : Field A]
  [closedA : IsAlgClosed A]
  [fieldB : Field B]
  [closedB : IsAlgClosed B]
  a : Spec (.of A) ⟶ S
  b : Spec (.of B) ⟶ S
  c : Scheme.strictHenselizationScheme b ⟶ Scheme.strictHenselizationScheme a
  over : c ≫ Scheme.strictHenselizationStructuralMap a =
    Scheme.strictHenselizationStructuralMap b

attribute [instance] SliceSpecialization.fieldA SliceSpecialization.closedA
  SliceSpecialization.fieldB SliceSpecialization.closedB

namespace SliceSpecialization

/-- The closed geometric fibre. Source: Orgogozo, Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
abbrev fibre {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S) :=
  pullback f d.a

/-- The special strict-local tube. Source: Orgogozo, Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
abbrev specialTube {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S) :=
  pullback f (Scheme.strictHenselizationStructuralMap d.a)

/-- The generic strict-local tube, not the geometric generic fibre.
Source: Orgogozo, §1 (blueprint: lem-trf-general-nearby-slice-test). -/
abbrev genericTube {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S) :=
  pullback f (Scheme.strictHenselizationStructuralMap d.b)

/-- The canonical closed-fibre inclusion. Source: Orgogozo, Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
def i {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S) :
    d.fibre f ⟶ d.specialTube f :=
  pullback.map f d.a f (Scheme.strictHenselizationStructuralMap d.a) (𝟙 X)
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d.a))) (𝟙 S)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Scheme.strictHenselizationClosedLift_over d.a).symm)

/-- The map induced by the specialization of strict localizations.
Source: Orgogozo, Lemma 3.1.1 (blueprint: lem-trf-general-nearby-slice-test). -/
def j {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S) :
    d.genericTube f ⟶ d.specialTube f :=
  pullback.map f (Scheme.strictHenselizationStructuralMap d.b) f
    (Scheme.strictHenselizationStructuralMap d.a) (𝟙 X) d.c (𝟙 S)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans d.over.symm)

/-- The sliced nearby complex, formed from the actual exact inverse images and
K-injective derived direct image. Source: Orgogozo, Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
def complex {X S : Scheme.{u}} (d : SliceSpecialization S) (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] : EtaleDerived X Λ ⥤ EtaleDerived (d.fibre f) Λ :=
  (etaleModules.{u, v} (pullback.fst f (Scheme.strictHenselizationStructuralMap d.b))).pull
      (Coeff.{u, v} Λ) ⋙ (etaleModules.{u, v} (d.j f)).push (Coeff.{u, v} Λ) ⋙
    (etaleModules.{u, v} (d.i f)).pull (Coeff.{u, v} Λ)

end SliceSpecialization

/-- Pointed compatible specialization diagrams over a scheme square. The projection
and closed-point equations force all three maps to be the induced fibre-product maps;
the strict-local maps are pointed maps over the base morphism.
Source: Orgogozo, Lemma 3.1.1 (blueprint: lem-trf-general-nearby-slice-test). -/
structure SliceChange {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (h : X' ⟶ X) (g : S' ⟶ S) (d : SliceSpecialization S)
    (d' : SliceSpecialization S') where
  aMap : Spec (.of d'.A) ⟶ Spec (.of d.A)
  bMap : Spec (.of d'.B) ⟶ Spec (.of d.B)
  aOver : d'.a ≫ g = aMap ≫ d.a
  bOver : d'.b ≫ g = bMap ≫ d.b
  aLoc : Scheme.strictHenselizationScheme d'.a ⟶ Scheme.strictHenselizationScheme d.a
  bLoc : Scheme.strictHenselizationScheme d'.b ⟶ Scheme.strictHenselizationScheme d.b
  aLocOver : Scheme.strictHenselizationStructuralMap d'.a ≫ g =
    aLoc ≫ Scheme.strictHenselizationStructuralMap d.a
  bLocOver : Scheme.strictHenselizationStructuralMap d'.b ≫ g =
    bLoc ≫ Scheme.strictHenselizationStructuralMap d.b
  aPoint : Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d'.a)) ≫
    aLoc = aMap ≫
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d.a))
  bPoint : Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d'.b)) ≫
    bLoc = bMap ≫
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d.b))
  specialization : d'.c ≫ aLoc = bLoc ≫ d.c
  fibreMap : d'.fibre f' ⟶ d.fibre f
  specialMap : d'.specialTube f' ⟶ d.specialTube f
  genericMap : d'.genericTube f' ⟶ d.genericTube f
  fibreLeft : fibreMap ≫ pullback.fst f d.a = pullback.fst f' d'.a ≫ h
  fibreRight : fibreMap ≫ pullback.snd f d.a = pullback.snd f' d'.a ≫ aMap
  specialLeft : specialMap ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap d.a) =
    pullback.fst f' (Scheme.strictHenselizationStructuralMap d'.a) ≫ h
  specialRight : specialMap ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap d.a) =
    pullback.snd f' (Scheme.strictHenselizationStructuralMap d'.a) ≫ aLoc
  genericLeft : genericMap ≫ pullback.fst f (Scheme.strictHenselizationStructuralMap d.b) =
    pullback.fst f' (Scheme.strictHenselizationStructuralMap d'.b) ≫ h
  genericRight : genericMap ≫ pullback.snd f (Scheme.strictHenselizationStructuralMap d.b) =
    pullback.snd f' (Scheme.strictHenselizationStructuralMap d'.b) ≫ bLoc
  iComm : d'.i f' ≫ specialMap = fibreMap ≫ d.i f
  jComm : d'.j f' ≫ specialMap = genericMap ≫ d.j f

/-- Exact derived inverse-image comparison for a commutative scheme square.
This is the already normalized set-sheaf comparison localized on constant modules.
Source: ILO XI §1.9 (blueprint: lem-trf-general-nearby-slice-test). -/
def slicePullSquare {P Q R T : Scheme.{u}} (a : Q ⟶ T) (b : P ⟶ R)
    (c : P ⟶ Q) (d : R ⟶ T) (w : c ≫ a = b ≫ d)
    (Λ : Type v) [CommRing Λ] :
    (etaleModules.{u, v} d).pull (Coeff.{u, v} Λ) ⋙ (etaleModules.{u, v} b).pull (Coeff.{u, v} Λ) ≅
      (etaleModules.{u, v} a).pull (Coeff.{u, v} Λ) ⋙
        (etaleModules.{u, v} c).pull (Coeff.{u, v} Λ) :=
  derivedSquare (f := etaleModules.{u, v} a) (g := etaleModules.{u, v} d)
    (h := etaleModules.{u, v} c) (k := etaleModules.{u, v} b)
    (GeometricMorphism.inverseIso (squareDirect.{u, v} a b c d w))
    (Coeff.{u, v} Λ)

/-- The ordinary sliced comparison: the inverse-image composition isomorphism, then
base change for `j` as the transpose of its direct-image counit, then restriction to
`K_T`. It is defined independently of nearby cycles and of any slice isomorphism.
Source: Orgogozo, Lemma 3.1.1 (blueprint: lem-trf-general-nearby-slice-test). -/
def ordinarySliceComparison {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (h : X' ⟶ X) (g : S' ⟶ S)
    (d : SliceSpecialization S) (d' : SliceSpecialization S')
    (z : SliceChange f f' h g d d') (Λ : Type v) [CommRing Λ]
    (K : EtaleDerived X Λ) :
    ((etaleModules.{u, v} z.fibreMap).pull (Coeff.{u, v} Λ)).obj ((d.complex f Λ).obj K) ⟶
      (d'.complex f' Λ).obj (((etaleModules.{u, v} h).pull (Coeff.{u, v} Λ)).obj K) :=
  (slicePullSquare z.specialMap z.fibreMap (d'.i f') (d.i f) z.iComm Λ).hom.app _ ≫
    ((etaleModules.{u, v} (d'.i f')).pull (Coeff.{u, v} Λ)).map
      (((etaleModules.{u, v} (d'.j f')).adj (Coeff.{u, v} Λ)).homEquiv _ _
        ((slicePullSquare (d.j f) (d'.j f') z.genericMap z.specialMap
          z.jComm.symm Λ).hom.app _ ≫
            ((etaleModules.{u, v} z.genericMap).pull (Coeff.{u, v} Λ)).map
              (((etaleModules.{u, v} (d.j f)).adj (Coeff.{u, v} Λ)).counit.app _))) ≫
    ((etaleModules.{u, v} (d'.i f')).pull (Coeff.{u, v} Λ)).map
      (((etaleModules.{u, v} (d'.j f')).push (Coeff.{u, v} Λ)).map
        ((slicePullSquare
          (pullback.fst f (Scheme.strictHenselizationStructuralMap d.b))
          (pullback.fst f' (Scheme.strictHenselizationStructuralMap d'.b))
          z.genericMap h z.genericLeft Λ).inv.app K))

/-- The geometric stalk on the transported site, calculated by the recorded pointed
étale neighbourhood colimit. Source: ILO XI §4.3
(blueprint: lem-trf-general-nearby-slice-test). -/
def sliceStalk {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Y) :
    Sheaf (etaleTopology.{u, v} Y) (Type (max (u + 1) v)) ⥤ Type (max (u + 1) v) :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft _ _ _).obj (AsSmall.up : Y.Etale ⥤ EtaleSite.{u, v} Y).op ⋙
      (Scheme.pointSmallEtale x).presheafFiber

/-- The fibre of an oriented triple at `(x,b,c)`, with `x` on the geometric closed
fibre. The intermediate lift `a → V` is descended along the geometric point `x → a`;
its strict-local extension is the specified neighbourhood-limit leg.
Source: ILO XI §4.3; Orgogozo §1
(blueprint: lem-trf-general-nearby-slice-test). -/
def slicePoint {X S : Scheme.{u}} (f : X ⟶ S) (d : SliceSpecialization S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ d.fibre f)
    (Z : VanishingSite.{u, v} f) :=
  {p : (Spec (.of Ω) ⟶ (AsSmall.down.obj Z.left.1).left) ×
      (Spec (.of d.B) ⟶ (AsSmall.down.obj Z.left.2).left) //
    p.1 ≫ (AsSmall.down.obj Z.left.1).hom = x ≫ pullback.fst f d.a ∧
    p.2 ≫ (AsSmall.down.obj Z.left.2).hom = d.b ∧
    ∃ va : (Scheme.pointSmallEtale d.a).fiber.obj (AsSmall.down.obj Z.right),
      ∃ l : Scheme.strictHenselizationScheme d.a ⟶ (AsSmall.down.obj Z.right).left,
      l ≫ (AsSmall.down.obj Z.right).hom = Scheme.strictHenselizationStructuralMap d.a ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d.a)) ≫
        l = va.left ∧
      p.1 ≫ (AsSmall.down.map Z.hom.1).left ≫
          pullback.fst (AsSmall.down.obj Z.right).hom f =
        x ≫ pullback.snd f d.a ≫ va.left ∧
      p.2 ≫ (AsSmall.down.map Z.hom.2).left =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation d.b)) ≫
          d.c ≫ l}

/-- A slice has precisely the oriented points `(x,b,c)`. Naturality in every triple
arrow specifies the point functor, not just cardinalities of its fibres.
Source: ILO XI §§1.8--1.12, 4.3 (blueprint: lem-trf-general-nearby-slice-test). -/
def IsSpecializationSlice {X S : Scheme.{u}} (f : X ⟶ S) (d : SliceSpecialization S)
    (e : GeometricMorphism
      (Sheaf (etaleTopology.{u, v} (d.fibre f)) (Type (max (u + 1) v)))
      (VanishingTopos.{u, v} f)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ d.fibre f),
    ∃ θ : ∀ Z : VanishingSite.{u, v} f,
      ((sliceStalk.{u, v} x).obj
        (e.inverse.obj ((OrientedProduct.associated (vanishingTopology f)).obj Z))) ≃
          slicePoint f d x Z,
      ∀ (Z W : VanishingSite.{u, v} f) (k : Z ⟶ W)
        (t : (sliceStalk.{u, v} x).obj
          (e.inverse.obj ((OrientedProduct.associated (vanishingTopology f)).obj Z))),
        (θ W ((sliceStalk x).map
          (e.inverse.map ((OrientedProduct.associated (vanishingTopology f)).map k)) t)).val =
          ((θ Z t).val.1 ≫ (AsSmall.down.map k.left.1).left,
            (θ Z t).val.2 ≫ (AsSmall.down.map k.left.2).left)

/-- Vanishing through degree `r`, with the actual standard cohomology functors.
Source: Orgogozo §3.1 (blueprint: lem-trf-general-nearby-slice-test). -/
def sliceVanishing (V : Site.{s}) (A : Type s) [CommRing A]
    (r : ℤ) (K : V.derived A) : Prop :=
  ∀ q : ℤ, q ≤ r → IsZero ((DerivedCategory.homologyFunctor (V.modules A) q).obj K)

/-- All cones are expressed by distinguished triangles, so no functorial cone choice
or extra shift is imposed. Source: Stacks 05RR; Orgogozo §3.1
(blueprint: lem-trf-general-nearby-slice-test). -/
def sliceConeVanishing (V : Site.{s}) (A : Type s) [CommRing A]
    {K L : V.derived A} (α : K ⟶ L) (r : ℤ) : Prop :=
  ∀ (C : V.derived A) (i : L ⟶ C) (p : C ⟶ K⟦(1 : ℤ)⟧),
    Triangle.mk α i p ∈ distTriang _ → sliceVanishing V A r C

set_option linter.checkUnivs false in
/-- The geometric slice morphisms, for all scheme morphisms in the fixed universes.
Source: ILO XI §4.3 (blueprint: lem-trf-general-nearby-slice-test). -/
abbrev SpecializationSliceFamily :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : SliceSpecialization S),
    GeometricMorphism
      (Sheaf (etaleTopology.{u, v} (d.fibre f)) (Type (max (u + 1) v)))
      (VanishingTopos.{u, v} f)

/-- The actual constant-module lift of a geometric slice.
Source: ILO XI §4.1 (blueprint: lem-trf-general-nearby-slice-test). -/
def sliceModules (E : SpecializationSliceFamily.{u, v})
    {X S : Scheme.{u}} (f : X ⟶ S) (d : SliceSpecialization S) :=
  moduleMorphism (vanishingDatum.{u, v} f) (etaleDatum (d.fibre f)) (E f d)

/-- The inclusion of bounded objects in the existing unbounded derived category.
Source: ILO XI §4.1 (blueprint: lem-trf-general-nearby-slice-test). -/
abbrev sliceBoundedInclusion (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :=
  ObjectProperty.ι (IsBounded (etaleDatum.{u, v} X) (Coeff.{u, v} Λ))

/-- A natural slice isomorphism on bounded complexes, not merely an objectwise
identification of cohomology groups. Source: Orgogozo, Lemma 3.1.1
(blueprint: lem-trf-general-nearby-slice-test). -/
abbrev SliceFormula (E : SpecializationSliceFamily.{u, v})
    {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type v) [CommRing Λ]
    (d : SliceSpecialization S) :=
  sliceBoundedInclusion X Λ ⋙ nearbyCycles f Λ ⋙
      (sliceModules E f d).pull (Coeff.{u, v} Λ) ≅
    sliceBoundedInclusion X Λ ⋙ d.complex f Λ

/-- The inverse-image identification for compatible slice squares, obtained by the
same generator-normalized module square used in ordinary nearby base change.
Source: ILO XI §1.9 (blueprint: lem-trf-general-nearby-slice-test). -/
def sliceSquare (E : SpecializationSliceFamily.{u, v})
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (h : X' ⟶ X) (g : S' ⟶ S) (w : h ≫ f = f' ≫ g)
    (d : SliceSpecialization S) (d' : SliceSpecialization S')
    (z : SliceChange f f' h g d d')
    (γ : ((E f' d').comp (squareMorphism f f' h g w)).direct ≅
      ((etaleMorphism z.fibreMap).comp (E f d)).direct)
    (Λ : Type v) [CommRing Λ] :
    (squareModules f f' h g w).pull (Coeff.{u, v} Λ) ⋙
        (sliceModules E f' d').pull (Coeff.{u, v} Λ) ≅
      (sliceModules E f d).pull (Coeff.{u, v} Λ) ⋙
        (etaleModules.{u, v} z.fibreMap).pull (Coeff.{u, v} Λ) :=
  derivedSquare (f := sliceModules E f d) (g := squareModules f f' h g w)
    (h := etaleModules.{u, v} z.fibreMap) (k := sliceModules E f' d')
    (GeometricMorphism.inverseIso γ).symm (Coeff.{u, v} Λ)

/-- The three assertions for a fixed finite-type morphism: natural slice formula,
identification of the ordinary counit comparisons, and detection of comparison-cone
cohomology by all compatible slices. Every integer cutoff and every base change occurs.
Source: Orgogozo, Lemma 3.1.1 (blueprint: lem-trf-general-nearby-slice-test). -/
def GeneralNearbySliceStatement (E : SpecializationSliceFamily.{u, v})
    {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type v) [CommRing Λ] : Prop :=
  ∃ ρ : ∀ d : SliceSpecialization S, SliceFormula E f Λ d,
    ∀ (T : Scheme.{u}) (g : T ⟶ S),
      ∃ σ : ∀ d' : SliceSpecialization T, SliceFormula E (pullback.snd f g) Λ d',
        (∀ (d : SliceSpecialization S) (d' : SliceSpecialization T)
          (z : SliceChange f (pullback.snd f g) (pullback.fst f g) g d d'),
          ∃ γ : ((E (pullback.snd f g) d').comp
              (squareMorphism f (pullback.snd f g) (pullback.fst f g) g
                (pullback.condition (f := f) (g := g)))).direct ≅
            ((etaleMorphism z.fibreMap).comp (E f d)).direct,
            ∀ (K : EtaleDerived X Λ)
              (hK : IsBounded (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K),
              ∃ hKT : IsBounded (etaleDatum.{u, v} (pullback f g)) (Coeff.{u, v} Λ)
                  (((etaleModules.{u, v} (pullback.fst f g)).pull (Coeff.{u, v} Λ)).obj K),
                (sliceSquare E f (pullback.snd f g) (pullback.fst f g) g
                    (pullback.condition (f := f) (g := g)) d d' z γ Λ).hom.app
                    ((nearbyCycles f Λ).obj K) ≫
                  ((etaleModules.{u, v} z.fibreMap).pull (Coeff.{u, v} Λ)).map
                    ((ρ d).hom.app ⟨K, hK⟩) ≫
                  ordinarySliceComparison f (pullback.snd f g) (pullback.fst f g) g
                    d d' z Λ K =
                ((sliceModules E (pullback.snd f g) d').pull (Coeff.{u, v} Λ)).map
                    (baseChange f (pullback.snd f g) (pullback.fst f g) g
                      (pullback.condition (f := f) (g := g)) Λ K) ≫
                  (σ d').hom.app ⟨_, hKT⟩) ∧
        (∀ (K : EtaleDerived X Λ),
          IsBounded (etaleDatum.{u, v} X) (Coeff.{u, v} Λ) K → ∀ r : ℤ,
          sliceConeVanishing (vanishingDatum (pullback.snd f g)) (Coeff.{u, v} Λ)
              (baseChange f (pullback.snd f g) (pullback.fst f g) g
                (pullback.condition (f := f) (g := g)) Λ K) r ↔
            ∀ (d : SliceSpecialization S) (d' : SliceSpecialization T)
              (z : SliceChange f (pullback.snd f g) (pullback.fst f g) g d d'),
              sliceConeVanishing (etaleDatum (d'.fibre (pullback.snd f g)))
                (Coeff.{u, v} Λ)
                (ordinarySliceComparison f (pullback.snd f g) (pullback.fst f g) g
                  d d' z Λ K) r)

/-- General specialization slices identify nearby cycles and their ordinary comparison,
and detect vanishing of its cone through any integer degree, universally in the base.

Source: Orgogozo, Modifications et cycles proches sur une base générale, Lemma 3.1.1,
printed p. 6, first proof paragraph and first displayed comparison; ILO XI §§1.8--1.12,
4.1--4.4 (blueprint: lem-trf-general-nearby-slice-test).

Proof plan:
1. Finite type is preserved by every base change (lem-sfb-finite-type-composition-base-change).
Exact termwise constant-module inverse image preserves the finite cohomological interval
(lem-weil-pbc-exact-functor-complex-cohomology). The annihilating integer remains invertible.
2. Apply lem-trf-nearby-specialization-slice to the bounded complexes, which are bounded below.
Its morphism has oriented points `(x,b,c)`, exactly the normalization above. It gives the
natural slice isomorphisms. Its compatibility, with the fixed counits of
`def-trf-oriented-nearby-cycles`, is the equality of the two composites in the statement.
The generic object in the sliced complex is the full strict localization at `b`.
3. Exact inverse image carries a distinguished cone triangle to a distinguished triangle
(lem-sf-exact-functor-derived-triangulated). Termwise the cone is `B^q ⊕ A^(q+1)`,
so the transported cone is a cone of the sliced comparison, with no degree shift.
4. The all-slices conservativity clause of lem-trf-nearby-specialization-slice detects each
cohomology sheaf of the cone. All specializations of T occur, by taking their images in S;
no pair in S is fixed in the test. This gives both implications with the same integer r,
including negative r. Repeat the argument after every preliminary base change U → S;
step 1 verifies its inputs and the successive-base-change compatibility fixes its maps.
-/
theorem general_nearby_slice_test
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 1 ≤ m) (hmΛ : ∀ x : Λ, m • x = 0)
    (hmS : IsUnit (m : Γ(S, ⊤))) :
    ∃ E : SpecializationSliceFamily.{u, v},
      (∀ {Y B : Scheme.{u}} (f' : Y ⟶ B) (d : SliceSpecialization B),
        IsSpecializationSlice f' d (E f' d)) ∧
      GeneralNearbySliceStatement E f Λ ∧
      ∀ (U : Scheme.{u}) (a : U ⟶ S),
        GeneralNearbySliceStatement E (pullback.snd f a) Λ := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
