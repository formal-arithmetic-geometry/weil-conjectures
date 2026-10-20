/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.QcqsOrientedTriplePresentation
public import WeilConjectures.CategoryTheory.ColimitSites
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import Sheaf.AlgebraicGeometry.ExistsIsSeparatedOverPullbackMap
import Sheaf.TraceFormula.QCQSEtaleFinitarySite
import Sheaf.CategoryTheory.PseudofunctorSplitFamily
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import WeilConjectures.CategoryTheory.FilteredColimitCategories

/-! # Oriented triple sites along affine inverse limits

Source: ILO, Exposé XI §2.5 and §2.7(2.c); Stacks 01ZM, 07RP, 09YL, 0A35
(blueprint: lem-trf-oriented-triple-limit-descent).

The realization comparisons below are normalized by the three scheme projections.
Their identity, composition and cocone equations therefore express canonical pullback
coherence. The geometric comparisons are specified on sections, with inverse comparisons
obtained by adjunction mates, which retain the adjunction units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- Forget a triple to its left, middle and right schemes, in that order.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-triple-limit-descent). -/
def orientedTripleUnderlying {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    OrientedEtaleTriples f g ⥤ Scheme.{u} × (Scheme.{u} × Scheme.{u}) where
  obj Z := (Z.left.1.left, (Z.right.left, Z.left.2.left))
  map a := (a.left.1.left, (a.right.left, a.left.2.left))

/-- The three actual projections of componentwise scheme base change.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-triple-limit-descent). -/
def orientedTripleBaseChangeLeg {X S Y X' S' Y' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (a : X' ⟶ X) (b : S' ⟶ S) (d : Y' ⟶ Y)
    (ha : a ≫ f = f' ≫ b) (hd : d ≫ g = g' ≫ b)
    (Z : OrientedEtaleTriples f g) :
    (orientedTripleUnderlying f' g').obj
        ((orientedTripleBaseChange f g f' g' a b d ha hd).obj Z) ⟶
      (orientedTripleUnderlying f g).obj Z :=
  (pullback.fst Z.left.1.hom a,
    (pullback.fst Z.right.hom b, pullback.fst Z.left.2.hom d))

/-- Componentwise base change for an arrow of the inverse system.
Source: ILO XI §2.7(2.c), Stacks 01ZM
(blueprint: lem-trf-oriented-triple-limit-descent). -/
def orientedTripleSystemTransition {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    {i j : I} (a : j ⟶ i) :
    OrientedEtaleTriples (f.app i) (g.app i) ⥤
      OrientedEtaleTriples (f.app j) (g.app j) :=
  orientedTripleBaseChange (f.app i) (g.app i) (f.app j) (g.app j)
    (X.map a) (S.map a) (Y.map a) (f.naturality a) (g.naturality a)

/-- Base change from one stage to the componentwise limit, using the actual limit maps.
Source: ILO XI §2.7(2.c), Stacks 01ZM
(blueprint: lem-trf-oriented-triple-limit-descent). -/
def orientedTripleSystemProjection {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) [HasLimit X] [HasLimit S] [HasLimit Y]
    (f : X ⟶ S) (g : Y ⟶ S) (i : I) :
    OrientedEtaleTriples (f.app i) (g.app i) ⥤
      OrientedEtaleTriples (limMap f) (limMap g) :=
  orientedTripleBaseChange (f.app i) (g.app i) (limMap f) (limMap g)
    (limit.π X i) (limit.π S i) (limit.π Y i)
    (limMap_π f i).symm (limMap_π g i).symm

/-- The same two base-change functors on the recorded finite triple skeletons.
Source: ILO XI §2.7(2.c) (blueprint: lem-trf-oriented-triple-limit-descent). -/
def finiteTripleSystemTransition {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    {i j : I} (a : j ⟶ i) :
    FiniteOrientedTripleSite (f.app i) (g.app i) ⥤
      FiniteOrientedTripleSite (f.app j) (g.app j) :=
  finiteOrientedTripleBaseChange (f.app i) (g.app i) (f.app j) (g.app j)
    (X.map a) (S.map a) (Y.map a) (f.naturality a) (g.naturality a)

/-- Projection base change on the recorded finite triple skeletons.
Source: ILO XI §2.7(2.c) (blueprint: lem-trf-oriented-triple-limit-descent). -/
def finiteTripleSystemProjection {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) [HasLimit X] [HasLimit S] [HasLimit Y]
    (f : X ⟶ S) (g : Y ⟶ S) (i : I) :
    FiniteOrientedTripleSite (f.app i) (g.app i) ⥤
      FiniteOrientedTripleSite (limMap f) (limMap g) :=
  finiteOrientedTripleBaseChange (f.app i) (g.app i) (limMap f) (limMap g)
    (limit.π X i) (limit.π S i) (limit.π Y i)
    (limMap_π f i).symm (limMap_π g i).symm

/-- A geometric comparison specified on every section. Here `ρ` and `ρ'` say that the
site equivalences are restriction, `θ` is the scheme-base-change direct-image formula,
and `κ` compares the realized site functor with concrete triple base change. The displayed
formula uniquely specifies the direct comparison. Its inverse-image comparison is, by
convention, `(conjugateIsoEquiv ((e.symm.toAdjunction.comp t.adj).comp e'.toAdjunction)
(sheafAdjunctionContinuous v (Type (u+1)) J J')).symm δ`; hence it preserves units and the
canonical identity/composition comparisons of adjoints, rather than choosing inverse images.
Source: ILO XI §§1.6, 1.9, 2.7; Stacks 0A35
(blueprint: lem-trf-oriented-triple-limit-descent). -/
def HasOrientedTripleGeometricComparison
    {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} D]
    {X S Y X' S' Y' : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S'} {g' : Y' ⟶ S'}
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    (R : C ⥤ OrientedEtaleTriples f g) (R' : D ⥤ OrientedEtaleTriples f' g')
    (B : OrientedEtaleTriples f g ⥤ OrientedEtaleTriples f' g')
    (v : C ⥤ D) [v.IsContinuous J J'] (κ : R ⋙ B ≅ v ⋙ R')
    (e : Sheaf (orientedEtaleTopology f g) (Type (u + 1)) ≌ Sheaf J (Type (u + 1)))
    (e' : Sheaf (orientedEtaleTopology f' g') (Type (u + 1)) ≌ Sheaf J' (Type (u + 1)))
    (ρ : e.functor ⋙ sheafToPresheaf J (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology f g) (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj R.op)
    (ρ' : e'.functor ⋙ sheafToPresheaf J' (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology f' g') (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj R'.op)
    (t : GeometricMorphism (Sheaf (orientedEtaleTopology f' g') (Type (u + 1)))
      (Sheaf (orientedEtaleTopology f g) (Type (u + 1))))
    (θ : t.direct ⋙ sheafToPresheaf (orientedEtaleTopology f g) (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology f' g') (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj B.op) : Prop :=
  ∃ δ : e'.inverse ⋙ t.direct ⋙ e.functor ≅ v.sheafPushforwardContinuous (Type (u + 1)) J J',
    (∀ (F : Sheaf J' (Type (u + 1))) (Z : C),
      (δ.hom.app F).hom.app (op Z) =
        (ρ.hom.app (t.direct.obj (e'.inverse.obj F))).app (op Z) ≫
        (θ.hom.app (e'.inverse.obj F)).app (op (R.obj Z)) ≫
        (e'.inverse.obj F).obj.map (κ.inv.app Z).op ≫
        (ρ'.inv.app (e'.inverse.obj F)).app (op (v.obj Z)) ≫
        (e'.counitIso.hom.app F).hom.app (op (v.obj Z))) ∧
    ∀ K : Sheaf J (Type (u + 1)),
      ((e.symm.toAdjunction.comp t.adj).comp e'.toAdjunction).unit.app K ≫
          δ.hom.app ((e.inverse ⋙ t.inverse ⋙ e'.functor).obj K) =
        (sheafAdjunctionContinuous v (Type (u + 1)) J J').unit.app K ≫
          (v.sheafPushforwardContinuous (Type (u + 1)) J J').map
            (((conjugateIsoEquiv
              ((e.symm.toAdjunction.comp t.adj).comp e'.toAdjunction)
              (sheafAdjunctionContinuous v (Type (u + 1)) J J')).symm δ).hom.app K)

/-- The precise finite-composition precoverage of XI 2.5, before Grothendieck saturation.
It is the least precoverage containing the recorded three finite generators and closed under
finite indexed composition. Thus membership retains a finite tree of generating covers;
this does not replace the specified pretopology by all finite topological covering families.
Source: ILO XI proof of Lemma 2.5, printed p. 179
(blueprint: lem-trf-oriented-triple-limit-descent). -/
def finiteTripleCompositePrecoverage {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Precoverage (FiniteOrientedTripleSite f g) :=
  sInf {P | finiteOrientedTripleGenerators f g ≤ P ∧ P.IsStableUnderFiniteComposition}

/-- Finite geometric data descent on the actual triple skeletons. A finite table includes
objects, arrows, incidence, identities and composition equations. Arbitrarily long but
finitely many specified path relations are included by listing their intermediate composites.
The equality and covering clauses retain a prescribed initial stage and an actual arrow to it.
Source: ILO XI §2.7(2.c); Stacks 01ZM, 07RP
(blueprint: lem-trf-oriented-triple-limit-descent). -/
def HasFiniteTripleLimitDescent {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) [HasLimit X] [HasLimit S] [HasLimit Y]
    (f : X ⟶ S) (g : Y ⟶ S) : Prop :=
  (∀ (n m : ℕ) (Z : Fin n → FiniteOrientedTripleSite (limMap f) (limMap g))
    (A : Fin m → Arrow (FiniteOrientedTripleSite (limMap f) (limMap g))),
    ∃ (i : I) (Zi : Fin n → FiniteOrientedTripleSite (f.app i) (g.app i))
      (Ai : Fin m → Arrow (FiniteOrientedTripleSite (f.app i) (g.app i))),
      (∀ q, (finiteTripleSystemProjection X S Y f g i).obj (Zi q) = Z q) ∧
      (∀ p, (finiteTripleSystemProjection X S Y f g i).mapArrow.obj (Ai p) = A p) ∧
      (∀ p q, (A p).left = Z q → (Ai p).left = Zi q) ∧
      (∀ p q, (A p).right = Z q → (Ai p).right = Zi q) ∧
      (∀ (p q r : Fin m) (h : (A p).right = (A q).left),
        Arrow.mk ((A p).hom ≫ eqToHom h ≫ (A q).hom) = A r →
        ∃ hi : (Ai p).right = (Ai q).left,
          Arrow.mk ((Ai p).hom ≫ eqToHom hi ≫ (Ai q).hom) = Ai r) ∧
      (∀ p q, A p = Arrow.mk (𝟙 (Z q)) → Ai p = Arrow.mk (𝟙 (Zi q)))) ∧
  (∀ (i : I) (U V : FiniteOrientedTripleSite (f.app i) (g.app i)) (a b : U ⟶ V),
    (finiteTripleSystemProjection X S Y f g i).map a =
      (finiteTripleSystemProjection X S Y f g i).map b →
    ∃ (j : I) (c : j ⟶ i), (finiteTripleSystemTransition X S Y f g c).map a =
      (finiteTripleSystemTransition X S Y f g c).map b) ∧
  (∀ (i : I) (n : ℕ) (Z : FiniteOrientedTripleSite (f.app i) (g.app i))
    (U : Fin n → FiniteOrientedTripleSite (f.app i) (g.app i)) (a : ∀ q, U q ⟶ Z),
    Presieve.ofArrows
      (fun q ↦ (finiteTripleSystemProjection X S Y f g i).obj (U q))
      (fun q ↦ (finiteTripleSystemProjection X S Y f g i).map (a q)) ∈
        finiteTripleCompositePrecoverage (limMap f) (limMap g)
          ((finiteTripleSystemProjection X S Y f g i).obj Z) →
    ∃ (j : I) (c : j ⟶ i),
      Presieve.ofArrows
        (fun q ↦ (finiteTripleSystemTransition X S Y f g c).obj (U q))
        (fun q ↦ (finiteTripleSystemTransition X S Y f g c).map (a q)) ∈
          finiteTripleCompositePrecoverage (f.app j) (g.app j)
            ((finiteTripleSystemTransition X S Y f g c).obj Z))

/-- The strict colimit-site presentation and its canonical geometric realization.
All data are part of the conclusion, not an assumed abstract site system. The precoverages
consist exactly of finite covering presieves for the realized finite triple sites.
Source: ILO XI §§2.5, 2.7(2.c); Stacks 09YL, 0A35
(blueprint: lem-trf-oriented-triple-limit-descent). -/
structure OrientedTripleLimitPresentation {I : Type u} [SmallCategory I]
    (X S Y : I ⥤ Scheme.{u}) [HasLimit X] [HasLimit S] [HasLimit Y]
    (f : X ⟶ S) (g : Y ⟶ S) where
  /-- A strict diagram: functor laws are the required transition equalities. -/
  F : Iᵒᵖ ⥤ Cat.{u + 1, u + 1}
  /-- An actual strict cocone, including all projection/transition equalities. -/
  V : Cocone F
  /-- Stage finite precoverages. -/
  P : ∀ i : I, Precoverage (F.obj (op i))
  /-- Limit finite precoverage. -/
  Q : Precoverage V.pt
  /-- Stage category realizations. -/
  E : ∀ i : I, F.obj (op i) ≌ FiniteOrientedTripleSite (f.app i) (g.app i)
  /-- Limit category realization. -/
  L : V.pt ≌ FiniteOrientedTripleSite (limMap f) (limMap g)
  /-- Exactly the stage finite covering families, with their actual topology. -/
  stageCovers : ∀ (i : I) (Z : F.obj (op i)) (R : Presieve Z),
    R ∈ P i Z ↔ Finite R.uncurry ∧ R.map (E i).functor ∈
      finiteTripleCompositePrecoverage (f.app i) (g.app i) ((E i).functor.obj Z)
  /-- Exactly the limit finite covering families, with their actual topology. -/
  limitCovers : ∀ (Z : V.pt) (R : Presieve Z),
    R ∈ Q Z ↔ Finite R.uncurry ∧ R.map L.functor ∈
      finiteTripleCompositePrecoverage (limMap f) (limMap g) (L.functor.obj Z)
  /-- The defining transported-stage-cover formula of a colimit site. -/
  transportedCovers : ∀ (Z : V.pt) (R : Presieve Z), R ∈ Q Z ↔
    ∃ (i : I) (Zi : F.obj (op i)) (Ri : Presieve Zi)
      (h : (V.ι.app (op i)).toFunctor.obj Zi = Z),
      Ri ∈ P i Zi ∧ h ▸ Ri.map (V.ι.app (op i)).toFunctor = R
  /-- Object sets are the filtered colimit. -/
  objects : IsColimit (Cat.objects.mapCocone V)
  /-- Arrow sets are the filtered colimit. -/
  arrows : IsColimit (Cat.arrows.mapCocone V)
  /-- Finite limits at every stage. -/
  stageFiniteLimits : ∀ i : I, HasFiniteLimits (F.obj (op i))
  /-- Finite limits at the limit. -/
  limitFiniteLimits : HasFiniteLimits V.pt
  /-- Finite-limit preservation of transitions. -/
  transitionFiniteLimits : ∀ (i j : I) (a : j ⟶ i),
    PreservesFiniteLimits (F.map a.op).toFunctor
  /-- Finite-limit preservation of projections. -/
  projectionFiniteLimits : ∀ i : I, PreservesFiniteLimits (V.ι.app (op i)).toFunctor
  /-- Continuity of transitions. -/
  transitionContinuous : ∀ (i j : I) (a : j ⟶ i),
    (F.map a.op).toFunctor.IsContinuous (P i).toGrothendieck (P j).toGrothendieck
  /-- Continuity of projections. -/
  projectionContinuous : ∀ i : I,
    (V.ι.app (op i)).toFunctor.IsContinuous (P i).toGrothendieck Q.toGrothendieck
  /-- Finite covers are preserved by transitions. -/
  transitionCovers : ∀ (i j : I) (a : j ⟶ i) (Z : F.obj (op i)) (R : Presieve Z),
    R ∈ P i Z → R.map (F.map a.op).toFunctor ∈ P j ((F.map a.op).toFunctor.obj Z)
  /-- Finite covers are preserved by projections. -/
  projectionCovers : ∀ (i : I) (Z : F.obj (op i)) (R : Presieve Z),
    R ∈ P i Z → R.map (V.ι.app (op i)).toFunctor ∈ Q ((V.ι.app (op i)).toFunctor.obj Z)
  /-- Realize transitions as actual componentwise pullback. -/
  κ : ∀ (i j : I) (a : j ⟶ i),
    (E i).functor ⋙ finiteOrientedTripleInclusion (f.app i) (g.app i) ⋙
        orientedTripleSystemTransition X S Y f g a ≅
      (F.map a.op).toFunctor ⋙ (E j).functor ⋙
        finiteOrientedTripleInclusion (f.app j) (g.app j)
  /-- Realize projections as actual componentwise pullback to the limits. -/
  π : ∀ i : I,
    (E i).functor ⋙ finiteOrientedTripleInclusion (f.app i) (g.app i) ⋙
        orientedTripleSystemProjection X S Y f g i ≅
      (V.ι.app (op i)).toFunctor ⋙ L.functor ⋙
        finiteOrientedTripleInclusion (limMap f) (limMap g)
  /-- Canonical identity normalization, tested on all three scheme projections. -/
  identity : ∀ (i : I) (Z : F.obj (op i)),
    Arrow.mk ((orientedTripleUnderlying (f.app i) (g.app i)).map
          ((κ i i (𝟙 i)).inv.app (Z)) ≫
        orientedTripleBaseChangeLeg (f.app i) (g.app i) (f.app i) (g.app i)
          (X.map (𝟙 i)) (S.map (𝟙 i)) (Y.map (𝟙 i))
          (f.naturality (𝟙 i)) (g.naturality (𝟙 i))
          ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj
            ((E i).functor.obj (Z)))) =
      Arrow.mk (𝟙 ((orientedTripleUnderlying (f.app i) (g.app i)).obj
        ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj ((E i).functor.obj Z))))
  /-- Canonical composition normalization, tested on all three scheme projections. -/
  composition : ∀ (i j k : I) (a : j ⟶ i) (b : k ⟶ j) (Z : F.obj (op i)),
    Arrow.mk (((orientedTripleUnderlying (f.app k) (g.app k)).map
          ((κ j k (b)).inv.app ((F.map a.op).toFunctor.obj Z)) ≫
        orientedTripleBaseChangeLeg (f.app j) (g.app j) (f.app k) (g.app k)
          (X.map (b)) (S.map (b)) (Y.map (b))
          (f.naturality (b)) (g.naturality (b))
          ((finiteOrientedTripleInclusion (f.app j) (g.app j)).obj
            ((E j).functor.obj ((F.map a.op).toFunctor.obj Z)))) ≫
      ((orientedTripleUnderlying (f.app j) (g.app j)).map
          ((κ i j (a)).inv.app (Z)) ≫
        orientedTripleBaseChangeLeg (f.app i) (g.app i) (f.app j) (g.app j)
          (X.map (a)) (S.map (a)) (Y.map (a))
          (f.naturality (a)) (g.naturality (a))
          ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj
            ((E i).functor.obj (Z))))) =
      Arrow.mk ((orientedTripleUnderlying (f.app k) (g.app k)).map
          ((κ i k (b ≫ a)).inv.app (Z)) ≫
        orientedTripleBaseChangeLeg (f.app i) (g.app i) (f.app k) (g.app k)
          (X.map (b ≫ a)) (S.map (b ≫ a)) (Y.map (b ≫ a))
          (f.naturality (b ≫ a)) (g.naturality (b ≫ a))
          ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj
            ((E i).functor.obj (Z))))
  /-- Canonical projection/transition normalization. -/
  cocone : ∀ (i j : I) (a : j ⟶ i) (Z : F.obj (op i)),
    Arrow.mk (((orientedTripleUnderlying (limMap f) (limMap g)).map
          ((π j).inv.app ((F.map a.op).toFunctor.obj Z))
      ≫
        orientedTripleBaseChangeLeg (f.app j) (g.app j) (limMap f) (limMap g)
          (limit.π X j) (limit.π S j) (limit.π Y j)
          (limMap_π f j).symm (limMap_π g j).symm
          ((finiteOrientedTripleInclusion (f.app j) (g.app j)).obj
            ((E j).functor.obj ((F.map a.op).toFunctor.obj Z)))) ≫
      ((orientedTripleUnderlying (f.app j) (g.app j)).map
          ((κ i j (a)).inv.app (Z)) ≫
        orientedTripleBaseChangeLeg (f.app i) (g.app i) (f.app j) (g.app j)
          (X.map (a)) (S.map (a)) (Y.map (a))
          (f.naturality (a)) (g.naturality (a))
          ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj
            ((E i).functor.obj (Z))))) =
      Arrow.mk ((orientedTripleUnderlying (limMap f) (limMap g)).map ((π i).inv.app (Z)) ≫
        orientedTripleBaseChangeLeg (f.app i) (g.app i) (limMap f) (limMap g)
          (limit.π X i) (limit.π S i) (limit.π Y i)
          (limMap_π f i).symm (limMap_π g i).symm
          ((finiteOrientedTripleInclusion (f.app i) (g.app i)).obj
            ((E i).functor.obj (Z))))
  /-- The stage oriented-topos equivalences. -/
  e : ∀ i : I, Sheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1)) ≌
    Sheaf (P i).toGrothendieck (Type (u + 1))
  /-- The limit oriented-topos equivalence. -/
  l : Sheaf (orientedEtaleTopology (limMap f) (limMap g)) (Type (u + 1)) ≌
    Sheaf Q.toGrothendieck (Type (u + 1))
  /-- Stage equivalences are restriction along the specified realization. -/
  ρ : ∀ i : I,
    (e i).functor ⋙ sheafToPresheaf (P i).toGrothendieck (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj
          ((E i).functor ⋙ finiteOrientedTripleInclusion (f.app i) (g.app i)).op
  /-- The limit equivalence is restriction along the specified realization. -/
  σ : l.functor ⋙ sheafToPresheaf Q.toGrothendieck (Type (u + 1)) ≅
    sheafToPresheaf (orientedEtaleTopology (limMap f) (limMap g)) (Type (u + 1)) ⋙
      (whiskeringLeft _ _ (Type (u + 1))).obj
        (L.functor ⋙ finiteOrientedTripleInclusion (limMap f) (limMap g)).op
  /-- Transition inverse images are left exact, so they define geometric morphisms. -/
  transitionLeftExact : ∀ (i j : I) (a : j ⟶ i),
    PreservesFiniteLimits (sheafPullback (F.map a.op).toFunctor (Type (u + 1))
      (P i).toGrothendieck (P j).toGrothendieck)
  /-- Projection inverse images are left exact. -/
  projectionLeftExact : ∀ i : I,
    PreservesFiniteLimits (sheafPullback (V.ι.app (op i)).toFunctor (Type (u + 1))
      (P i).toGrothendieck Q.toGrothendieck)
  /-- Agreement with every representative of the componentwise geometric base change. -/
  transitionGeometric : ∀ (i j : I) (a : j ⟶ i)
    [_h : (F.map a.op).toFunctor.IsContinuous (P i).toGrothendieck (P j).toGrothendieck]
    (t : GeometricMorphism
      (Sheaf (orientedEtaleTopology (f.app j) (g.app j)) (Type (u + 1)))
      (Sheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1))))
    (θ : t.direct ⋙
        sheafToPresheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology (f.app j) (g.app j)) (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj
          (orientedTripleSystemTransition X S Y f g a).op),
    HasOrientedTripleGeometricComparison (P i).toGrothendieck (P j).toGrothendieck
      ((E i).functor ⋙ finiteOrientedTripleInclusion (f.app i) (g.app i))
      ((E j).functor ⋙ finiteOrientedTripleInclusion (f.app j) (g.app j))
      (orientedTripleSystemTransition X S Y f g a) (F.map a.op).toFunctor
      (κ i j a) (e i) (e j) (ρ i) (ρ j) t θ
  /-- The same canonical comparison for projection to the limit, with its unit equation. -/
  projectionGeometric : ∀ (i : I)
    [_h : (V.ι.app (op i)).toFunctor.IsContinuous (P i).toGrothendieck Q.toGrothendieck]
    (t : GeometricMorphism
      (Sheaf (orientedEtaleTopology (limMap f) (limMap g)) (Type (u + 1)))
      (Sheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1))))
    (θ : t.direct ⋙
        sheafToPresheaf (orientedEtaleTopology (f.app i) (g.app i)) (Type (u + 1)) ≅
      sheafToPresheaf (orientedEtaleTopology (limMap f) (limMap g)) (Type (u + 1)) ⋙
        (whiskeringLeft _ _ (Type (u + 1))).obj
          (orientedTripleSystemProjection X S Y f g i).op),
    HasOrientedTripleGeometricComparison (P i).toGrothendieck Q.toGrothendieck
      ((E i).functor ⋙ finiteOrientedTripleInclusion (f.app i) (g.app i))
      (L.functor ⋙ finiteOrientedTripleInclusion (limMap f) (limMap g))
      (orientedTripleSystemProjection X S Y f g i) (V.ι.app (op i)).toFunctor
      (π i) (e i) l (ρ i) σ t θ

/-- Affine-transition descent for the finite-cover oriented triple sites, their strict
colimit-site presentation, and their geometric inverse images.

Source: ILO XI §2.5 and §2.7(2.c), printed pp. 179--180; Stacks 01ZM, 07RP, 09YL, 0A35
(blueprint: lem-trf-oriented-triple-limit-descent).

Proof (the twelve steps of the DAG node):
1. For any initial stage i, the slice I/i is cofiltered and its forgetful functor is initial
(lem-weil-pbc-initial-functor-cofiltered-criterion). Directed reindexing of its opposite
(lem-weil-pbc-filtered-category-directed-cofinal) gives simultaneous directed descent for
all three bases, retaining an actual arrow to i. Without an initial stage use nonemptiness.
2. Affine limit projections (lem-weil-pbc-limit-affine-transition) are qcqs by
lem-weil-pbc-affine-morphism-permanence. The limit schemes and structural arrows are qcqs
by lem-weil-pbc-qcqs-morphism-permanence, so the recorded triple presentations apply.
3. Descend the three separated etale finite-presentation coordinates using the object
clause of lem-weil-pbc-etale-finite-data-descent and lem-weil-pbc-descend-separated.
Their sources are qcqs since their structure morphisms are of finite presentation.
4. Encode a cross arrow U → V as an X-map U → X ×_S V. The pullback target is etale of
finite presentation by lem-trf-qcqs-etale-finitary-site. Descend that map using the morphism
clause of finite-data descent; do the same over Y. No finite presentation of X → S is used.
5. Descend triple arrows componentwise. Their commutativity and all finitely many specified
relations are equalities of maps into these same pullback targets. The equality clause of
finite-data descent imposes them at a common later stage. Include inverses to descend isos.
6. Types (a),(b) descend by the finite-data covering clause. For type (c), descend the middle
arrow and left lift; define the right source by the required fibre product. A finite tree
of such generators descends with its equations, giving the exact composite precoverage.
7. Strictify componentwise base change, including the limit pseudocone, with
lem-coef-pseudofunctor-split-family-strictification. Retain its realization comparisons.
Uniqueness of maps into the three pullbacks gives their identity and composition equations.
8. Transport the finite precoverages along the equivalences. Base change preserves all
three types, finite compositions and finite limits. Apply
lem-weil-pbc-left-exact-site-inverse-image-tensor and lem-weil-pbc-colimit-of-sites to form
the strict cocone with the stated object/arrow colimits and transported-cover formula.
9. Finite triple descent gives essential surjectivity of the realization. The Hom-colimit
clause of lem-weil-pbc-filtered-colimit-categories and eventual equality give full
faithfulness. Cover descent and descent of isomorphisms give an equivalence of sites.
10. The realization reflects finite limits, so the strict cocone preserves them. Covers
are preserved by construction; the left-exact-site theorem supplies continuity and left
exactness of the inverse images. Functor and cocone laws are strict equalities.
11. The canonical generator formula of lem-trf-qcqs-oriented-triple-presentation, Yoneda
(lem-galois-yoneda-hom-bijection) and sheafification (def-weil-pbc-sheafification) identify
the componentwise geometric direct images with restriction by concrete triple base change.
Transport across the restriction equivalences gives exactly the displayed section formula.
12. The three scheme projections normalize the identity, composition and cocone comparisons.
The units and associativity of ordinary inverse images are those of
lem-weil-pbc-sets-etale-inverse-image-composition-units. The generator fibre-product formula
of lem-trf-oriented-product-universal preserves them by uniqueness. Taking adjunction mates
of the specified direct comparisons gives the unit equation and the canonical inverse-image
identity/composition comparisons, by the mate bijection and its composition laws. -/
theorem orientedTripleLimitDescent
    (I : Type u) [SmallCategory I] [IsCofiltered I]
    (X S Y : I ⥤ Scheme.{u}) [HasLimit X] [HasLimit S] [HasLimit Y]
    (f : X ⟶ S) (g : Y ⟶ S)
    [∀ i : I, CompactSpace (X.obj i)] [∀ i : I, QuasiSeparatedSpace (X.obj i)]
    [∀ i : I, CompactSpace (S.obj i)] [∀ i : I, QuasiSeparatedSpace (S.obj i)]
    [∀ i : I, CompactSpace (Y.obj i)] [∀ i : I, QuasiSeparatedSpace (Y.obj i)]
    [∀ (i j : I) (a : i ⟶ j), IsAffineHom (X.map a)]
    [∀ (i j : I) (a : i ⟶ j), IsAffineHom (S.map a)]
    [∀ (i j : I) (a : i ⟶ j), IsAffineHom (Y.map a)] :
    (CompactSpace (limit X : Scheme.{u}) ∧ QuasiSeparatedSpace (limit X : Scheme.{u})) ∧
    (CompactSpace (limit S : Scheme.{u}) ∧ QuasiSeparatedSpace (limit S : Scheme.{u})) ∧
    (CompactSpace (limit Y : Scheme.{u}) ∧ QuasiSeparatedSpace (limit Y : Scheme.{u})) ∧
    (QuasiCompact (limMap f) ∧ QuasiSeparated (limMap f)) ∧
    (QuasiCompact (limMap g) ∧ QuasiSeparated (limMap g)) ∧
    HasFiniteTripleLimitDescent X S Y f g ∧
    Nonempty (OrientedTripleLimitPresentation X S Y f g) := by
  sorry

end AlgebraicGeometry.Scheme
