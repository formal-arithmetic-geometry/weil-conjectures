module

public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Pullback compatibility of the hypercohomology edge

Source: Stacks Project, Tags 0BKV and 0D6H; the nonflat compatibility is the
shifted-unit argument recorded in the DAG
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback).

The edge, cohomology pullback, and Leray comparison are specified on representatives.
Only the theorem is postponed. The specification predicates and the maps on sections
and on hypercohomology have their full data here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedDerivedComparisons
open CategoryTheory.CoefficientDerivedSections
open SheafOfModules.RingedSiteCup

namespace SheafOfModules.RingedHypercohomology

/-- The ordinary scalar-extension unit comparison supplied by the normalized lift.
Its unit normalization determines it uniquely: it is multiplication of scalar tensors.
Source: Stacks Project, Tags 07A4 and 07A6
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def ordinaryUnit {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g) :
    l.edge.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring :=
  Classical.choose l.unit_canonical

/-- Pullback of a section, in the existing compatible-family encoding of Γ.
In the Hom(O,-) encoding this is j inverse followed by pullback of the section;
thus it is precisely s maps to 1 tensor inverse-image(s).
Source: Stacks Project, Tag 07A4
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def sectionPullback {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g)
    (F : Y.modules) (s : (coefficientSections Y.A).obj F) :
    (coefficientSections X.A).obj (l.edge.pullback.obj F) :=
  (globalUnderlyingSections X.corner).hom.app _
    ((ordinaryUnit l).inv ≫
      l.edge.pullback.map ((globalUnderlyingSections Y.corner).inv.app F s))

/-- The cocycle-to-sheaf edge normalization on every K-injective representative.
The first equality uniquely lifts the inclusion of global cycles to sections of cycles.
The second descends it to homology and then uses the canonical representative isomorphism.
Source: Stacks Project, Tag 0BKV (lemma-sheafification-cohomology)
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def EdgeSpec (X : Site.{u, w}) (n : ℤ)
    (e : globalAbelianDerived X.corner ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} n ⟶
      cohomology X.corner n ⋙ coefficientSections X.A) : Prop :=
  ∀ (I : CochainComplex X.modules ℤ), I.IsKInjective →
    ∃ z : ((coefficientComplexSections X.A).obj I).cycles n ⟶
        (coefficientSections X.A).obj (I.cycles n),
      z ≫ (coefficientSections X.A).map (I.iCycles n) =
        ((coefficientComplexSections X.A).obj I).iCycles n ∧
      ((coefficientComplexSections X.A).obj I).homologyπ n ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).inv.app
            ((coefficientComplexSections X.A).obj I) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            ((globalAbelianUnit X.corner).app I) ≫ e.app (DerivedCategory.Q.obj I) =
        z ≫ (coefficientSections X.A).map
          (I.homologyπ n ≫ (representativeCohomology X.corner I n).hom)

/-- The cohomology pullback r is fixed by tensors of local cocycles on every flat
K-flat representative. Factoring pullback(iCycles) through cycles is the tensor-of-cocycles
pairing κ in degrees (0,n), with H⁰(O'[0])=O'. No inverse to r is required.
Source: Stacks Project, Tags 07A4 and 0BKV, tensor-of-cocycles construction
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def PullbackSpec {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g) (n : ℤ)
    (r : cohomology Y.corner n ⋙ l.edge.pullback ⟶
      l.edge.left ⋙ cohomology X.corner n) : Prop :=
  ∀ (P : CochainComplex Y.modules ℤ), Y.corner.mateFlat P →
    ∃ (v : DerivedCategory.Q.obj
          ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≅
        l.edge.left.obj (DerivedCategory.Q.obj P))
      (z : l.edge.pullback.obj (P.cycles n) ⟶
        ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P).cycles n),
      v.inv = l.alpha P ∧
      z ≫ ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P).iCycles n =
        l.edge.pullback.map (P.iCycles n) ∧
      l.edge.pullback.map
          (P.homologyπ n ≫ (representativeCohomology Y.corner P n).hom) ≫
            r.app (DerivedCategory.Q.obj P) =
        z ≫ ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P).homologyπ n ≫
          (representativeCohomology X.corner _ n).hom ≫
          (cohomology X.corner n).map v.hom

/-- Ordinary global sections of direct image, normalized by the module adjunction.
The equation evaluates both sides at a section of the source module, so it fixes the
comparison on every compatible family, including on sites without a final object.
Source: Stacks Project, Tag 0D6H (lemma-Leray-unbounded)
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def SectionsComparisonSpec {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g)
    (θ : l.edge.pushforward ⋙ coefficientSections Y.A ≅ coefficientSections X.A) : Prop :=
  ∀ (F : X.modules) (s : (coefficientSections X.A).obj F),
    (globalUnderlyingSections Y.corner).inv.app (l.edge.pushforward.obj F)
        (θ.inv.app F s) =
      l.edge.moduleAdjunction.homEquiv (SheafOfModules.unit Y.ring) F
        ((ordinaryUnit l).hom ≫ (globalUnderlyingSections X.corner).inv.app F s)

/-- The Leray comparison is the canonical one whose right-derived units commute.
This specifies the composite RΓ Rg_* comparison on every K-injective complex.
Source: Stacks Project, Tag 0D6H (lemma-Leray-unbounded)
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def LeraySpec {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g)
    (θ : l.edge.pushforward ⋙ coefficientSections Y.A ≅ coefficientSections X.A)
    (c : l.edge.right ⋙ globalAbelianDerived Y.corner ≅ globalAbelianDerived X.corner) :
    Prop :=
  ∀ (I : CochainComplex X.modules ℤ), I.IsKInjective →
    (globalAbelianUnit Y.corner).app
          ((l.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (globalAbelianDerived Y.corner).map (l.eta.app I) ≫
        c.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso θ (.up ℤ)).hom.app I) ≫
        (globalAbelianUnit X.corner).app I

/-- P is cohomology of the derived adjunction unit, followed by the canonical Leray
comparison and derived global sections of t. Scalars are forgotten to compare the
underlying groups over the two possibly different rings of global sections.
Source: Stacks Project, Tags 07A6 and 0D6H
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback). -/
def hypercohomologyPullback {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g)
    (c : l.edge.right ⋙ globalAbelianDerived Y.corner ≅ globalAbelianDerived X.corner)
    {K : Y.D} {D : X.D} (t : l.edge.left.obj K ⟶ D) (n : ℤ) :
    (globalAbelianDerived Y.corner ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj K ⟶
      (globalAbelianDerived X.corner ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj D :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
    ((globalAbelianDerived Y.corner).map (l.edge.derivedAdjunction.unit.app K) ≫
      c.hom.app (l.edge.left.obj K) ≫ (globalAbelianDerived X.corner).map t)

/-- The nonflat, unbounded hypercohomology edge identity, with its specified canonical maps.
Source: Stacks Project, Tags 0BKV and 0D6H; shifted-unit argument in the DAG
(blueprint: lem-sfb-ringed-hypercohomology-edge-pullback).

Proof: (1) By lem-sfb-ringed-hypercohomology-shifted-unit represent x by
u : O[-n] to K, with edge Hⁿ(u)(1). Use the same external scalar ring on both
sites and then forget its action. (2) The comparison of
lem-sfb-ringed-derived-monoidal-comparisons identifies the Leray adjunction
with the composite adjunction. Unit naturality and the adjunction triangle show
that the pulled-back class is represented by t composed with L(u), under the
canonical shifted-unit comparison of lem-weil-pbc-ringed-projection-mate-exact.
(3) The cocycle pairing of def-sfb-ringed-site-module-cup-product is natural
in its second argument. Its value on the flat shifted unit is scalar multiplication,
so Hⁿ(Lu)(1)=r(1 tensor inverse-image(Hⁿ(u)(1))). This uses no flatness of K
or of the structural ring map. (4) Apply edge evaluation to t composed with L(u).
This yields the displayed identity. Naturality of the pairing gives naturality
of r; functoriality of the unit, Leray comparison, cohomology, and postcomposition
gives both naturality equations for P. Representative normalization gives the
edge and comparison independence, including on the empty site and for zero rings. -/
theorem edge_pullback {X Y : Site.{u, w}} {g : Morphism X Y} (l : Lift g) :
    ∃ (eY : ∀ n : ℤ,
        globalAbelianDerived Y.corner ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} n ⟶
          cohomology Y.corner n ⋙ coefficientSections Y.A)
      (eX : ∀ n : ℤ,
        globalAbelianDerived X.corner ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} n ⟶
          cohomology X.corner n ⋙ coefficientSections X.A)
      (r : ∀ n : ℤ, cohomology Y.corner n ⋙ l.edge.pullback ⟶
        l.edge.left ⋙ cohomology X.corner n)
      (θ : l.edge.pushforward ⋙ coefficientSections Y.A ≅ coefficientSections X.A)
      (c : l.edge.right ⋙ globalAbelianDerived Y.corner ≅ globalAbelianDerived X.corner),
      (∀ n : ℤ, EdgeSpec Y n (eY n) ∧ EdgeSpec X n (eX n) ∧ PullbackSpec l n (r n)) ∧
      SectionsComparisonSpec l θ ∧ LeraySpec l θ c ∧
      (∀ (K : Y.D) (D : X.D) (t : l.edge.left.obj K ⟶ D) (n : ℕ)
        (x : (globalAbelianDerived Y.corner ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).obj K),
        (eX (n : ℤ)).app D (hypercohomologyPullback l c t (n : ℤ) x) =
          (coefficientSections X.A).map
            ((r (n : ℤ)).app K ≫ (cohomology X.corner (n : ℤ)).map t)
            (sectionPullback l ((cohomology Y.corner (n : ℤ)).obj K)
              ((eY (n : ℤ)).app K x))) ∧
      (∀ (K K' : Y.D) (f : K ⟶ K') (D : X.D)
        (t : l.edge.left.obj K' ⟶ D) (n : ℤ),
        (globalAbelianDerived Y.corner ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map f ≫
            hypercohomologyPullback l c t n =
          hypercohomologyPullback l c (l.edge.left.map f ≫ t) n) ∧
      (∀ (K : Y.D) (D D' : X.D) (t : l.edge.left.obj K ⟶ D) (a : D ⟶ D') (n : ℤ),
        hypercohomologyPullback l c (t ≫ a) n =
          hypercohomologyPullback l c t n ≫
            (globalAbelianDerived X.corner ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map a) := by
  sorry

end SheafOfModules.RingedHypercohomology
