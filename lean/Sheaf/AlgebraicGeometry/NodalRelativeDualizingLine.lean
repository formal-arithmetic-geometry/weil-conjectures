module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange
public import Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange
public import Sheaf.AlgebraicGeometry.CurveModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.RelativeDualizingTracePair
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme
import Sheaf.AlgebraicGeometry.NodalClosedPointsReduced
import Sheaf.AlgebraicGeometry.GorensteinCurveRelativeDualizing
import Sheaf.AlgebraicGeometry.ProperFlatSpaceDerivedDuality
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison

/-! # Relative dualizing lines of nodal algebraic-space curve families

Source: Stacks Project, moduli-curves.tex, Tags 0E6P, 0E6Q and 0E6R, including the
relative Serre-duality display after 0E6Q; curves.tex, Tag 0E37; spaces-over-fields.tex,
Tag 0ADD (blueprint: lem-sfb-nodal-relative-dualizing-line).

The existing family and nodal-fibre predicates retain algebraic-space total spaces.
All cartesian realizations of every scheme base change are included. Cohomology is
right derived in all module sheaves before restricting to quasi-coherent inputs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- First cohomology in the relative Serre-duality formula: right derive the existing
scalar sections functor in all module sheaves, then restrict its inputs to QCoh.
This is only an abbreviation for that composite, with no higher-direct-image theorem.
Source: Stacks, moduli-curves.tex, display after 0E6Q; Cohomology on Sites, 0B6C
(blueprint: lem-sfb-nodal-relative-dualizing-line). -/
abbrev nodalLineH1 {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (a : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) : X.QCoh ⥤ ModuleCat.{u} A :=
  (SheafOfModules.isQuasicoherent X.structureSheaf).ι ⋙ X.smallModuleRestriction ⋙
    (affineScalarSections A Y a X f).rightDerived 1

/-- A line in cohomologicaldegree -1, on the already equivalent small ringed model.
Source: Stacks, moduli-curves.tex, 0E6Q
(blueprint: lem-sfb-nodal-relative-dualizing-line). -/
def nodalLineSingle {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] (M : X.Modules) : X.DerivedModules :=
  (DerivedCategory.singleFunctor X.SmallModules (-1)).obj (X.smallModuleRestriction.obj M)

/-- The canonical map from derived pullback to the ordinary pullback of a line in
degree -1, followed by a specified ordinary module map. It uses the universal derived
counit and the actual basis equivalence, so it does not choose a derived comparison.
Source: Stacks, Cohomology on Sites, 06YY; moduli-curves.tex, 0E6P
(blueprint: lem-sfb-nodal-relative-dualizing-line). -/
def nodalLinePullbackMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (g : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (M : Y.Modules) (N : X.Modules) (h : (moduleTensorPullback g).obj M ⟶ N) :
    (spaceDerivedPullback g).obj (nodalLineSingle Y M) ⟶ nodalLineSingle X N :=
  (spaceDerivedPullback g).map
    ((DerivedCategory.singleFunctorIsoCompQ Y.SmallModules (-1)).hom.app
      (Y.smallModuleRestriction.obj M)) ≫
    ((smallTensorPullbackComplex g).totalLeftDerivedCounit DerivedCategory.Q
      (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ))).app
        ((HomologicalComplex.single Y.SmallModules (.up ℤ) (-1)).obj
          (Y.smallModuleRestriction.obj M)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (smallModuleTensorPullback g)
        (.up ℤ) (-1)).hom.app (Y.smallModuleRestriction.obj M)) ≫
    (DerivedCategory.singleFunctorIsoCompQ X.SmallModules (-1)).inv.app _ ≫
    (DerivedCategory.singleFunctor X.SmallModules (-1)).map
      (X.smallModuleRestriction.map
        ((moduleTensorPullback g).map (Y.smallModuleEquivalence.unitIso.inv.app M) ≫ h))

end AlgebraicSpace

/-- A cartesian realization of an arbitrary scheme base change of the family.
The square is in presheaves and remembers the actual maps, with no schematicity
assumption on the source space.
Source: Stacks, moduli-curves.tex, 0E6P--0E6R
(blueprint: lem-sfb-nodal-relative-dualizing-line). -/
structure NodalDualizingLineBaseChange {S : Scheme.{u}} {T : Over S}
    (C : ProperCurveFamily T) where
  base : Over S
  baseMap : base ⟶ T
  space : AlgebraicSpace S
  projection : space ⟶ AlgebraicSpace.schemeSpace base
  map : space ⟶ C.space
  square : IsPullback map.hom.hom projection.hom.hom C.projection (yoneda.map baseMap)

/-- A relative dualizing line, with its affine representing property and coherent
pullback identifications on every scheme base change. The unique comparison clause
is local on an affine base and fixes the comparison by its action on the represented
functor. Scheme restriction is the actual restriction to Zariski opens, so the last
field gives an ordinary invertible module, including on every schematic fibre.
Source: Stacks, moduli-curves.tex, 0E6Q (definition and following display), 0E6P, 0E6R;
Descent, 03DX and 05VG (blueprint: lem-sfb-nodal-relative-dualizing-line). -/
structure NodalDualizingLineSystem {S : Scheme.{u}} {T : Over S}
    (C : ProperCurveFamily T)
    [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules] where
  omega : ∀ B : NodalDualizingLineBaseChange C, B.space.Modules
  line : ∀ B : NodalDualizingLineBaseChange C, B.space.IsLineModule (omega B)
  trace : ∀ B : NodalDualizingLineBaseChange C,
    (AlgebraicSpace.derivedDirectImage B.projection).obj
      (AlgebraicSpace.nodalLineSingle B.space (omega B)) ⟶
        (AlgebraicSpace.schemeSpace B.base).derivedStructure
  dualizing : ∀ B : NodalDualizingLineBaseChange C,
    AlgebraicSpace.IsRelativeDualizingTracePair
      (AlgebraicSpace.RelativeDualizingTracePair.mk
        (AlgebraicSpace.nodalLineSingle B.space (omega B)) (trace B))
  serre : ∀ (B : NodalDualizingLineBaseChange C) (A : Type u) [CommRing A]
    (a : B.base.left ≅ Spec (.of A)) (F : B.space.QCoh),
    (F.obj ⟶ omega B) ≃
      ((AlgebraicSpace.nodalLineH1 A B.base a B.space B.projection).obj F ⟶
        ModuleCat.of A A)
  naturality : ∀ (B : NodalDualizingLineBaseChange C) (A : Type u) [CommRing A]
    (a : B.base.left ≅ Spec (.of A)) (F G : B.space.QCoh) (h : F ⟶ G)
    (t : G.obj ⟶ omega B),
    serre B A a F (h.hom ≫ t) =
      (AlgebraicSpace.nodalLineH1 A B.base a B.space B.projection).map h ≫
        serre B A a G t
  unique_affine : ∀ (B : NodalDualizingLineBaseChange C) (A : Type u) [CommRing A]
    (a : B.base.left ≅ Spec (.of A)) (M : B.space.Modules)
    (e : ∀ F : B.space.QCoh, (F.obj ⟶ M) ≃
      ((AlgebraicSpace.nodalLineH1 A B.base a B.space B.projection).obj F ⟶
        ModuleCat.of A A)),
    SheafOfModules.IsQuasicoherent M →
    (∀ (F G : B.space.QCoh) (h : F ⟶ G) (t : G.obj ⟶ M),
      e F (h.hom ≫ t) =
        (AlgebraicSpace.nodalLineH1 A B.base a B.space B.projection).map h ≫
          e G t) →
    ∃! i : M ≅ omega B, ∀ (F : B.space.QCoh) (h : F.obj ⟶ M),
      serre B A a F (h ≫ i.hom) = e F h
  baseChange : ∀ (B D : NodalDualizingLineBaseChange C)
    (g : D.space ⟶ B.space) (b : D.base ⟶ B.base),
    IsPullback g.hom.hom D.projection.hom.hom B.projection.hom.hom (yoneda.map b) →
    g ≫ B.map = D.map → b ≫ B.baseMap = D.baseMap →
      ((AlgebraicSpace.moduleTensorPullback g).obj (omega B) ≅ omega D)
  trace_baseChange : ∀ (B D : NodalDualizingLineBaseChange C)
    (g : D.space ⟶ B.space) (b : D.base ⟶ B.base)
    (hc : IsPullback g.hom.hom D.projection.hom.hom B.projection.hom.hom (yoneda.map b))
    (hg : g ≫ B.map = D.map) (hb : b ≫ B.baseMap = D.baseMap)
    (hw : g ≫ B.projection = D.projection ≫ AlgebraicSpace.traceSchemeMap b),
    AlgebraicSpace.moduleDerivedExchange B.projection D.projection
        (AlgebraicSpace.traceSchemeMap b) g hw
        (AlgebraicSpace.nodalLineSingle B.space (omega B)) ≫
      (AlgebraicSpace.derivedDirectImage D.projection).map
        (AlgebraicSpace.nodalLinePullbackMap g (omega B) (omega D)
          (baseChange B D g b hc hg hb).hom) ≫ trace D =
      (AlgebraicSpace.spaceDerivedPullback (AlgebraicSpace.traceSchemeMap b)).map (trace B) ≫
        AlgebraicSpace.traceDerivedStructureMap (AlgebraicSpace.traceSchemeMap b)
  identity : ∀ (B : NodalDualizingLineBaseChange C)
    (hc : IsPullback ((𝟙 B.space) : B.space ⟶ B.space).hom.hom
      B.projection.hom.hom B.projection.hom.hom
      (yoneda.map (𝟙 B.base)))
    (hg : 𝟙 B.space ≫ B.map = B.map) (hb : 𝟙 B.base ≫ B.baseMap = B.baseMap),
    baseChange B B (𝟙 B.space) (𝟙 B.base) hc hg hb =
      (AlgebraicSpace.moduleTensorPullbackId B.space).app (omega B)
  composition : ∀ (B D E : NodalDualizingLineBaseChange C)
    (g : D.space ⟶ B.space) (b : D.base ⟶ B.base)
    (h : E.space ⟶ D.space) (c : E.base ⟶ D.base)
    (hc₁ : IsPullback g.hom.hom D.projection.hom.hom B.projection.hom.hom (yoneda.map b))
    (hg₁ : g ≫ B.map = D.map) (hb₁ : b ≫ B.baseMap = D.baseMap)
    (hc₂ : IsPullback h.hom.hom E.projection.hom.hom D.projection.hom.hom (yoneda.map c))
    (hg₂ : h ≫ D.map = E.map) (hb₂ : c ≫ D.baseMap = E.baseMap)
    (hc₃ : IsPullback ((h ≫ g) : E.space ⟶ B.space).hom.hom
      E.projection.hom.hom B.projection.hom.hom
      (yoneda.map (c ≫ b)))
    (hg₃ : (h ≫ g) ≫ B.map = E.map) (hb₃ : (c ≫ b) ≫ B.baseMap = E.baseMap),
    baseChange B E (h ≫ g) (c ≫ b) hc₃ hg₃ hb₃ =
      ((AlgebraicSpace.moduleTensorComposition h g).app (omega B)).symm ≪≫
        (AlgebraicSpace.moduleTensorPullback h).mapIso
          (baseChange B D g b hc₁ hg₁ hb₁) ≪≫ baseChange D E h c hc₂ hg₂ hb₂
  scheme : ∀ (B : NodalDualizingLineBaseChange C) (U : Over S)
    (e : AlgebraicSpace.schemeSpace U ≅ B.space),
    ((AlgebraicSpace.schemeRestriction (AlgebraicSpace.schemeSpace U)
      (AlgebraicSpace.affineIdentityChart U)).obj
        ((AlgebraicSpace.moduleTensorPullback e.hom).obj (omega B))).IsInvertible

/-- The geometric fibres are reduced Gorenstein schemes, and the nodal family has
its relative dualizing line with natural relative Serre duality and arbitrary
base change, including the identity and iterated base changes.
Source: Stacks, moduli-curves.tex, 0E6P--0E6R and the display following 0E6Q;
curves.tex, 0E37; spaces-over-fields.tex, 0ADD
(blueprint: lem-sfb-nodal-relative-dualizing-line).

Proof:
1. Proper geometric fibres are separated and of finite type, with dimension one.
   Apply lem-sfb-separated-space-dimension-one-scheme to make them schemes, then
   lem-trf-nodal-points-reduced-algebraically-closed for reducedness. Over every
   algebraically closed extension the same argument applies. The scheme theorem
   lem-sfb-gorenstein-curve-relative-dualizing gives the fibre dualizing line and
   identifies its shifted complex with the right-adjoint dualizing object.
2. Lem-sfb-proper-field-algebraic-dualizing gives finite injective dimension of
   that complex at every stalk. Trivialize the line and undo the shift. Split off
   the injective negative-degree contractible summands of a bounded injective
   representative to obtain a finite injective resolution of the local ring.
3. Take the trace pair from lem-sfb-proper-flat-space-derived-duality. Its derived
   geometric-point fibres are one-dimensional in degree -1 by step 1. Apply
   lem-sfb-pseudocoherent-point-fibre-line with m=1: its H^-1 is a line and the
   complex is this line shifted by one. This is the relative dualizing module.
4. Derived trace-pair base change, followed by H^-1, gives ordinary tensor base
   change, since a line has no higher Tor. Trace-pair identity and composition
   give the displayed identity and composition equations on these modules.
5. On every affine base change, lem-sfb-proper-space-curve-qcoh-bound gives
   H^q(F)=0 for q>1 for every quasi-coherent F. Thus RΓ(F)[1] is nonpositive.
   Its truncation triangle and lem-pc-derived-tstructure-orthogonality identify
   Hom(RΓ(F)[1],A[0]) with Hom(H^1(F),A). The trace adjunction and
   lem-weil-pbc-derived-single-fully-faithful identify the first group with
   Hom(F,omega). Every comparison is natural in F; no flatness or coherence
   assumption on F is used.
6. Yoneda on quasi-coherent modules gives the unique affine comparison preserving
   these representing bijections; the line is quasi-coherent by local triviality.
   Uniqueness glues the comparisons. Finally lem-trf-scheme-etale-invertible-comparison
   identifies the actual Zariski restriction on a represented scheme with an ordinary
   invertible module. Apply this also to the schematic geometric fibres; their
   representing property is precisely ordinary Serre duality. -/
theorem exists_nodalDualizingLineSystem {S : Scheme.{u}} {T : Over S}
    [∀ Z : AlgebraicSpace S, HasDerivedCategory.{w} Z.SmallModules]
    (C : ProperCurveFamily T) (hnodal : C.HasNonemptyNodalGeometricFibres) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left),
      ∃ (U : Over S) (r : U ⟶ Over.mk (a ≫ T.hom))
        (e : yoneda.obj U ≅ Limits.pullback C.projection
          (yoneda.map (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T))),
        e.hom ≫ Limits.pullback.snd C.projection
          (yoneda.map (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)) = yoneda.map r ∧
        IsReduced U.left ∧ ∀ x : U.left,
          IsNoetherianRing (U.left.presheaf.stalk x) ∧
          ∃ n : ℕ, HasInjectiveDimensionLE
            (ModuleCat.of (U.left.presheaf.stalk x) (U.left.presheaf.stalk x)) n) ∧
    Nonempty (NodalDualizingLineSystem C) := by
  sorry

end AlgebraicGeometry
