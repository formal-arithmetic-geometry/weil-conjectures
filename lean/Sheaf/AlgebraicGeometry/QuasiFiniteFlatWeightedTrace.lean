/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.CompactifiableOverField
import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Artinian.Module
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Sheaf.RingTheory.SimpleFiltration
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Stability
import Sheaf.RingTheory.BasisIffBasisQuotientOfNilpotent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFpFiniteFactorization
import Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.QuasiFiniteFinitePartsPresentation
import WeilConjectures.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.RingTheory.SimpleFiltration
/-!
# Weighted trace for a quasi-finite flat morphism

Source: SGA 4, Exposé XVII, Theorem 6.2.3 and Variances 1–4
(blueprint: lem-pur-quasifinite-flat-weighted-trace).

The coordinates below are the actual restriction-of-germs maps, followed by the
inverse-image stalk comparison. Their index consists of lifts of the geometric point;
the associated point of the fibre is used to compute the local-ring length.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The point of the scheme-theoretic geometric fibre corresponding to a lift.
Source: SGA 4 XVII 6.2.2–6.2.3
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
noncomputable def weightedTraceFibrePoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y) (t : f.GeometricFiber y) :
    (pullback f y : Scheme.{u}) :=
  (pullback.lift t.1 (𝟙 _) (t.2.trans (Category.id_comp y).symm)) default

/-- The multiplicity is the finite composition length of the local fibre ring.
Source: SGA 4 XVII 6.2.3, construction p. 425, and the weighting of 6.2.4–6.2.5
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
noncomputable def weightedTraceMultiplicity {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y) (t : f.GeometricFiber y) : ℕ :=
  (Module.length ((pullback f y).presheaf.stalk (weightedTraceFibrePoint f y t))
    ((pullback f y).presheaf.stalk (weightedTraceFibrePoint f y t))).toNat

/-- The canonical coordinate of the stalk of `f_! f^* F` at a lift of `y`.
Source: SGA 4 XVII 6.1.4, 6.2.2–6.2.3
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
noncomputable def weightedTraceCoordinate (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (t : f.GeometricFiber y) :
    (Scheme.pointSmallEtale y).sheafFiber.obj
        ((lowerShriek (ModuleCat.{u + 1} B) f).obj
          ((upperStar (ModuleCat.{u + 1} B) f).obj F)) ⟶
      (Scheme.pointSmallEtale y).sheafFiber.obj F :=
  (Scheme.pointSmallEtale y).sheafFiber.map
      ((lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app
        ((upperStar (ModuleCat.{u + 1} B) f).obj F)) ≫
    stalkRestrict (ModuleCat.{u + 1} B) f y t
      ((upperStar (ModuleCat.{u + 1} B) f).obj F) ≫
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} B) f t.1).hom.app F ≫
    eqToHom (congrArg (fun s ↦ (Scheme.pointSmallEtale s).sheafFiber.obj F) t.2)

/-- The weighted-sum characterization, including all algebraically closed geometric points.
Source: SGA 4 XVII 6.2.3, construction p. 425, and the weighting of 6.2.4–6.2.5
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def IsQuasiFiniteFlatWeightedTrace (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (a : ((Scheme.pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} B)).obj
      ((lowerShriek (ModuleCat.{u + 1} B) f).obj
        ((upperStar (ModuleCat.{u + 1} B) f).obj F))),
    ((Scheme.pointSmallEtale y).sheafFiber.map (τ.app F)) a =
      ∑ᶠ t : f.GeometricFiber y,
        weightedTraceMultiplicity f y t • (weightedTraceCoordinate B f F y t) a

/-- Compatibility with arbitrary Noetherian base change, using the unique support
comparison inside ordinary direct image.
Source: SGA 4 XVII 6.2.3, Variance 2
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def WeightedTraceBaseChange (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ (X' Y' : Scheme.{u}) [IsNoetherian X'] [IsNoetherian Y']
    (a : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y') [HasCompactification f']
    (sq : IsPullback a f' f b)
    (τ' : upperStar (ModuleCat.{u + 1} B) f' ⋙ lowerShriek (ModuleCat.{u + 1} B) f' ⟶
      𝟭 (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} B))),
    IsQuasiFiniteFlatWeightedTrace B f' τ' →
    ∃ e : lowerShriek (ModuleCat.{u + 1} B) f ⋙ upperStar (ModuleCat.{u + 1} B) b ≅
        upperStar (ModuleCat.{u + 1} B) a ⋙ lowerShriek (ModuleCat.{u + 1} B) f',
      (∀ H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
        e.hom.app H ≫ (lowerShriekToLowerStar (ModuleCat.{u + 1} B) f').app
            ((upperStar (ModuleCat.{u + 1} B) a).obj H) =
          (upperStar (ModuleCat.{u + 1} B) b).map
              ((lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app H) ≫
            (baseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app H) ∧
      ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B),
        (upperStar (ModuleCat.{u + 1} B) b).map (τ.app F) =
          e.hom.app ((upperStar (ModuleCat.{u + 1} B) f).obj F) ≫
            (lowerShriek (ModuleCat.{u + 1} B) f').map
              ((squareUpperStarIso (ModuleCat.{u + 1} B) sq.toCommSq).inv.app F) ≫
            τ'.app ((upperStar (ModuleCat.{u + 1} B) b).obj F)

/-- Composition compatibility, with the composition comparison characterized inside
ordinary direct image, so that the comparison is not arbitrary.
Source: SGA 4 XVII 6.2.3, Variance 3
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def WeightedTraceComposition (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ (Z : Scheme.{u}) [IsNoetherian Z] (g : Y ⟶ Z)
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g] [QuasiCompact g]
    [HasCompactification g] [HasCompactification (f ≫ g)],
    g.IsQuasiFinite →
    ∀ (τg : upperStar (ModuleCat.{u + 1} B) g ⋙ lowerShriek (ModuleCat.{u + 1} B) g ⟶
        𝟭 (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)))
      (τfg : upperStar (ModuleCat.{u + 1} B) (f ≫ g) ⋙
          lowerShriek (ModuleCat.{u + 1} B) (f ≫ g) ⟶
        𝟭 (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B))),
      IsQuasiFiniteFlatWeightedTrace B g τg →
      IsQuasiFiniteFlatWeightedTrace B (f ≫ g) τfg →
      ∃ c : lowerShriek (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) g ≅
          lowerShriek (ModuleCat.{u + 1} B) (f ≫ g),
        (∀ H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
          c.hom.app H ≫ (lowerShriekToLowerStar (ModuleCat.{u + 1} B) (f ≫ g)).app H =
            (lowerShriekToLowerStar (ModuleCat.{u + 1} B) g).app
                ((lowerShriek (ModuleCat.{u + 1} B) f).obj H) ≫
              (lowerStar (ModuleCat.{u + 1} B) g).map
                ((lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app H) ≫
              (lowerStarComp (ModuleCat.{u + 1} B) f g).hom.app H) ∧
        ∀ F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B),
          c.hom.app ((upperStar (ModuleCat.{u + 1} B) (f ≫ g)).obj F) ≫ τfg.app F =
            (lowerShriek (ModuleCat.{u + 1} B) g).map
              ((lowerShriek (ModuleCat.{u + 1} B) f).map
                ((upperStarComp (ModuleCat.{u + 1} B) f g).hom.app F)) ≫
              (lowerShriek (ModuleCat.{u + 1} B) g).map
                (τ.app ((upperStar (ModuleCat.{u + 1} B) g).obj F)) ≫ τg.app F

/-- The canonical scalar-extension comparison is the adjoint of the unit-induced map
on compact supports, using the canonical restriction-of-scalars comparison k. Here E
with its displayed adjunction is precisely sheaf scalar extension, specified by its
universal property, as in lem-pod-etale-stalk-tensor-scalar.
Source: SGA 4 XVII 6.2.3, coefficient compatibility and the weighted-sum construction
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
noncomputable def weightedTraceScalarComparison
    {B B' : Type (u + 1)} [CommRing B] [CommRing B'] (φ : B →+* B')
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (k : lowerShriek (ModuleCat.{u + 1} B') f ⋙ Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ lowerShriek (ModuleCat.{u + 1} B) f)
    (E : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B'))
    (adj : E ⊣ Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    E.obj ((lowerShriek (ModuleCat.{u + 1} B) f).obj
        ((upperStar (ModuleCat.{u + 1} B) f).obj F)) ⟶
      (lowerShriek (ModuleCat.{u + 1} B') f).obj
        ((upperStar (ModuleCat.{u + 1} B') f).obj (E.obj F)) :=
  (adj.homEquiv _ _).symm
    ((lowerShriek (ModuleCat.{u + 1} B) f).map
        ((upperStar (ModuleCat.{u + 1} B) f).map (adj.unit.app F)) ≫
      (lowerShriek (ModuleCat.{u + 1} B) f).map
        ((upperStarRestrictScalarsIsoSheaf φ f).hom.app (E.obj F)) ≫
      k.inv.app ((upperStar (ModuleCat.{u + 1} B') f).obj (E.obj F)))

/-- Coefficient changes, including nonflat homomorphisms of finite coefficient rings,
commute with the trace after the canonical restriction-of-scalars comparisons.
Source: SGA 4 XVII 6.2.3, functoriality and the integral weighted construction
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def WeightedTraceCoefficientChange (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ (B' : Type (u + 1)) [CommRing B'] [Finite B'] (φ : B →+* B')
    (τ' : upperStar (ModuleCat.{u + 1} B') f ⋙ lowerShriek (ModuleCat.{u + 1} B') f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B'))),
    IsQuasiFiniteFlatWeightedTrace B' f τ' →
    ∃ k : lowerShriek (ModuleCat.{u + 1} B') f ⋙ Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
        Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ lowerShriek (ModuleCat.{u + 1} B) f,
      (∀ H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B'),
        k.hom.app H ≫ (lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app
            ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj H) =
          (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
              ((lowerShriekToLowerStar (ModuleCat.{u + 1} B') f).app H) ≫
            (lowerStarRestrictScalarsIso φ f).hom.app H) ∧
      (∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B'),
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).map (τ'.app F) =
          k.hom.app ((upperStar (ModuleCat.{u + 1} B') f).obj F) ≫
            (lowerShriek (ModuleCat.{u + 1} B) f).map
              ((upperStarRestrictScalarsIsoSheaf φ f).inv.app F) ≫
            τ.app ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj F)) ∧
      ∀ (E : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B'))
        (adj : E ⊣ Sheaf.restrictScalars Y.smallEtaleTopology φ)
        (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)),
        IsIso (weightedTraceScalarComparison φ f k E adj F) ∧
          weightedTraceScalarComparison φ f k E adj F ≫ τ'.app (E.obj F) = E.map (τ.app F)

/-- For an etale morphism the trace is the sum-of-sheets adjunction counit, using the
comparison fixed by graph extension into direct image.
Source: SGA 4 XVII 6.2.3 (etale specialization) and Proposition 6.2.11
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def WeightedTraceEtaleNormalization (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ [h : Etale f],
    ∃ e : etaleLowerShriek (ModuleCat.{u + 1} B) f h ≅ lowerShriek (ModuleCat.{u + 1} B) f,
      (∀ H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B),
        e.hom.app H ≫ (lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app H =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} B) f H) ∧
      ∀ F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B),
        e.hom.app ((upperStar (ModuleCat.{u + 1} B) f).obj F) ≫ τ.app F =
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) f h).counit.app F

/-- For finite locally free maps of constant rank, trace after the ordinary unit is rank
multiplication. The trace on direct image is specified through the canonical inclusion.
Source: SGA 4 XVII 6.2.3 (Variance 4) and 6.2.5 (Variance 4')
(blueprint: lem-pur-quasifinite-flat-weighted-trace). -/
def WeightedTraceRank (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) : Prop :=
  ∀ (r : ℕ) [f.IsFiniteLocallyFreeOfDegree r]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)),
    ∃ t : (lowerStar (ModuleCat.{u + 1} B) f).obj
        ((upperStar (ModuleCat.{u + 1} B) f).obj F) ⟶ F,
      (lowerShriekToLowerStar (ModuleCat.{u + 1} B) f).app
          ((upperStar (ModuleCat.{u + 1} B) f).obj F) ≫ t = τ.app F ∧
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).unit.app F ≫ t = r • 𝟙 F

/-- The exact quasi-finite compact-support functor and the unique flat weighted trace.
All comparisons in the compatibility predicates are fixed by their inclusions into
ordinary direct image; the coordinates are actual restriction-of-germs maps.
Source: SGA 4 XVII 6.1.4, Theorem 6.2.3, Variances 1–4, and 6.2.5–6.2.11.
(blueprint: lem-pur-quasifinite-flat-weighted-trace)

Proof plan:

1. Identify the sheaf functor and its derived value. By [lem-weil-pbc-quasifinite-fp-finite-
factorization], write $u=pj$ with $j:X\hookrightarrow T$ a quasi-compact open immersion and
$p:T\to Y$ finite of finite presentation. The base is quasi-compact by its finite affine cover and
quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]; $T$ is Noetherian by [lem-
weil-pbc-finite-type-over-noetherian]. By [lem-weil-pbc-finite-proper] this is a compactification.
The identities of [lem-cbc-proper-support-sheaf-composition] identify the sheaf of sections with
proper support with $p_*j_!$, naturally as a subsheaf of $u_*$. Extension by zero is exact by
[lem-weil-pbc-extension-by-zero-exact]; finite direct image is exact by [lemma-weil-pbc-finite-
direct-image-exact]. The latter abelian-sheaf assertion applies to module sheaves as well: direct
image forgets to the same abelian direct image, and kernels and cokernels carry their induced
$B$-actions. Thus $u_!=p_*j_!$ is exact. On a degree-zero sheaf $H$, finite direct image has no
higher cohomology, so $Rp_*Dj_!H=p_*j_!H$ in degree zero. The comparisons in [lem-amb-etale-
compact-comparisons] identify this value with the given compactification-independent $Ru_!H$; only
the bounded-below restriction is used here.

2. Compute the stalks, without assuming flatness. Apply [lemma-weil-pbc-finite-stalk-formula] to
the finite $p$ of Step 1 and $j_!H$. The inside/outside formula of [lem-weil-pbc-extension-by-
zero-stalks] removes exactly the points outside $X$, leaving $$(u_!H)_{\bar
y}=\bigoplus_{x\in|X_{\bar y}|}H_{\bar x}.$$ These are the canonical restriction-of-germs maps,
not arbitrarily chosen isomorphisms. For $H=u^*F$, the pullback-to-geometric-fibre identification
[lem-weil-pbc-etale-geometric-fibre-inverse-image-constant] gives $H_{\bar x}=F_{\bar y}$. Its
naturality preserves addition and every $b\in B$ action, so the formula is $B$-linear. The
support-composition and base-change maps in [lem-cbc-proper-support-sheaf-composition] preserve
the underlying sections, and hence give the corresponding reindexing identifications on these
sums.

3. Record the geometric fibre algebra. The fibre $T_{\bar y}$ of the finite $p$ in Step 1 is
finite over $\Omega$: on an affine chart a finite set of module generators remains generating
after tensoring with $\Omega$. By [lem-weil-pbc-finite-over-field-affine-finite-dim] write it as
$\operatorname{Spec}A$, with $A$ finite-dimensional over $\Omega$. By [lem-weil-pbc-finite-dim-
algebra-artinian], $A$ is Artinian. It has finitely many maximal ideals: otherwise successive
intersections of distinct maximal ideals strictly decrease (a product of elements lying in the
earlier maximal ideals and outside the new one witnesses strictness), contradicting the descending
chain condition. Every element $a$ of its Jacobson radical is nilpotent: stabilization
$a^nA=a^{n+1}A$ gives $a^n=a^{n+1}b$, and $1-ab$ is a unit because it lies in no maximal ideal, so
$a^n=0$. Therefore [lem-weil-pbc-product-of-localizations-at-maximal] gives $A\cong\prod_x A_x$
with local factors. Each factor is Artinian, since a decreasing chain of its ideals pulls back to
a decreasing chain in $A$. By [lem-weil-pbc-artinian-local-unique-prime] its spectrum is a
singleton. The open subscheme $X_{\bar y}\subset T_{\bar y}$ is consequently a union of some of
these finitely many clopen factors and is itself finite over $\Omega$. Each residue field is
$\Omega$ by [lem-weil-pbc-closed-point-residue-field-base]. This proves all the geometric
assertions needed to interpret the weights, including the empty fibre.

4. For a local factor $C$ of Step 3, its module length equals $\dim_\Omega C$. Indeed [lem-weil-
pbc-artinian-ring-self-finite-length] and [lem-weil-pbc-finite-length-module-simple-filtration]
give a finite filtration by simple $C$-modules. Every simple module over the commutative local
ring $C$ is its residue field: a nonzero element generates the simple module, the resulting
surjection $C\to M$ has maximal kernel, and that kernel is the unique maximal ideal. Thus every
simple quotient is $\Omega$. Additivity [lem-weil-pbc-length-additive-short-exact] makes the
length of $C$ the number of these quotients. The dimension is the same number: in each short exact
sequence lift a basis of the quotient and append a basis of the subspace. Induction on the
filtration gives $\operatorname{length}_C C=\dim_\Omega C$. Consequently a finite geometric fibre
algebra has dimension equal to the sum of the lengths of its local factors.

5. Construct the map on actual sheaves. Use the finite-parts presentation [lem-pur-quasifinite-
finite-parts-presentation]. In a decomposition $X_U=\coprod_{i\in I}V_i$, each finite $v_i$ for
$i\ne0$ is flat and locally finitely presented. For clarity, these properties survive the base
change to $U$: [lem-weil-pbc-flat-module-base-change] on affine charts and the local criterion
[lem-weil-pbc-flat-map-local-criterion] give flatness; [lem-weil-pbc-qcqs-morphism-permanence](3)
gives local finite presentation. Restriction to an open-and-closed source piece does not change
its local rings or local presentations. By [lem-weil-pbc-finite-flat-rank-iso], its rank
$n_i:U\to\mathbf N$ is locally constant and stable under every base change. Define on each open
where these finitely many functions are constant $$g_\phi:(a_i)_{i\ne0}\longmapsto\sum_{i\ne0} n_i
a_i.$$ The formulas agree on overlaps, so define a sheaf morphism on $U$. For a refinement
$\sigma:I'\to I$, the finite algebra of $V_i$ is the product of those of $V'_j$ with
$\sigma(j)=i$, hence $n_i=\sum_{\sigma(j)=i}n'_j$ for $i\ne0$. Thus
$$g_{\phi'}t_\sigma(a)=\sum_{j:\sigma(j)\ne0}n'_j a_{\sigma(j)}=\sum_{i\ne0}n_i a_i=g_\phi(a).$$
The new finite pieces carved out of $V_0$ receive the coordinate zero in $t_\sigma$ and contribute
nothing. Etale restriction compatibility follows from rank base change. The presentation's
universal property now gives the desired $B$-linear map $\tau_{u,F}:u_!u^*F\to F$. In particular
its existence is proved by compatible generators and relations, not inferred from an arbitrary
assignment on stalks.

6. Calculate the trace and prove uniqueness. At $\bar y$ take the finite-parts decomposition
supplied in [lem-pur-quasifinite-finite-parts-presentation] with remainder having empty fibre and
one geometric point in each finite piece. Its generators identify the stalk with the sum in Step
2. The rank $n_i(\bar y)$ is the $\Omega$-dimension of the single local fibre algebra by [lem-
weil-pbc-finite-flat-rank-iso]; Step 4 identifies it with its self-length. Thus $\tau_{u,F}$ has
exactly the displayed weighted-sum formula. If two sheaf maps have that formula, their equalizer
inclusion is an isomorphism on every geometric stalk. By [lemma-weil-pbc-geometric-stalk-
conservative] it is an isomorphism, and the maps are equal. This uses the sheaf category only.

7. Naturality and arbitrary Noetherian base change. Any morphism $F\to F'$ commutes on each
generator with the integer multiplication $n_i$; the presentation in [lem-pur-quasifinite-finite-
parts-presentation] therefore proves naturality. For $g:Y'\to Y$, use the actual support base-
change isomorphism of [lem-cbc-proper-support-sheaf-composition]. Pullback sends the generator for
$V_i/U$ to that for $V_i\times_YY'$ over $U\times_YY'$, and [lem-weil-pbc-finite-flat-rank-iso](2)
leaves its coefficient $n_i$ unchanged. The inverse-image functor on module sheaves is exact and
left adjoint to direct image by [prop-weil-pbc-inverse-image-modules-exact], so preserves the
colimit presentation and its epimorphic family of generators. The two maps agree on these pulled-
back generators and hence agree everywhere. All schemes to which the finite-parts result is
applied are Noetherian: base change preserves finite presentation by [lem-weil-pbc-qcqs-morphism-
permanence](3), and finite type over the Noetherian $Y'$ is Noetherian by [lem-weil-pbc-finite-
type-over-noetherian]. Separatedness and local quasi-finiteness pass to this base change by [lem-
weil-pbc-separated-lqf-base-change]. Its quasi-compactness is part of the finite presentation just
verified, so [pqf-lem-qf-locqf-qc] gives quasi-finiteness. Flatness follows from the affine base-
change argument of Step 5. No flatness of $g$ or invertibility of the order of $B$ is used.

8. Composition, including the nonreduced intermediate fibre. Let $v:Z\to X$ be another separated
quasi-finite flat morphism of finite presentation. For the composite $w=u\circ v$, local finite
presentation follows on affine charts from [lem-weil-pbc-finite-presentation-base-change-
composition](2), and flatness from [lem-pc-flat-compose]. The Noetherian schemes $Z$ and $Y$ are
quasi-compact and, by [lem-weil-pbc-locally-noetherian-quasi-separated], quasi-separated. Thus
[lem-weil-pbc-qcqs-morphism-permanence](1) gives quasi-compactness and quasi-separatedness of $w$,
completing finite presentation. Separatedness follows by factoring the composite diagonal as the
diagonal of $v$ followed by the base change of the diagonal of $u$, both closed immersions: on
affine charts their ring maps are surjective, tensoring a surjective ring map is still surjective,
and a composite of surjections is surjective. For any $y\in Y$, the space $|X_y|$ is discrete by
quasi-finiteness of $u$. Thus, in $|Z_y|$, the inverse image of each singleton $\{x\}$ is open and
is homeomorphic to the underlying fibre $|Z_x|$ of $v$; its points are isolated by quasi-
finiteness of $v$. Every point of $|Z_y|$ is therefore isolated, proving quasi-finiteness of $w$
directly from its definition. Thus $w$ is in the asserted class. At a geometric $\bar y$ of $Y$,
write $A_x=\mathcal O_{X_{\bar y},x}$ as in Step 3. Over $\operatorname{Spec}A_x$, the pullback of
$v$ is separated and locally quasi-finite by [lem-weil-pbc-separated-lqf-base-change], and of
finite presentation by [lem-weil-pbc-qcqs-morphism-permanence](3), hence quasi-finite by [pqf-lem-
qf-locqf-qc]. It is finite: apply the factorization of [lem-weil-pbc-quasifinite-fp-finite-
factorization] over this Artinian Noetherian base; its finite ambient scheme is finite-dimensional
over $\Omega$, and the product argument of Step 3 makes every open subscheme a finite union of
clopen local factors. Thus its coordinate algebra splits into local Artinian $\Omega$-algebras
$C_z$, one for each $z$ lying over $x$. Each $C_z$ is flat over $A_x$: [lem-weil-pbc-flat-module-
base-change] and [lem-weil-pbc-flat-map-local-criterion] give the base-changed flatness, and
restriction to its one-point clopen component gives the same local map. The maximal ideal
$\mathfrak m_x$ is nilpotent by [lem-weil-pbc-artinian-local-noetherian-nilpotent]. Choose a basis
of $C_z/\mathfrak m_xC_z$ over $\Omega=A_x/\mathfrak m_x$ and lift it to $C_z$. By [lem-weil-pbc-
local-artinian-basis-when-flat] these lifts form an $A_x$-basis. With
$e_z=\dim_\Omega(C_z/\mathfrak m_xC_z)$, counting the resulting $\Omega$-basis gives $$\dim_\Omega
C_z=e_z\dim_\Omega A_x.$$ Step 4 applies both to $C_z$ and to the local fibre ring $C_z/\mathfrak
m_xC_z$. Therefore the multiplicities satisfy $$m_{uv}(z)=m_u(x)m_v(z).$$ The sheaf composition
identification is the equality of sections in [lem-cbc-proper-support-sheaf-composition]; by Step
2 it identifies the stalk of $u_!v_!$ with the iterated direct sum indexed by $x$ and $z$ over
$x$. On a tuple $(a_z)$ the iterated trace is $$\sum_xm_u(x)\Bigl(\sum_{z\mapsto
x}m_v(z)a_z\Bigr)=\sum_zm_{uv}(z)a_z,$$ which is the trace of the composite by Step 6. Equality
follows by the equalizer argument of Step 6, using [lemma-weil-pbc-geometric-stalk-conservative].
In particular one must retain the thickening $\operatorname{Spec}A_x$ in this calculation;
replacing it by its reduced point prematurely would lose $m_u(x)$.

9. Coefficient changes. Restriction of scalars leaves all underlying sums and integer
multiplications unchanged. For a homomorphism $B\to B'$ of finite commutative rings, sheafified
scalar extension $B'\otimes_B-$ is left adjoint to restriction of scalars: the usual sectionwise
tensor/Hom adjunction descends to sheaves by the universal property of sheafification. Hence it
preserves the generators and relations of [lem-pur-quasifinite-finite-parts-presentation]. Put $F'
= B'\otimes_B F$. The unit $F\to\operatorname{Res}_B F'$ induces
$u_!u^*F\to\operatorname{Res}_B(u_!u^*F')$: restriction of scalars leaves the pullback and proper-
support sections unchanged. Applying the scalar-extension/restriction adjunction to this map
defines the canonical comparison $$B'\otimes_Bu_!u^*F\longrightarrow u_!u^*(B'\otimes_BF)$$ This
is an isomorphism: by [lem-pod-etale-stalk-tensor-scalar] and Step 2 it is the canonical bijection
$B'\otimes_B\bigoplus_xF_{\bar y}\cong\bigoplus_x(B'\otimes_BF_{\bar y})$ at each geometric stalk,
and [lemma-weil-pbc-geometric-stalk-conservative] applies. On each tensor generator both trace
maps send $b'\otimes(a_x)_x$ to $\sum_xm_x(b'\otimes a_x)$, so they agree. Tensor relations show
this calculation respects addition and balancing. Thus the coefficient compatibility is ordinary
sheaf scalar extension; no claim that a nonflat scalar extension is exact is needed.

10. Etale and degree normalization. If $u$ is etale, its geometric fibres are reduced: etaleness
is preserved by base change by [lem-weil-pbc-etale-base-change-finite-limits], and [etale-
proposition-etale-reduced] applies over the reduced field $\Omega$. Each local Artinian factor of
Step 3 is then a field: its maximal ideal is nilpotent by [lem-weil-pbc-artinian-local-noetherian-
nilpotent], hence zero in a reduced ring. Its residue field is $\Omega$, so its length is one. By
[lem-asd-etale-compact-support-normalization] the compact-support functor is etale sum extension
and its counit is the sum/evaluation map; the weights just computed and uniqueness in Step 6
identify $\tau$ with it. Finally, if $u$ is finite locally free of constant rank $r$, its unit
$F\to u_*u^*F$ sends $a$ to the diagonal tuple $(a)_x$, by the adjunction-unit description of the
generators in [lem-pur-quasifinite-finite-parts-presentation]. By [lem-weil-pbc-finite-flat-rank-
iso] and Step 4, $\sum_xm_x=\dim_\Omega\Gamma(X_{\bar y},\mathcal O)=r$, so the composite sends
$a$ to $ra$ on every stalk. The equalizer argument gives multiplication by $r$ as a sheaf map. For
$r=0$ the source fibre is empty and the map is zero; for the identity all weights and the trace
are one.
-/
theorem quasiFiniteFlatWeightedTrace (B : Type (u + 1)) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (hq : f.IsQuasiFinite) :
    PreservesFiniteLimits (lowerShriek (ModuleCat.{u + 1} B) f) ∧
    PreservesFiniteColimits (lowerShriek (ModuleCat.{u + 1} B) f) ∧
    Nonempty
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) 0 ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} B) f ≅
        lowerShriek (ModuleCat.{u + 1} B) f ⋙
          DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) 0) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      IsFinite (pullback.snd f y) ∧
      Finite (pullback f y : Scheme.{u}) ∧
      Function.Bijective (weightedTraceFibrePoint f y) ∧
      ∀ x : (pullback f y : Scheme.{u}),
        IsArtinianRing ((pullback f y).presheaf.stalk x) ∧
        IsFiniteLength ((pullback f y).presheaf.stalk x) ((pullback f y).presheaf.stalk x) ∧
        IsIso ((pullback.snd f y).residueFieldMap x)) ∧
    (∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Function.Bijective (fun a ↦ fun t : f.GeometricFiber y ↦
        (weightedTraceCoordinate B f F y t) a)) ∧
    (∃! τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
        𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)),
      IsQuasiFiniteFlatWeightedTrace B f τ) ∧
    ∀ τ : upperStar (ModuleCat.{u + 1} B) f ⋙ lowerShriek (ModuleCat.{u + 1} B) f ⟶
        𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)),
      IsQuasiFiniteFlatWeightedTrace B f τ →
      WeightedTraceBaseChange B f τ ∧ WeightedTraceComposition B f τ ∧
      WeightedTraceCoefficientChange B f τ ∧ WeightedTraceEtaleNormalization B f τ ∧
      WeightedTraceRank B f τ := by
  sorry

end AlgebraicGeometry.Etale
