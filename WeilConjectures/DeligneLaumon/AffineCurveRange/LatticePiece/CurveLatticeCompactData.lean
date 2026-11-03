/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-!
# The lattice pieces in the affine curve range argument

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, devissage and lattice paragraphs.
The integral compact-support object is the ordinary condensed construction.
Its reduction tower retains the canonical quotient transition maps. No integral
compact-support object is defined by taking an inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.AffineCurveRange

/-- Match the ordinary module derived universe used by compact Qbar sections.
Source: the ordinary point coefficient convention
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev latticeModuleDerived (R : Type (u + 1)) [CommRing R] :
    HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} R) := HasDerivedCategory.standard _

attribute [local instance] latticeModuleDerived

/-- Scalar extension is additive because it preserves finite coproducts.
Source: exact coefficient extension in the lattice paragraph
(blueprint: def-zl-curve-lattice-compact-data). -/
instance latticeScalarExtension_additive {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (r : R →+* S) : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} r).Additive := by
  let : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} r).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r).isLeftAdjoint
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} r) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- A lisse integral coefficient on a smooth separated finite-type scheme of
relative dimension at most one. The dense open curve pieces have dimension one;
the reduced finite complements over the algebraically closed field have dimension zero.

Source: latest blueprint, `lem-zl-affine-curve-range.proof.md`, devissage and lattice
paragraphs (blueprint: def-zl-curve-lattice-compact-data).
This structure records existing data. In particular its lattice is an actual module,
and the compactification is supplied as data, rather than chosen from a proof hole.
-/
structure LatticePiece (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] where
  E : Type u
  [field : Field E]
  [algebra : Algebra (Padic ell) E]
  [finiteDimensional : FiniteDimensional (Padic ell) E]
  X : Over (Spec (.of k))
  [locallyOfFiniteType : LocallyOfFiniteType X.hom]
  [quasiCompact : QuasiCompact X.hom]
  [separated : IsSeparated X.hom]
  dimension : ℕ
  dimension_le_one : dimension ≤ 1
  [smooth : SmoothOfRelativeDimension dimension X.hom]
  M : AdicCompletion.Modules ell E X.left
  lisse : IsLisseCoefficientModule (DerivedNakayama.integerRing ell E) M
  compactification : Compactification X.hom

attribute [instance] LatticePiece.field LatticePiece.algebra LatticePiece.finiteDimensional
  LatticePiece.locallyOfFiniteType LatticePiece.quasiCompact LatticePiece.separated
  LatticePiece.smooth

namespace LatticePiece

variable {ell : ℕ} [Fact ell.Prime] {k : Type u} [Field k]
  (d : LatticePiece ell k)

/-- The actual lisse lattice is constructible with finite constant local models.
Source: the lattice paragraph, where locally finite free lattices are constructible
(blueprint: def-zl-curve-lattice-compact-data).
The finite-type scheme is Noetherian. A trivial one-stratum stratification and the
finite free local models of the lisse lattice give the required constructibility. -/
theorem constructible :
    IsConstantModelConstructible (DerivedNakayama.integerRing ell d.E) d.X.left d.M := by
  classical
  have : IsLocallyNoetherian d.X.left := LocallyOfFiniteType.isLocallyNoetherian d.X.hom
  have : CompactSpace d.X.left := QuasiCompact.compactSpace_of_compactSpace d.X.hom
  have : IsNoetherian d.X.left := {}
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  exact ⟨Scheme.Stratification.trivial d.X.left, fun _ ↦
    pullback_finiteConstantLocalModel (DerivedNakayama.integerRing ell d.E) (𝟙 d.X.left)
      d.M (lisse_finiteModel _ d.X.left d.M d.lisse)⟩

/-- The degree-zero lattice is bounded constructible before compact support.
Source: the constructible input in the lattice paragraph, range step 7
(blueprint: def-zl-curve-lattice-compact-data).
A sheaf in degree zero is bounded; its only nonzero cohomology is the sheaf itself.
Apply the existing single-degree constructibility lemma to the preceding local models. -/
theorem boundedConstructible :
    constantModelBoundedConstructible (DerivedNakayama.integerRing ell d.E) d.X.left
      ((DerivedCategory.singleFunctor _ 0).obj d.M) := by
  exact single_constructible (DerivedNakayama.integerRing ell d.E) d.X.left d.M
    d.constructible

/-- The lisse lattice in degree zero has Tor amplitude [0,0].
Source: local freeness in the lattice paragraph, range step 4
(blueprint: def-zl-curve-lattice-compact-data).
The coefficient-heart lisse cover is the ordinary local-freeness cover after the
Cartesian coefficient identification. Locally free modules are flat, and a flat
module in degree zero has Tor amplitude [0,0] against every module. -/
theorem torAmplitudeZero :
    DerivedCategory.torAmplitudeIn _ 0 0
      ((DerivedCategory.singleFunctor _ 0).obj d.M) := by
  have hfree : IsLocallyFree
      (condensedRingObj (DerivedNakayama.integerRing ell d.E) d.X.left) d.M :=
    (isLocallyFree_iff d.M).mpr d.lisse
  exact DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hfree.flat

variable [IsAlgClosed k]

/-- The scalar ring is the actual terminal sections of the integral condensed ring.
Source: the point realization in the lattice paragraph
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev scalarRing := condensedScalarRing (DerivedNakayama.integerRing ell d.E)

/-- Integral compact support followed by exact point sections.
Source: the definition of M in the lattice paragraph
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev compactFunctor :=
  CondensedRing.rightDerivedLowerShriekOfCompactification
      (DerivedNakayama.integerRing ell d.E) d.compactification ⋙
    (CondensedRing.CohomologyTransport.sections
      (DerivedNakayama.integerRing ell d.E) (Spec (.of k))).mapDerivedCategory

/-- The actual compact-support complex of the integral lattice, before rationalization.
Source: M = RΓ_c(U,L_0) in the lattice paragraph
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev integralComplex := d.compactFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj d.M)

/-- Forget only the scalar action, through the exact ordinary-module forgetful functor.
Source: evaluation before the Milnor argument
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev forgetScalars := forget₂ (ModuleCat.{u + 1} d.scalarRing) Ab.{u + 1}

/-- Fix the module and abelian universes before specializing colimit preservation.
Source: exact ordinary scalar forgetting
(blueprint: def-zl-curve-lattice-compact-data). -/
instance forgetScalars_finiteColimits : PreservesFiniteColimits d.forgetScalars where
  preservesFiniteColimits J :=
    ModuleCat.forget₂PreservesColimitsOfShape.{u + 1, u + 1, 0, 0}
      (J := J) (R := d.scalarRing)

/-- The same integral compact-support object in D(Ab).
Source: P_X in step 7 of the range node
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev abelianComplex : DerivedCategory Ab.{u + 1} :=
  d.forgetScalars.mapDerivedCategory.obj d.integralComplex

/-- Exact scalar forgetting detects zero homology.
Source: pass from the abelian Milnor calculation back to integral modules
(blueprint: def-zl-curve-lattice-compact-data).
The exact-functor homology comparison identifies underlying homology groups;
a module whose underlying additive group is zero is itself zero. -/
theorem homology_isZero_of_forget (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj d.abelianComplex)) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} d.scalarRing) i).obj d.integralComplex) := by
  have h' := h.of_iso
    ((d.forgetScalars.mapDerivedCategoryHomologyFunctorIso i).app d.integralComplex)
  have : Subsingleton ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} d.scalarRing) i).obj d.integralComplex) :=
    AddCommGrpCat.subsingleton_of_isZero h'
  exact ModuleCat.isZero_of_subsingleton _

/-- Compact support of the canonical derived quotient tower, still with its integral action.
Source: reduction modulo successive uniformizer powers and its quotient transitions
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev reductionTower :=
  AdicCompletion.derivedTower ell d.E d.X.left
      ((DerivedCategory.singleFunctor _ 0).obj d.M) ⋙ d.compactFunctor

/-- The finite-level compact-support tower in D(Ab), with quotient-induced transitions.
Source: K_n in steps 5--8 of the range node
(blueprint: def-zl-curve-lattice-compact-data). -/
abbrev abelianTower : ℕᵒᵖ ⥤ DerivedCategory Ab.{u + 1} :=
  d.reductionTower ⋙ d.forgetScalars.mapDerivedCategory

end LatticePiece
end WeilConjectures.AffineCurveRange
