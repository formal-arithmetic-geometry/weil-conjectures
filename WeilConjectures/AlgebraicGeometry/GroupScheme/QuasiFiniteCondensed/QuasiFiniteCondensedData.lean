/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartGeneralStatement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Expressions of the quasi-finite condensed direct-image theorem

The ambient strict Weil pairs, their canonical Weil cohomology and the compact-support
image of lem-zl-quasi-finite, in a module of their own so that the subclaim modules and
the item module `Sheaf.DeligneLaumon.QuasiFiniteCondensed` (which re-exports this module)
share them without an import cycle
(blueprint: def-zl-quasi-finite-auxiliary-expressions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.QuasiFiniteCondensed

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Ambient strict pairs, before imposing bounded constructibility on the carrier.
Source: sk-def-sf-weil-complexes, the displayed Weil isomorphism
(blueprint: lem-zl-quasi-finite). -/
abbrev _root_.WeilConjectures.QuasiFiniteCondensed.AmbientPair :=
  CategoryTheory.Endofunctor.IsoAlgebra
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom).mapDerivedCategory

/-- Canonical Weil cohomology, using the exact Frobenius/cohomology comparison.
Source: def-weil-complex-weights, upper-weight display
(blueprint: lem-zl-quasi-finite). -/
def _root_.WeilConjectures.QuasiFiniteCondensed.cohomology
    (K : AmbientPair D l X₀) (b : ℤ) : NativeL2.WeilModule D l X₀ :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategoryHomologyFunctorIso b)).obj K

variable {X₀}
  {Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Compact-support direct image with the canonical proper/open Frobenius exchange.
The compactification presents the operation, rather than supplying an arbitrary map.
Source: lem-zl-quasi-finite.proof.md, opening factorization and composition
(blueprint: lem-zl-quasi-finite). -/
def _root_.WeilConjectures.QuasiFiniteCondensed.image
    (g₀ : X₀ ⟶ Y₀) (c₀ : Compactification g₀.left)
    (K : AmbientPair D l X₀) : AmbientPair D l Y₀ :=
  (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    (RelativeCurve.exchange D l g₀ c₀)).obj K

end WeilConjectures.QuasiFiniteCondensed
