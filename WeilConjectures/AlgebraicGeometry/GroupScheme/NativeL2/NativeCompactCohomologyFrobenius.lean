/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.CompactTransport.NativeCompactFrobeniusTransport

/-!
# Compact cohomology and Frobenius of native Weil modules

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-mixedness-for-a-relative-affine-curve/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.md, the cohomology and Frobenius in the conclusion
(blueprint: def-zl-condensed-compact-cohomology-frobenius).

All data come from the actual compactification, condensed lower shriek, point insertion,
proper/open exchange and the input Weil isomorphism. No duality or purity is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.NativeCompactTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeL2
open CompactTransport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The actual compact-support complex on the geometric point, before coefficient sections.
Source: latest blueprint, R a_! of the underlying degree-zero module
(blueprint: def-zl-condensed-compact-cohomology-frobenius). -/
abbrev compactComplex (c₀ : Compactification X₀.hom) (M : WeilModule D l X₀) :=
  (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
    (compactBase D X₀ c₀)).obj ((DerivedCategory.singleFunctor _ 0).obj M.carrier)

/-- Canonical compact Frobenius: point insertion, the proper/open mates and the Weil map.
Source: latest blueprint, geometric Frobenius on compact support
(blueprint: def-zl-condensed-compact-cohomology-frobenius). -/
@[irreducible] def compactOperator (c₀ : Compactification X₀.hom)
    (M : WeilModule D l X₀) : End (compactComplex D l X₀ c₀ M) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (derivedPointInsertion l D.k (NativeCondensedModule.frobeniusPointIso D).hom
    (𝟭 _)).hom.app _ ≫
    (constantExtensionCompactExchange (Profinite.padicAlgClRingObj l)
      (compactBase D X₀ c₀) (D.geometricFrobenius X₀)
      (D.geometricFrobenius (compactModel D X₀ c₀))
      (NativeCondensedModule.frobeniusPointIso D)
      (compactOpenSquare D X₀ c₀) (compactProperSquare D X₀ c₀)).app _ ≫
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
      (compactBase D X₀ c₀)).map
        (derivedTheta l (D.geometricFrobenius X₀).hom M.carrier M.str).hom

end WeilConjectures.NativeL2
