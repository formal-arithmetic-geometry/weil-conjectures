/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GeometricFrobeniusTransport.GeometricFrobeniusCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Global geometric Frobenius

Source: latest blueprint, `def-weil-global-geometric-frobenius`, order 3387;
the two displayed composites and the final cohomology sentence
(blueprint: def-weil-global-geometric-frobenius).

The operators below are the canonical condensed-coefficient transports followed by the
Weil structure.  Compact support uses the canonical normalized compactification data from
the condensed transport theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures

namespace GlobalGeometricFrobenius

/-- The two displayed endomorphisms of coefficient complexes for a strict Weil pair.
`c₀` presents the recorded compact-support functor; it is an arbitrary compactification
of the geometric structure map. Ordinary transport is insertion along Spec(γ) followed
by the adjunction-mate exchange. Compact transport uses the normalized proper/open
exchange and the comparison back to `c₀`. The exact-derived pullback comparison converts
the pair's termwise structure into the specified `Lg_Y^*` structure. Compose the resulting
transport with RΓ(θ), respectively RΓ_c(θ), in exactly that order.
Source: latest blueprint, def-weil-global-geometric-frobenius, both displayed composites
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : strictWeilComplexCategory D ell hEll Y₀ c) :
    End ((condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).hom).obj K.obj.carrier) ×
      End ((condensedRingCompactCoefficientComplex (WeilCoefficient.ab c)
        c₀).obj K.obj.carrier) := by
  let g := (D.geometricFrobenius Y₀).hom
  let a := (D.geometricFiber Y₀).hom
  let M := K.obj.carrier
  let θ := (leftDerivedUpperStarIsoMapDerivedCategory (WeilCoefficient.ab c) g).app M ≪≫
    K.obj.str
  let t₀ := GeometricFrobeniusTransport.ordinaryTransport D ell Y₀ c M
  let hM : boundedConstructible (condensedRingObj (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).left) ((CohomologyTransport.L (WeilCoefficient.ab c) g).obj M) :=
    GeometricFrobeniusTransport.FrobeniusTransportLaws.pull_constructible
      (GeometricFrobeniusTransport.geometricFrobeniusCohomologyTransport D ell hEll Y₀ c)
      ⟨M, K.property⟩
  let tc₀ := GeometricFrobeniusTransport.compactTransport D ell hEll Y₀ c c₀ c₀
    ⟨M, K.property⟩ hM
  exact ⟨t₀ ≫ (condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c) a).map θ.hom,
    tc₀ ≫ (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₀).map θ.hom⟩

/-- Apply ordinary derived homology to the two specified endomorphisms in every integer
 degree, giving the actions denoted F on H^i and H_c^i.
Source: latest blueprint, def-weil-global-geometric-frobenius, final sentence
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobeniusOnCohomology (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : strictWeilComplexCategory D ell hEll Y₀ c) (i : ℤ) :=
  ((DerivedCategory.homologyFunctor _ i).map
      (globalGeometricFrobenius D ell hEll Y₀ c c₀ K).1,
    (DerivedCategory.homologyFunctor _ i).map
      (globalGeometricFrobenius D ell hEll Y₀ c c₀ K).2)

/-- For a derived Weil complex use its recorded realization (For K, θ_K).
This uses the termwise-derived forgetful functor, with no identification of the derived
Weil category with the strict-pair category.
Source: latest blueprint, def-weil-global-geometric-frobenius, For(K) and θ_K paragraph
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobeniusOfWeilComplex (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : weilComplexCategory D ell hEll Y₀ c) :=
  globalGeometricFrobenius D ell hEll Y₀ c c₀
    ((weilComplexRealization D ell hEll Y₀ c).obj K)

/-- The ordinary and compact cohomology actions of a derived Weil complex, in any degree.
Source: latest blueprint, def-weil-global-geometric-frobenius, For(K) and final sentence
(blueprint: def-weil-global-geometric-frobenius). -/
def globalGeometricFrobeniusOfWeilComplexOnCohomology (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : weilComplexCategory D ell hEll Y₀ c) (i : ℤ) :=
  globalGeometricFrobeniusOnCohomology D ell hEll Y₀ c c₀
    ((weilComplexRealization D ell hEll Y₀ c).obj K) i

end GlobalGeometricFrobenius

end WeilConjectures
