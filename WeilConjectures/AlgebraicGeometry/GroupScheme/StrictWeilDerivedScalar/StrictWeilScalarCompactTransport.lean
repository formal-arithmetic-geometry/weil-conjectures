/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.StrictWeilDerivedScalar.StrictWeilScalarLocalCompatibility
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius


/-! # Scalar compatibility of the compact Frobenius transport

Source: prop-every-iterate-trace.proof.md, scalar descent, steps 5--7 of the derived comparison.
(blueprint: lem-zl-strict-weil-scalar-compact-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
open scoped CategoryTheory.Obj
namespace WeilConjectures.StrictWeilDerivedScalar

local instance (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The recorded global endomorphism factors through its specified compact first arrow.
Source: def-weil-global-geometric-frobenius, its defining composite
(blueprint: lem-zl-strict-weil-scalar-compact-transport). -/
theorem global_compact_factorization (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : strictWeilComplexCategory D ell hEll Y₀ c) :
    (GlobalGeometricFrobenius.globalGeometricFrobenius D ell hEll Y₀ c c₀ K).2 =
      compactTransport D ell hEll Y₀ c c₀ K.obj.carrier K.property ≫
        (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₀).map K.obj.str.hom := by
  simp only [GlobalGeometricFrobenius.globalGeometricFrobenius, compactTransport,
    Iso.trans_hom, Functor.map_comp, Category.assoc]
  rfl

/-- The specified compact first arrow commutes with scalar extension, before any Weil
structure is applied. The right side includes the inverse scalar/pullback comparison.
Source: derived scalar comparison, steps 5--7, expanding the scalar-descent sentence
of latest prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-scalar-compact-transport).

Proof: choose a Nagata compactification over k₀ and base change to k. The Frobenius acts
on the open/proper diagram. The normalized inverse-image tensor comparison takes a
section m tensor c to its inverse image tensor the same constant c. Consequently the
point scalar isomorphism intertwines the two point insertions. Compute this square on
flat-term K-flat representatives and descend using exact sections and exact field
extension. For the proper square use the unrestricted direct-image scalar/exchange
identity, at the open extension of K. For the open square take adjunction mates of the
pullback composition square; unit and counit triangles cancel. Paste these two squares
with the point insertion square. The refinement unit normalizations identify the result
with the compactTransport defined above on the chosen compactification, and transport
it to the arbitrary c₀. The final endpoint is exact native pullback, so the inverse of
pullComparison appears on the right. No Weil structure, trace or cohomology is used. -/
theorem compactTransport_scalar (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c₀ : Compactification (D.geometricFiber Y₀).hom)
    (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E)
      (D.geometricFiber Y₀).left)
    (hK : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E) (D.geometricFiber Y₀).left) K)
    (hT : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber Y₀).left)
      ((change ell E (D.geometricFiber Y₀).left).obj K)) :
    (scalarChange ell E).map (compactTransport D ell hEll Y₀ (.finite E) c₀ K hK) ≫
        compactComparison D ell E c₀
          ((NativeCondensedDerived.pull (Profinite.continuousMapRingObj E)
            (D.geometricFrobenius Y₀).hom).obj K) =
      compactComparison D ell E c₀ K ≫
        compactTransport D ell hEll Y₀ .qbar c₀
          ((change ell E (D.geometricFiber Y₀).left).obj K) hT ≫
        (condensedRingCompactCoefficientComplex (Profinite.padicAlgClRingObj ell) c₀).map
          ((pullComparison ell E (D.geometricFrobenius Y₀).hom).inv.app K) := by
  sorry

end WeilConjectures.StrictWeilDerivedScalar
