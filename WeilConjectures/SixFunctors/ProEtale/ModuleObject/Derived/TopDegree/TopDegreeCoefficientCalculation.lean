/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs

/-! # The constant unit and top trace after the finite section calculation

Source: sk-cor-trace, steps 2--6.
(blueprint: lem-pd-constant-unit-and-top-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The constant unit and top trace after the finite section calculation.
Source: sk-cor-trace, steps 2--6 (blueprint: lem-pd-constant-unit-and-top-trace).

Proof in words.
Apply constant_cohomology_bounds and sk-lem-finite to the regular coefficient unit.
This gives the sharp interval and finite cohomology over finite coefficients.
The assembly supplies the actual finite constant-section bijection as a proved
input, by connected_finite_constant_sections at the terminal pro-etale object.
This finite underived input is strictly smaller than the remaining assertion over
all coefficient constructors. Identify the
regular module with the constant sheaf through the actual finite encoding, then use
full faithfulness of the degree-zero embedding. Its comparison on the section 1 is
tracePullUnit, so unitSection_bijective_of_pull gives the specified map on the point.
For the cyclic coefficient ring use coefficient_frobenius and the degree-zero
cohomology of condensed_sf_identification at the regular unit. Self-injectivity kills
higher dual Ext, and the counit normalization identifies evaluation at 1 with the
specified twisted trace. For any finite ring use its Z/ell^n-algebra structure and
exists_topDegreeScalarIso; use the canonical scalar-six maps on complexes and their
counits. No flatness of this ring map is required. At O_E use the actual epimorphic
constant-sheaf tower and continuousCohomology_limit. Finite cohomology at each level
kills the preceding-degree first derived limit via continuousCohomology_milnor.
The normalized finite trace maps induce the integral trace: this follows from
compatibility of the construction and its adjunction, rather than detection of an
arbitrary equality by finite reductions. Reconstruct O_E using adic completeness.
Localize to E and use flat finite-extension/closure maps; the bounded perfect models
make flat cohomology change canonical. The point root line is free of rank one;
use compatible roots to perform the computation and inverse-line cancellation to
remove their choice. This yields the actual untwisted trace with values in Value.
-/
theorem constant_unit_and_top_trace {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (hfinite : ∀ (A : Type (u + 1)) [CommRing A] [Finite A]
      [TopologicalSpace A] [DiscreteTopology A],
      Function.Bijective
        ((toSheafify (Scheme.ProEt.topology X.left)
          ((Functor.const X.left.ProEtᵒᵖ).obj (RingCat.of A))).app
            (Opposite.op (Scheme.ProEt.mk (𝟙 X.left))))) :
    Function.Bijective
        (fun z : U ell c (Spec (.of k)) ⟶ U ell c (Spec (.of k)) ↦
          z ≫ unitSection ell c X) ∧
      Function.Bijective (trace ell c hEll X d) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
