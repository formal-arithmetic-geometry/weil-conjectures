/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerRationalTraceDefs

/-! # Ordinary traces under extension from E to Qbar
Source: the reviewed Euler-product proof Step 3.
(blueprint: lem-condensed-weil-euler-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open NativeCondensedModule

/-- One extended strict pair compares all global powers and all rational local traces.
Source: thm-trf-l-function-euler-product, reviewed proof Step 9 (blueprint Step 3).
Proof: extend the actual strict pair by the derived condensed E-to-Qbar coefficient
functor, with Weil map T(theta) after the inverse canonical scalar/pullback comparison.
Scalar-six stability and field-coefficient ctf=bc make this pair bounded constructible.
The strict-Weil cohomology scalar comparison identifies compact cohomology tensored
with Qbar with that of the extended pair, intertwining global Frobenius and hence every
power. At each rational geometric lift, its stalk comparison intertwines the specified
m-fold semilinear returns. This includes the point reparametrization, as established
before biduality by the canonical tensor-section normalization and proper/open mates.
Choose a finite E-basis in each degree, extend the basis to Qbar, and write the
intertwining operators as conjugate matrices. Their diagonal sums are related by the
inclusion E to Qbar, since trace is invariant under conjugation and extension of
scalars. Constant-section ring identifications give precisely the ordinary scalar
traces below. Zero groups, negative degrees, empty schemes and m=1 are included.
(blueprint: lem-condensed-weil-euler-scalar-extension). -/
theorem eulerScalarExtensionTraces
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (E : PadicAlgCl.FiniteIntermediateField ell)
    (K : strictWeilComplexCategory D ell hEll X₀ (.finite E))
    (c₀ : Compactification (D.geometricFiber X₀).hom) :
    ∃ KΩ : strictWeilComplexCategory D ell hEll X₀ .qbar,
      (∀ m j, E.1.subtype (eulerCompactTrace D X₀ ell hEll (.finite E) K c₀ m j) =
        eulerCompactTrace D X₀ ell hEll .qbar KΩ c₀ m j) ∧
      (∀ (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
        (hv : scalarLocalReturn D X₀ (eulerExtensionPoint D X₀ m hm y) m) (j : ℤ),
        E.1.subtype (eulerPointTrace D X₀ ell hEll (.finite E) K
          (eulerExtensionPoint D X₀ m hm y) m hv j) =
        eulerPointTrace D X₀ ell hEll .qbar KΩ
          (eulerExtensionPoint D X₀ m hm y) m hv j) := by
  sorry

end WeilConjectures.CondensedWeilEuler
