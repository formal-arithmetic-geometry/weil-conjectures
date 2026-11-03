/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFiniteExceptionalComparisonParts

/-! # Normalized geometric models for finite exceptional comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite coefficient models and normalized geometric compact-support comparison
exist before comparing their right adjoints or constructing the exceptional scalar square.

Source: latest blueprint, `sk-thm-sf-package.proof.md`, Clause (1), finite agreement
with the transported etale adjoint; the current node's steps 1--2 and scalar-coordinate
normalization (blueprint: lem-sf-finite-exceptional-geometric-models).

Proof:
1. The structure maps and the proper middle map make X, Y and c.Z qcqs and Noetherian.
For every finite ring A, take the normalized section-action encoding supplied by
moduleObject_ordinary_coefficient_equivalence. Restrict its derived equivalence to
localizing closures, using its stated localizing-image equality. Finite admissible
site comparison identifies the entire ordinary etale category with the ordinary
pro-etale localizing closure. Compose these equivalences. The counit of the restricted
encoding equivalence and the site comparison give the required site isomorphism.
The finite-Tor comparison and constructible descent identify the two small full
subcategories. Use the same encoding construction on the middle scheme.
2. For phi:A->B, form the identity-on-sections restriction comparison between these
encodings. It is a ring-linear natural isomorphism because both actions are by phi
on the same sections. Derive it and transpose under the actual scalar adjunctions.
The equivalences transport the adjunctions, so this left comparison is invertible
and satisfies encoding_unit by its defining transpose. The site restriction square
is finiteExceptionalDerivedSiteRestriction, whose inverse mate is the specified
finiteExceptionalSiteScalarMap. Paste the two restriction squares to obtain
comparison_normalization. Scalar extension preserves the localizing closure:
it preserves coproducts and triangles and sends each finite-Tor constructible
generator to such an object, by listedCoefficientCtf for the actual finite ring map.
This gives scalarSource and scalarTarget without assuming flatness.
3. Postcomposition of sections preserves coefficient identities and composition.
The inverse mates of the composite restriction squares equal the composites of their
inverse mates, by injectivity of the mate correspondence. Transposing the restriction
identity likewise fixes the scalar unit. This proves the two scalar coordinate
cocycles with exactly finiteExceptionalScalarComposition and finiteExceptionalTower.
4. The actual finite condensed ring is admissible. Brown existence gives its right
adjoint with both preservation certificates on the localizing closure. Compare its
chosen compactification with c, lift this comparison through the fully faithful
inclusion, and transport the adjunction along that left isomorphism. This supplies
M.brown for the specified c. The ordinary etale compact-support functor has a right
adjoint on the Noetherian schemes; choose that functor with its actual adjunction.
These choices form M. No comparison of right adjoints is asserted in this step.
5. Compose the normalized internal/fixed compact-support comparison with the finite
etale/pro-etale compact-support comparison for this same c. Lift through the full
localizing inclusions and cancel the site equivalences to obtain chi. On bounded-below
etale inputs the direct-image factor is the specified canonical site map, and the
open factor is the exact extension-by-zero comparison. Thus the composite is precisely
the displayed support_normalization equation, including the equivalence unit.
6. Take the canonical compactification comparison on each pair of boundary
compactifications. Its common-refinement equation gives compactification_refinement;
its identity and cocycle give the remaining two geometric laws. Package these data
as FiniteExceptionalGeometricComparisons M. Empty schemes and zero rings are included
because all constructions, restrictions and adjunctions retain their zero objects.
-/
theorem finiteExceptionalGeometricModels_exists
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hbase : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) :
    ∃ M : FiniteExceptionalModels ell c, Nonempty (FiniteExceptionalGeometricComparisons M) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
