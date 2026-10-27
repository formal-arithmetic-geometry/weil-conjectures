## What changed

Replaced the proof hole in `supported_image_koszul_comparison_nonpositive` by a complete
assembly of two separate geometric classicality steps, literal two-term bounds, a proved
bounded abelian comparison counit, and exact faithful reflection of homology vanishing.
The statement and both existing definitions are unchanged. All new modules are under
`Sheaf.Paper`; no source-library file is changed.

`BoundedClassicalAbelianCounit.bounded_classical_abelian_counit` is proved. It works directly
with abelian sheaves: derive the comparison unit using injective acyclicity; use the triangle
identity on classical single complexes; use `PlusDevissage.isIso_app_of_bounded` on their
finite truncation triangles; then pass from D+ to the ordinary unbounded right derived
functor using the published compatibility isomorphisms. There is no new coefficient
encoding equivalence and no completion functor in this proof.

The remaining work is split along original steps 1--2 and 3--4. The first statement has no
support chain, pullback or derived direct image. The second is a preservation theorem for
an arbitrary module whose scalar-complex cohomology is already classical; it has no
Noetherian or local-model hypotheses and no comparison direct image. Neither is the
original conclusion with renamed hypotheses. The parent combines them with substantial
proved derived-category glue and proves both original conclusion clauses.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.supported_image_koszul_comparison_nonpositive`
(`lem-sfb-supported-image-koszul-comparison-nonpositive`). No sorry remains in the item.

New proved theorem:
`AlgebraicGeometry.ProEtale.bounded_classical_abelian_counit`
(`lem-sfb-bounded-classical-abelian-counit`).

Two new named holes remain, each the whole proof of its public theorem in its own module:

- `AlgebraicGeometry.ProEtale.integral_image_koszul_classical`
  (`lem-sfb-integral-image-koszul-classical`, `Sheaf.Paper.IntegralImageKoszulClassical`).
- `AlgebraicGeometry.ProEtale.support_pullback_koszul_classical`
  (`lem-sfb-support-pullback-koszul-classical`, `Sheaf.Paper.SupportPullbackKoszulClassical`).

This is a decomposition: one original hole closed, two added; net minus one hole before
pruning effects. It is not a claim that the geometric comparison theorem is sorry-free.
Every new hole has its source, a proof in words, and a matching node. No data is chosen
from a new unproved existence statement.

## No longer needed

Removed the following old private proof imports from the item:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Paper.NoetherianScalarConstructibleHeart`
- `Sheaf.Paper.FiniteModelSheafQuotientConstructible`
- `Sheaf.Paper.PrincipalReductionConeCalculus`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`

The source classicality dependencies (original steps 1--2) and support/pullback dependencies
(original steps 3--4) remain necessary in the respective new nodes; their removal from the
parent's imports is delegation of those exact proof steps, not a mathematical pruning claim.
The following nodes have been replaced in the parent's proof by the direct abelian counit
argument: `sk-prop-sf-comparison`, `det-pe-classical-derived-equivalence`, and
`sk-thm-pe-classical-sheaves`. Their module-valued interfaces are not used by the proved
assembly. Generic Grothendieck-valued unit, injective acyclicity and exact-functor cohomology
supply the required abelian interfaces instead. No existing module is withdrawn, and no
unit's realized route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original reviewed mathematical plan is retained. Its Lean interfaces need additional
glue: the finite-reduction results use ordinary module/coefficient model encodings, whereas
the literal Koszul comparison in the assigned theorem is abelian-valued. The two new
classicality statements specify the actual scalar differential and the required abelian
essential-image output. The independent proof of the counit avoids treating a module-valued
counit as definitionally an abelian-valued one.

The original Noetherian hypothesis is retained exactly. This delivery does not repair the
unrestricted parent's already-recorded obligation to establish it.

Edge cases: image of zero is the zero module; all displayed functors preserve zero.
Empty S gives only zero sheaves. The support theorem includes the root path, for which
extension is identity, arbitrary pullbacks, and n=0 (the identity differential, hence zero
cohomology). The integral-image theorem requires n>=1 as in the finite quotient result.
Torsion is allowed throughout. The literal complex has zero terms outside -1,0 independently
of any finiteness assumptions, and the parent proves those bounds from `isZero_double_X`.

## New nodes

`lem-sfb-integral-image-koszul-classical`: original steps 1--2, using Noetherian image
constructibility, finite quotients, principal reduction and constructible comparison. A new
item with one named sorry.

`lem-sfb-support-pullback-koszul-classical`: original steps 3--4, preservation under exact
support operations and arbitrary pullback. A new item with one named sorry.

`lem-sfb-bounded-classical-abelian-counit`: the bounded abelian specialization of original
step 5, with a complete Lean proof. The parent's updated proof uses this theorem, bounds
of the actual double complex, and exact faithful reflection. No change record is needed:
existing definitions, theorem signatures, attributes and public imports are untouched.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
