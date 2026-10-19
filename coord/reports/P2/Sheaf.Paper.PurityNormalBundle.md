## What changed

Completed the three proof bodies in `Sheaf.Paper.PurityNormalBundle`, retaining all
existing public signatures and definitions. The proof of `zeroSection_spec` uses the
section identity in the over category and Mathlib's closed-immersion cancellation for
an affine projection. The proof of `regular_spec` transports the regular-sequence
conormal basis to the actual conormal stalks, proves finite local freeness and the
specified rank, and identifies the canonical comparison with the regular-sequence
polynomial map on every stalk. The proof of `vectorBundle_zeroSection` identifies the
two augmentations by the symmetric-algebra universal property and transports the
identity through the same relative-spectrum anti-equivalence used in `vectorBundle`.
All additional helpers are private and proved. In particular, ideal-equality transport
is handled before specializing to scheme stalks, and the polynomial bijectivity argument
is checked in a generic algebraic context. This avoids expensive unfolding of the chosen
sheaf-algebra presentation. No heartbeat or compile limit was raised. No definition or
statement repair and no consumer adaptation is needed.

## Proved and sorry left

Original holes replaced by proofs:

- `AlgebraicGeometry.PurityNormalBundle.zeroSection_spec`.
- `AlgebraicGeometry.PurityNormalBundle.regular_spec`.
- `AlgebraicGeometry.PurityNormalBundle.vectorBundle_zeroSection`.

Three original holes closed, zero holes added, zero split off, zero `sorry` occurrences
left in the delivered Lean module. Existing imported theorem dependencies remain
independent project items. Compiler and delivery validation are recorded by the tools.

## No longer needed

The affine-cover closed-immersion argument of
`lem-weil-pbc-closed-immersion-affine-cover-criterion` is replaced by
`IsClosedImmersion.of_comp`, since the projection is affine and the composite is the
identity. The module-stalk argument of `lem-weil-pbc-module-iso-on-stalks` is replaced
by `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` directly for commutative-ring
sheaves and reflection of isomorphisms by `Under.forget`. The separate use of
`lem-weil-pbc-symmetric-algebra-universal-property` to construct the chosen-basis
polynomial isomorphism is unnecessary: Mathlib's `SymmetricAlgebra.equivMvPolynomial`
already handles an arbitrary basis. The sheaf symmetric-algebra universal property
`lem-weil-pbc-quasi-coherent-symmetric-algebra-core` remains used for augmentations.

The following redundant proof imports were removed; each remains available through the
existing public providers where its declarations are needed:

- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
- `Mathlib.AlgebraicGeometry.Restrict`.
- `Mathlib.Topology.Sheaves.Functors`.
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`.

The obsolete `tool_uses` entries for the three bypassed nodes above are removed while
all remaining approvals retain their order. No unit statement or unit proof step is
bypassed. No module is withdrawn; these import removals do not claim that the modules
leave the targets' transitive closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The planned generic criteria admit the
shorter Mathlib applications described above. The stalk generator computation requires
representatives on inverse images of affine opens; these come from the existing
`AlgebraicGeometry.Scheme.Modules.affine_conormal_sections` theorem, together with
surjectivity of the cotangent quotient. The existing affine-conormal-sections node is
used as a general tool for local representatives, not as a replacement for a unit step;
its maintainer tool-use approval is requested in the independent review. No additional
mathematical result is assumed. The current blueprint's normal-cone clause and the
Stacks proofs of Tags 00LN, 0636, 0637 and 063M were read against these arguments.

The node `def-pur-normal-bundle` is now attached to the relative-Spec/Rees comparison
module `Sheaf.Paper.PurityNormalCone`; the module in this delivery still implements its
regular conormal-bundle and zero-section clauses. Its attachment is left unchanged.
The item module is also recorded in `pur9-def-normal-cone`; its actual relative-spectrum
construction remains unchanged. The original unit has no proof steps, and its normal
cone and regular vector-bundle assertions are retained.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
