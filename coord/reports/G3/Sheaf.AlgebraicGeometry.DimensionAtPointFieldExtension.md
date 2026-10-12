## What changed

Closed the single hole in `AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension` without changing its signature. The new fully proved helper `AlgebraicGeometry.polynomial_presentation_height_field_extension` constructs the scalar-extended polynomial surjection and compares the four prime heights using isomorphic fibre quotients and Mathlib's flat height formula. Private proved helpers transport local dimension across homeomorphisms and the polynomial-quotient formula across arbitrary surjections. Updated the DAG proof to this route. Both delivered modules compile without warnings.

## Proved and sorry left

Closed `AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension` (1 of 1 original holes). Added no holes: `AlgebraicGeometry.polynomial_presentation_height_field_extension` and every private helper are fully proved. The proof still depends on the existing holed theorem `AlgebraicGeometry.topologicalKrullDimAt_polynomial_quotient_eq_height_difference` in its original module; that existing dependency is unchanged.

## No longer needed

No original module import removed and no existing module pruned. Removed redundant proof imports
`Mathlib.RingTheory.Ideal.GoingDown` and `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` from the new
helper: `Mathlib.RingTheory.RingHom.Flat` already supplies going-down and tensor flatness.

Old target proof dependencies no longer used directly (all removed from its `proof_deps`):
`lem-weil-pbc-polynomial-ring-field-regular-ring`, `def-weil-pbc-noetherian-ring`,
`lem-weil-pbc-presentation-base-change`, `lem-weil-pbc-finite-type-algebra-noetherian`,
`def-pc-field-extension`, `lem-weil-pbc-field-extension-base-change-faithfully-flat`,
`def-weil-pbc-faithfully-flat-ring-map`, `def-weil-pbc-flat-ring-map`,
`lem-weil-pbc-flat-height-formula`, `def-weil-affine-spectrum`, and
`def-kun-topological-dimension-at-point`.
The polynomial Noetherianity, finite-type Noetherianity, and flat height formula ingredients
remain recorded on the new helper and are supplied by Mathlib instances/theorems.
The presentation-base-change theorem is replaced by tensor-map surjectivity and `rTensor_ker`;
faithful flatness is replaced by tensor flatness. Spectrum and local-dimension definitions
remain in the target's statement imports; their nodes are statement dependencies, not invoked
proof lemmas. None of these changes claims that a module has left the target import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the plan. The plan did not expose the existing Mathlib tensor-product kernel formula; using it avoids choosing generators. The local copy of literature/stacks-project/algebra.tex is absent, so the cited proof was read from https://stacks.math.columbia.edu/tag/00P4. The new statement was checked at n=0, S=0 (no primes), and the identity extension. Its addition form avoids cancellation of infinite heights. The unit's realized statement and steps are preserved.

## New nodes

`lem-weil-pbc-polynomial-presentation-height-field-extension`, in `Sheaf.RingTheory.PolynomialPresentationHeightFieldExtension`, is a proved algebraic part of the original argument, not a new hole. Searches ran through msearch: LeanSearch returned Internal Server Error (recorded unavailable); Loogle and grep found no matching combined statement. The component lemmas were read in Mathlib and used in the proof. No change records needed: existing statements and definitions are unchanged.

## Second reading by G3

1. Compared the target module with the repository version before delivery: the existing
   theorem signature and docstring are byte for byte unchanged. Only proved private helpers,
   its proof, and a plain proof import were added; no definition or target changed.
2. Both modules compile without warnings through lcompile. No delivered declaration contains
   sorry or any forbidden construct. Scratch `#print axioms` shows only propext,
   Classical.choice, Quot.sound for the new public helper; the target additionally has sorryAx
   from the pre-existing polynomial-quotient dimension formula. The delivery probe checks all
   declarations. Every ring map and equivalence is explicitly constructed from proved results;
   no arbitrary data is chosen from an unproved existence theorem.
3. No holed statement is split off. Read the proved algebraic helper and its flat-square proof:
   quotient ideals correspond by surjectivity and the kernel equality, their prime heights
   correspond by a ring equivalence, and the two flat height formulas give the cross sum.
   At n=0 a surjective algebra map from k forces S=k or the zero ring; the latter has no primes.
   Identity extensions and arbitrary polynomial quotients satisfy the same formula, and the
   additive form needs no cancellation of infinite heights. Independent LeanFinder, Loogle,
   msearch grep and rg searches found the component height lemmas used, not a shorter combined
   result or an existing local-dimension homeomorphism lemma. The helper is strictly the
   algebraic part, not a restatement of local topological dimension invariance.
4. The proof takes the presentation, Mathlib flat height formula and existing quotient-dimension
   route from Tag 00P4, checked against its online proof. The local-dimension helper transports
   the original formula, and bounded natural heights justify the final omega step.
   Read sk-thm-p1's realized statement/steps: none is bypassed or edited. Corrected the report's
   incomplete old-dependency list and removed two redundant new-module imports. No module pruned.
5. Read both DAG nodes against the code. Corrected the new node's informal statement to the
   actual existential conclusion (the constructed map is scalar extension, but the theorem
   does not assert that extra property). Updated its proof dependencies to the actual Mathlib
   route: tensor exactness instead of presentation baseChange, flatness instead of faithful
   flatness; retained the Noetherianity and height ingredients. Added independent search evidence.

Second reading changed only redundant proof imports, the new node's explanatory statement and
proof metadata, and the report. No Lean signature, definition, or proof body changed.
