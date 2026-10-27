## What changed

Replaced the body of `AlgebraicGeometry.PGLLinearization.projective_pgl_stable_quotient`
with a compiling proof from three separate geometric inputs and the existing
`finite_graded_proj_projective`. Its signature and the existing closure definitions
are unchanged.

The proof constructs the open immersion from J into its scheme-theoretic image,
identifies its geometric points with the restricted semistable locus, and transfers
closed orbits and finite stabilizers by cancellation of the closed immersion.
It converts the invariant finite-type algebra into the specified ambient-subring
finite-generation condition. An explicit identity comparison between the additive
and k-submodule gradings transfers the finite graded Proj theorem, including its
projective embedding and every divisible Veronese. Finally it transfers the glued
quotient's invariance, universality for algebraic spaces, and orbit bijection from
the restricted action to the original action.

Added `PGLInvariantSectionFiniteness`, with a complete proof from the projective
section-algebra theorem, the reductive invariant finite-generation theorem, and
`PGLSectionAffineAction`. It constructs the coefficient map by degree-zero
projection and proves coefficient finiteness using an injective linear map into
the actual degree-zero section space. It explicitly compares tensor-formula and
ordinary pullbacks when extracting the polarization.

The three remaining geometric constructions are separately stated in new modules,
with sources, full proof descriptions, and DAG nodes. No data definitions with
postponed construction proofs were added. No source-library module was edited.
Single-file compiles succeeded for the original module and each developed helper;
the complete sandbox compile passed: image restriction 4.2 s, section action
0.2 s, quotient gluing 2.4 s, finiteness 11.3 s, and the item 18.9 s.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.PGLLinearization.projective_pgl_stable_quotient` by decomposition.
The item module has zero remaining holes. This is a decomposition, not a complete
axiom-free proof of the geometric quotient theorem.

Also proved
`AlgebraicGeometry.PGLLinearization.invariant_section_finiteness`
(node `lem-sfb-pgl-invariant-section-finiteness`). Private helpers
`coefficient_proj`, `finiteGeneration`, and `stable_restriction` are fully proved.

Added exactly three holes, each the whole proof of its named public theorem:

- `AlgebraicGeometry.PGLLinearization.invariant_image_restriction`
  (`lem-sfb-pgl-invariant-image-restriction`): restricting the action and comparing
  semistability along an invariant scheme-theoretic image.
- `AlgebraicGeometry.PGLLinearization.section_affine_action`
  (`lem-sfb-pgl-section-affine-action`): the degree-preserving affine action on the
  section ring and identification of its fixed subring.
- `AlgebraicGeometry.PGLLinearization.semistable_affine_quotient_gluing`
  (`lem-sfb-pgl-semistable-affine-quotient-gluing`): affine invariant localization,
  chart assembly, categorical descent, and the geometric orbit bijection.

Thus one original hole is closed and three holes are added; the packet is a net
increase of two holes before closure accounting of already-existing dependencies.
Existing imported theorems retain their own holes. No private theorem or definition
contains `sorry`.

## No longer needed

No original dependency is pruned: the original density, projective section-algebra,
reductivity, finite graded Proj and affine finite-stabilizer quotient inputs all
remain needed by the implemented argument or one of its separate remaining steps.
There are no withdrawn modules. The parent now imports the geometric inputs through
the new interfaces; this does not make their mathematical dependencies unnecessary.

Removed unused proof imports from the new statement-only image-restriction and
quotient-gluing modules. Their DAG plans retain the needed dependency records.
No existing public import was removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original ten-step plan does not provide the induced affine action on the full
section algebra as a Lean declaration. `PGLGeometricReductivity` expects an
`AffinePGL.Action`, whereas `PGLLinearizedPolarization.Action` supplies pointwise
scheme actions and line isomorphisms. The missing construction requires flat base
change, pullback coherence and comparison of homogeneous fixed sections. It is now
stated as a separate mathematical lemma rather than assumed by applying the
finite-generation theorem to an unspecified action.

The plan also treated image restriction/semistability comparison and invariant
localization/chart gluing as prose steps. Their exact interfaces are now explicit.
They are genuine parts of the argument: neither new theorem has all of the original
hypotheses and conclusion. The gluing theorem has no closure construction, invariant
finite-generation conclusion, projectivity conclusion or Veronese conclusion.

The edge cases checked in formulating these interfaces include empty schemes, the
zero section ring, nonreduced schemes, positive characteristic, rank one, degree-zero
constants larger than k, zero-divisor denominators, and algebraic-space targets
without separation assumptions. No counterexample or statement weakening was used.
The unit route is preserved. No definition, statement, attribute, or public import
in the adopted source tree was changed.

## New nodes

`lem-sfb-pgl-invariant-image-restriction` is the action-restriction and semistability
comparison portion of original steps 1--3. Its statement allows any closed immersion
with the image kernel, avoiding expensive concrete image unfolding in the interface.

`lem-sfb-pgl-section-affine-action` is the induced section-ring action needed before
applying the stated reductive invariant theorem. It has no finite-generation or
quotient conclusion.

`lem-sfb-pgl-invariant-section-finiteness` is proved. It isolates the algebraic
finiteness portion of step 4 with the actual structural coefficient map.

`lem-sfb-pgl-semistable-affine-quotient-gluing` is steps 5--10, taking an already
identified stable semistable open and returning its geometric quotient, without
asserting projectivity. Its docstring includes the zero-divisor-safe localization
argument. The proof-scope change is documented in
`coord/changes/projective-pgl-private-proof-sections.md`, as requested by preflight.
Existing signatures and definitions stay unchanged; there are no forced adaptations.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
