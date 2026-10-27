## What changed

The assigned theorem `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_constructible`
retains its exact signature and both original public imports. Its proof now constructs
and uses the actual residue graded module, applies degreewise constructibility of a
finite constant tensor, applies the existing surjective scalar-restriction theorem,
and transports cohomology along the graded-layer comparison isomorphism.

`Sheaf.Paper.AdicGradedResidueTensorComparison` proves the algebraic part of the
argument: the kernel of the residue quotient annihilates the consecutive-power
kernel; the residue module is explicitly constructed using the quotient-module
action and the inverse kernel-quotient equivalence; its scalar action agrees with
the original action; restriction gives the original kernel module; and over a
Noetherian ring this residue module is finite. The finite-generation proof uses
the identity semilinear map from the finite ideal in the larger quotient, so no
presentation, generators or module witness are chosen from an unproved theorem.
Only the derived comparison remains a named theorem hole in that module.

`Sheaf.Paper.CoefficientConstructibleConstantTensor` constructs the exact constant
single complex and its tensor using the existing K-flat tensor. Its remaining
theorem is the general geometric tensor step, for an arbitrary bounded constructible
complex and an arbitrary finite module over one Noetherian coefficient ring.

Validation: all three modules compile without warnings through the required
single-file compiler. The constant-tensor module took 30.4 seconds; the final
residue-comparison module took 9.5 seconds; the assigned module took 29.8 seconds.
All are within the 60-second per-file limit. The existing node changes only in
`proof`, `proof_deps` and `proof_origin`; no target or existing signature changes.

The two new obligations are independent parts of the original argument. The
comparison has no constructibility, boundedness or Noetherianity hypothesis. The
constant-tensor assertion has no ideal, quotient tower, higher reduction, graded
kernel or change of coefficient ring. Neither restates the assigned theorem, and
the assigned proof combines them with the existing scalar-restriction theorem.

Sources read: the current integral-models unit and its Stacks comparison proof;
Stacks `proetale.tex`, Tag 09BR, `lemma-compare-truncations-constructible`, and Tag
09BQ, `lemma-tensor-c`; `sites-cohomology.tex`, Tag 094H,
`lemma-locally-constant-tensor-product`. The route retains the unit's integral-model
comparison and the original residue-tensor argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicFiniteGradedLayer_constructible`
(`lem-sfb-adic-graded-layer-constructibility`). There are zero holes left in the
assigned module. The algebraic theorems
`AlgebraicGeometry.Scheme.adicFiniteGradedModule_torsion`,
`AlgebraicGeometry.Scheme.adicFiniteResidueGradedModule_smul`, and
`AlgebraicGeometry.Scheme.adicFiniteResidueGradedModule_finite`, and the constructed
`AlgebraicGeometry.Scheme.adicFiniteResidueGradedModule_restrictIso`, have complete proofs.

Added exactly two named theorem holes, each in its own new module:

- `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_residueTensor`
  (`lem-sfb-adic-graded-residue-tensor-comparison`): the derived balancing
  comparison for the explicit kernel module. Its algebraic input is proved.
- `AlgebraicGeometry.Scheme.coefficientConstructible_constantTensor`
  (`lem-sfb-coefficient-constructible-constant-tensor`): the common-strata and
  locally constant tensor argument for arbitrary finite constant modules.

This is a decomposition with one original hole closed and two holes added, not a
complete proof from the three permitted axioms. The existing imported theorem
`coefficientSurjectiveRestriction_constructible` is also still a separate project
obligation; this delivery does not change it. No definition contains a hole.

## No longer needed

No original import is removed, no existing module is withdrawn, and no globally
unreachable module is claimed. The filtration triangle theorem
`adicFiniteGradedLayer_triangle` is not needed to prove constructibility of its
first term. Its module `Sheaf.Paper.AdicCoefficientFiltration` remains necessary
for the actual kernel and layer definitions.

The assigned node no longer directly cites
`lem-pur-derived-change-of-rings`,
`lem-sfb-adic-finite-stratification-pullback`,
`def-weil-pbc-proetale-operations`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, or
`lem-weil-pbc-locally-constant-tensor`. The geometric dependencies are retained in
the constant-tensor node's proof plan. The balancing node instead names the existing
independent-coefficient K-flat extension and tensor-cancellation declarations,
together with the existing actual reduction data and constant realization. The
ordinary-module change-of-rings theorem is not imported speculatively: its signature
does not supply the needed sheaf comparison. No claim is made that its module is
unused elsewhere or absent from transitive public imports.

## Where the brief, the DAG or earlier work was wrong

The original mathematical statement is unchanged. The broad plan is valid, but
the declaration attached to `lem-pur-derived-change-of-rings` is the
ordinary-module universal pair and does not itself expose the required
independent-coefficient sheaf balancing isomorphism. Likewise the local tensor
theorem is formulated for locally constant sheaves on a site, rather than the
affine-local coefficient constructibility predicate in this item. The two named
interfaces isolate these separate gaps; the finite residue action and its finite
generation are now explicit and proved rather than left in the prose.

Edge cases checked in the statements and constructions: J=0 makes the consecutive
kernel zero; J=top makes the quotient rings zero; the zero ring and empty scheme
are allowed; a zero finite module tensors to zero. A nonflat module over a singular
Noetherian ring can give infinitely many negative tensor cohomology degrees, so
neither new theorem asserts boundedness below, finite Tor dimension or bounded
higher reductions. The scalar restriction map goes from the larger quotient to
the residue quotient and is surjective in all these cases.

Mathlib searches ran through the logged search tool with LeanFinder, Loogle, grep
and LeanSearch. They found ideal-quotient surjectivity, quotient-module actions,
finite semilinear images and ordinary tensor tower identities, but no exact
constructible sheaf theorem or derived graded-layer comparison. Existing library
finite-tensor theorems impose finite coefficient rings; flat tensor results impose
flatness. These hypotheses are not available here. Blueprint text searches for
constant tensor and graded residue found no matching imported blueprint node;
this delivery serves the same recorded Stacks tensor step of the integral-models
unit.

## New nodes

`lem-sfb-adic-graded-residue-tensor-comparison` records the explicit residue module,
its proved annihilation and finite generation, and the remaining unbounded derived
comparison. Its module is `Sheaf.Paper.AdicGradedResidueTensorComparison`. The
comparison statement is independent of the constructibility hypothesis.

`lem-sfb-coefficient-constructible-constant-tensor` records the exact constant
single/tensor constructions and the geometric degreewise constructibility step.
Its module is `Sheaf.Paper.CoefficientConstructibleConstantTensor`. The source is
the common-stratification application of Tag 094H within the Tag 09BR argument.

No existing statement or shared definition is changed, so no change record or
consumer adaptation is required.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
