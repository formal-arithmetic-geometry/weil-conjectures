## What changed

Proved `AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology` in the assigned module,
without changing its signature, public imports, definitions or existing docstrings.
The boundary embeds in the zero-dimensional complement supplied by
`exists_dense_irreducible_opens`. Pullback preserves constructibility and the proved
upstream finite-sheaf tool gives finite stalks over the finite coefficient ring.
The existing zero-dimensional cohomology theorem gives a finite product in degree zero
and vanishing in positive degrees. The Ext/derived comparison and finite edge map carry
both conclusions to the stated boundary sheaf on X. The DAG proof now records this route. The second reading removed three redundant
proof imports and corrected one elementary-step flag.

The source computation was checked at [Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA).
The local literature paths in the node are not present on this machine, so its online
primary source was read. Search used LeanFinder, Loogle, the required msearch grep,
and direct searches of Mathlib and both library roots. No direct theorem replaces this
boundary computation; the existing library ingredients suffice.

## Proved and sorry left

Proved the module's only original sorry:
`AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology`
(node `lem-pbc-g2-dense-open-boundary-cohomology`). No sorry remains in the delivered
module; no new declaration or sorry is added. Existing dependencies, especially
`zero_dimensional_etale_cohomology` and its remaining geometric computation, retain
whatever outstanding proofs they already have. This is a proof from existing named
statements, not a claim that the entire transitive target is axiom-free yet.

Local single-file compilation passed without warnings. The required delivery dry run
also checks compilation on the server and the declaration probe.
The proof makes no choice of a boundary point and handles empty X, U=X, and
zero-dimensional components through the same finite-product and inducing-map arguments.
The IsReduced assumption remains unchanged, although the proof does not need it.

## No longer needed

Removed these proof imports:
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.AlgClosed.Basic`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`

The second reading additionally removed redundant direct proof imports:
- `WeilConjectures.ConstructibleSheaf.Pullback` (provided publicly by Monoidal);
- `Mathlib.RingTheory.Finiteness.Cardinality`;
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`.
Their declarations remain available through the retained imports; no further DAG
proof dependency is pruned by these removals.

The node no longer directly depends on `lem-weil-pbc-cohomology-pullback-derived-unit`
(module `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`): the already proved
finite edge-map theorem suffices. It also no longer directly depends on
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finitely-many-components`,
`lem-weil-pbc-closed-point-residue-field-base`, or
`lemma-weil-pbc-finite-direct-image-exact`. Their geometric or exactness content is
encapsulated by existing tools; this does not claim those modules are globally unreached.
The original proof-dependency entries `def-weil-pbc-curve-setting` and
`def-weil-pbc-etale-constructible-sheaf` remain statement dependencies, not separate
proof obligations. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The second reading found three redundant direct
proof imports, and the constructibility/stalk step was incorrectly marked elementary
despite using the substantive existing constructible-pullback theorem. These are repaired. The planned general derived-unit comparison is
unnecessarily broad here: the proved finite edge map applies directly to the boundary.
The zero-dimensional theorem uses derived cohomology while this item uses Ext cohomology;
`Scheme.nonempty_sheafH_extDerivedIso` supplies the needed comparison.
Lean needed an explicit `ModuleCat.forget₂PreservesColimitsOfSize` instance to avoid
an unresolved universe metavariable in the stalk/forgetful-functor comparison.

## Second reading by P1

1. PASS: Read the complete module and its diff against the repository. The existing
   theorem signature is byte-for-byte identical, including IsReduced, the finite
   coefficient ring, arbitrary dense open, and both cohomology conclusions. All four
   public imports, existing docstrings and definitions are unchanged. There are no
   other delivered modules or change records. I independently read the closed-boundary
   computation in [Stacks Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA): its dimension
   zero, finite stalk product and finite direct-image arguments agree with this result.
2. PASS: Compiled the original delivery and then the repaired file through lcompile.py,
   with no warnings or errors. No sorry, axiom, unsafe, opaque, implemented_by or extern
   occurs in the module. A scratch copy with
   `#print axioms AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology` reports exactly
   propext, Classical.choice, Quot.sound and sorryAx. The last is inherited from existing
   open dependencies, notably the geometric zero-dimensional cohomology computation;
   no new hole or hollow definition is introduced.
3. PASS: No statement is split off and no declaration or node is added, so no new
   statement needs a truth or duplication check. The actual argument covers empty X,
   U = X, and zero-dimensional components: the inducing-map dimension bound is valid
   for an empty subspace, and the product/injectivity argument also works with no points.
   Every geometric point is supplied by algClosurePoint, without assuming a boundary
   point exists. Finite stalks use finite generation over the existing finite ring.
4. PASS AFTER REPAIR: Read DenseIrreducibleOpens, ZeroDimensionalCohomology, the
   Ext/derived comparison, the finite edge-map theorem and the upstream finite-stalk
   proof. The inducing-map argument obtains precisely the dimension bound needed by
   zero_dimensional_etale_cohomology. Its degree-zero map matches c literally; the
   comparison isomorphism transports both conclusions. The finite edge map points
   from cohomology on X to cohomology on Z, so its injectivity has the required direction.
   The FiniteSupport acyclicity theorem does not shorten the complete argument: it
   needs separately established finite closed support and separably closed residue
   fields, and supplies no degree-zero finiteness. Removed three redundant imports
   after individual omission compiles, then compiled with all three removed together.
   All other retained proof imports supply a used declaration. No longer needed lists
   every old proof dependency omitted from the new proof, including the two definitions
   retained only as statement dependencies. Inspected sk-thm-p1.json realized: none of
   the removed dependencies realizes a unit statement or step; the curve-calculation
   route remains intact. No claim is made that removed modules are globally unreachable.
5. PASS AFTER REPAIR: The only changed node fields are proof, proof_deps and proof_origin.
   Each recorded dependency exists and its Lean declaration agrees with the use in
   the proof; proof_deps is exactly the union of the step citations. The construction,
   finite product, comparison and finite edge-map steps describe the Lean argument.
   Changed the constructibility/stalk step from elementary true to false because it
   invokes the substantive constructible-pullback theorem. The agent proof origin
   correctly distinguishes the Lean implementation from the cited source computation.

Second-reading changes: removed the direct imports
WeilConjectures.ConstructibleSheaf.Pullback,
Mathlib.RingTheory.Finiteness.Cardinality and
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic; corrected the DAG elementary flag;
updated this report. No proof body, signature, definition, public import or hole changed.
Holes closed: AlgebraicGeometry.IsCurve.dense_open_boundary_cohomology (one).
Holes added: none. This closes one local hole using existing dependencies, rather than
establishing that its whole import closure is already free of sorryAx.
