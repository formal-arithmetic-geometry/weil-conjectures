## What changed

Replaced the sorry in
`AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_filtration_core`
with a complete Lean proof from the three existing ingredients and one new transport lemma.
The original declaration's signature, visibility, docstring and public imports are unchanged.

The proof takes the separable closure inside the algebraic closure of C.functionField,
applies `Scheme.abelianSheaves_equiv_discreteGModules`, and transfers the finite primary
stalk hypotheses through its additive comparison. It applies the proved Sylow filtration,
forms the actual intermediate fixed field, and obtains its finite separable structure from
`openSubgroup_fixedField_finite_separable`. The normalization and its compatible generic-point
isomorphism come directly from hmodel. The commuting square is proved using the normalization
factorization. Finiteness, etaleness, flatness and finite presentation are derived from the
finite separable field extension. The degree is proved to be its field degree, hence the
open subgroup index, which is coprime to ell.

Added proof-only imports of `Mathlib.FieldTheory.Galois.Profinite`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, and
`Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport`.
Updated the core node's proof, proof_deps and proof_origin to match this argument.
Added the new transport module and its DAG node. There are no interface changes to existing
modules and no forced adaptations.

Both sandbox modules compile in import order using lcompile.py, without warnings.
deliver3.py --no-push printed OK: compilation and preflight passed except for the second
reading, which the next worker writes. Nothing was pushed. The original theorem signature
was also compared byte-for-byte against the repository and is identical.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_filtration_core`
(lem-sc-generic-primary-coarse-filtration-core). No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.Scheme.exists_sheaf_filtration_of_invariant_primary_chain`
(lem-sc-primary-module-filtration-sheaf-transport), in the new module
`Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport`.
Its whole proof is exactly `by sorry`; its docstring and node give the complete proof in words.
This is a decomposition, not an unconditional proof or a net reduction in holes: one closed,
one added. The new statement assumes the already constructed subgroup and invariant chain;
it contains no Sylow existence, curve, normalization, generic-point commuting square, etale
or finite-locally-free degree assertion. Those parts are now proved in the core.

The transport statement was checked on n=0 (zero and full endpoints force R=0), zero
successive quotients (d=0), repeated subgroup terms, H=G (no field extension), separably
closed K (trivial G), and imperfect K (Ks is the separable closure inside an algebraic closure,
not an incorrectly asserted algebraically closed separable closure). No nonzero-module or
positive-length assumption is added.

## No longer needed

None of the original imports, nodes or modules is pruned. All three original proof
ingredients are used directly: the abelian sheaf/module equivalence, Sylow filtration,
and open-subgroup fixed field. An experimental proof import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` was removed before
delivery; FiberDegree already exposes the needed finite-separable-etale field lemma.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The core node's original one-sentence plan did not state the bridge from the finite additive
subgroup chain supplied by SylowModuleFiltration to sheaf short exact sequences and the
terminal pullback isomorphism. The new transport lemma isolates that bridge and specifies
the canonical action-on-germs compatibility; an arbitrary underlying-group isomorphism
without that condition would not suffice.

The helper `openSubgroup_fixedField_finite_separable` has an unused universe parameter in
its converse clause. Its application needs all three universe levels specified to avoid an
unsolved universe metavariable. The Krull compactness instances require a direct proof
import of Mathlib.FieldTheory.Galois.Profinite, since the fixed-field module's own proof
imports are not re-exported.

The recorded literature files are absent from this read-only clone.
WANTED: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/
lem-sc-affine-generic-second.md, proof paragraphs 1--2, and literature/stacks-project/
etale-cohomology.tex, Tags 04JQ, 03QT and 03SF, for the new transport node.
The natural-language argument is explicitly marked agent-written, rather than claiming
an unavailable document was read. The existing node statements and Lean signatures were
read. The imported unit record has empty realized lists; these are unchanged.

The blueprint_refs.py ancestor lookup for the core returns None because preceding
stage-3 created.item fields contain module names instead of node IDs. The new node records
the actual imported ancestor lem-sc-affine-generic-second by following the existing
blueprint.from links; existing provenance fields are unchanged.

Searches were run through msearch.py and recorded in searches.jsonl. LeanSearch returned
Internal Server Error and is recorded as unavailable; LeanFinder returned only Galois
profinite constructions, and the Mathlib grep returned no sheaf-filtration transport theorem.
The library/DAG search found the three existing ingredients but no statement of this bridge.

## New nodes

`lem-sc-primary-module-filtration-sheaf-transport`, at
`dag/nodes/sec-curve-estimates/lem-sc-primary-module-filtration-sheaf-transport.json`,
realized by `Sheaf.AlgebraicGeometry.Curve.PrimaryModuleFiltrationSheafTransport`:
transports a supplied invariant additive-subgroup chain, whose successor quotients are
finite, ell-torsion and H-trivial, to short exact sequences of sheaves over the fixed field
and across a specified scheme isomorphism. It supplies only the sheaf filtration and its
terminal identification. It does not repackage the original curve theorem. Its statement
includes all hypotheses and the action compatibility, and its proof explains quotient
structures, finite bases, restriction of monodromy, exactness, constants, and indexing.
No change record is required: no existing interface or statement changes.


## Second reading by V1

1. **Existing interfaces: PASS.** Read the complete core module and its diff against the
repository. The sole existing theorem
`AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_filtration_core`
has its original signature byte for byte; visibility, docstring and public imports also
stay unchanged. No definitions, target statements or other existing modules change.
The three added core imports are private proof imports. No change record is needed.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled both modules
in import order through lcompile.py (3.5 s and 7.1 s), without warnings or errors.
Read the transfer of finiteness and primary torsion through iM, the supplied Sylow chain,
the actual fixed field L, hmodel's normalization and isomorphism, and every line of the
commuting-square and degree arguments. The factorization uses he in the correct direction;
the degree is the field finrank and then H's index. There is exactly one textual sorry,
the entire proof of the public named transport theorem listed above. No forbidden
constant, hollow definition, or arbitrary witness extracted into a definition occurs.
A scratch copy with explicit #print axioms for both declarations compiled and reported
only propext, Classical.choice, Quot.sound and sorryAx for each. Removed the scratch copy.
The core remains conditional on open lower statements; this is one hole closed and one
added, zero net holes removed, not a completed axiom-free proof.

3. **Split statement: PASS.** Compared every hypothesis and conclusion of
`exists_sheaf_filtration_of_invariant_primary_chain` with its new node. The specified
action-on-germs compatibility identifies the actual monodromy, rather than allowing
an unrelated group isomorphism. An open H is closed, its fixed field has fixing subgroup
H, and Ks is a separable closure of that finite separable field. Its invariant subgroups
and quotients are discrete continuous modules: stabilizers contain the open stabilizers
of representatives. Each finite quotient is killed by the prime ell and H acts trivially,
so a finite basis over ZMod ell gives precisely the stated constant biproduct. Exact
abelian equivalences transport the chain, and inverse image along e.inv transports it
to T. This proves the claimed natural-language reduction without a curve or degree
hypothesis. Checked n=0 (A0 is both bottom and top, so R and the pullback are zero),
repeated terms (d=0), H=G, a trivial Galois group, and imperfect K. For example,
a one-step chain with R=ZMod ell and trivial H-action gives one constant quotient;
a two-step chain with R=ZMod (ell^2) uses ell R as its middle term and gives two
constant quotients. The latter needs no split extension. The docstring gives the
quotient, basis, monodromy, exactness, constant-object and indexing arguments.
This is strictly a part of the core argument, not a restatement of the curve theorem.
Independent msearch queries used different words: Loogle `"ShortExact", "Sheaf"`
returned only two flasque topological-sheaf results; grep
`Discrete.*filtration|filtration.*Discrete|Galois.*constant|constant.*Galois`
returned only an unrelated stochastic-process result. Also searched lean/ for the
chain, filtration, short-exact and constant-sheaf declarations and read the three
existing ingredients. No replacement transport theorem was found. Its formal proof
requires the monodromy and exact-equivalence constructions and cannot be closed by a
short application of an existing result.

4. **Route and pruning: PASS.** The existing abelian-sheaf equivalence, Sylow theorem
and fixed-field theorem are all applied directly. FiberDegree is used for the degree
calculation and Galois.Profinite supplies the Krull compactness instances. The transport
module's public imports provide symbols in its signature; none is solely proof support.
The old core proof_deps minus the new proof_deps is empty, agreeing with
`## No longer needed`. Read dag/units/sk-prop-cd-affine.json: its realized statement
and all four realized step lists are empty and are unchanged. The chapter/unit route
is kept; only the module-chain-to-sheaf bridge is isolated below it.

5. **DAG records: PASS.** Diffed the existing core node: only proof, proof_deps and
proof_origin change, and the recorded Lean statement, statement and stmt_deps remain
identical. The new node records all hypotheses, the exact Lean signature, source place,
stepwise proof, union of proof dependencies, agent provenance, three search kinds,
split status, creation metadata, blueprint ancestry, chapter, unit and Lean realization.
Its proof agrees with the docstring and its single open declaration. The core's recorded
steps agree with the Lean proof, including normalization factorization and field degree.
The unavailable literature and failed LeanSearch service are explicitly recorded by the
first worker; this reading verifies the mathematical argument without claiming to have
read those missing local source files.

**Changes made by the second reader:** appended this independent review and recorded
the additional searches. No Lean or node repair was necessary. The closed and added
holes remain exactly the two declaration names in `## Proved and sorry left`; no
module or node is pruned.
