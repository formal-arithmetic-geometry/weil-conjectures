## What changed

Replaced the whole-proof sorry in
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.residue_transport` with a complete
Lean reduction. The existing declaration signature, hypotheses, public imports and
docstring are unchanged. Only private proof imports were added to the item.

The proof first derives maximality of the lifted uniformizer ideal from the existing
DVR theorem, using `Ideal.map_span` and `ULift.ringEquiv.symm`. Its first quotient is
therefore a field and a Noetherian ring. The literal `sfbResidueComplex` is read in
constant-ring coordinates by the new, concrete `fixedScalarDerivedModel` construction.
The coefficient-transport lemma gives its constructible cohomology and global Tor
condition. The existing proved `hasFiniteCoefficientProEtaleTorAmplitude_iff_locally`
and `constructible_localTor_iff_etaleOrigin` then give the etale antecedent. The
fixed-scalar presentation lemma identifies the original-site witness, and the assumed
completeness supplies the first conjunct. The reverse implication explicitly reverses
these three comparisons and discards only completeness.

Added three modules: `FixedScalarComplexModel` defines the actual termwise site and
scalar equivalences followed by localization; `IntegralResidueCoefficientTransport`
states just the coefficient comparison; `FixedScalarEtaleOrigin` states the generic
change of presentation of an already supplied etale-origin witness. Neither remaining
lemma is the item with its completeness hypothesis repackaged: the first has no etale
origin conclusion, and the second concerns arbitrary field-valued complexes with no
integral ring or original residue predicate. The actual descent step is supplied by
the already proved project theorem and remains explicit in the item's Lean proof.

No adopted source-library module or existing definition was changed. No consumers need
adaptation. The new definitions use the inverse of a specified exact equivalence;
they do not choose an arbitrary object from an unproved existence theorem.

Validation: all four sandbox modules compiled together in import order. Removed the
two proof-local `letI` style warnings. New universe arguments are explicit. The final
delivery check compiles and probes every delivered declaration independently.

## Proved and sorry left

Closed the one existing syntactic hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.residue_transport`
(node `lem-sfb-integral-models-residue-transport`). Its complete proof composes the
coefficient, local/global Tor, etale-descent and scalar-presentation equivalences.

Added two whole-proof holes, each with a source, proof in words and matching node:

- `AlgebraicGeometry.ProEtale.IntegralModelsStacks.integral_residue_coefficient_transport`
  (`lem-sfb-integral-residue-coefficient-transport`), in
  `Sheaf.AlgebraicGeometry.IntegralResidueCoefficientTransport`.
- `AlgebraicGeometry.Scheme.fixedScalar_etaleOrigin`
  (`lem-sfb-fixed-scalar-etale-origin`), in
  `Sheaf.AlgebraicGeometry.FixedScalarEtaleOrigin`.

The item itself has zero holes. The new model-construction module has zero holes.
This is a decomposition: one existing hole closed, two holes added, net one additional
hole. It is not a sorry-free proof of the mathematical result. The field/maximality
argument and the combination of the existing descent theorems are fully proved.

## No longer needed

No existing public import was removed. The item uses only the two new comparison
modules and `ConstructibleLocalTorEtaleOrigin` as private proof imports. The latter
publicly supplies `ProEtaleTorLocalGlobal`; no redundant extra import is needed.
The new fixed-scalar presentation module imports the comparison data, rather than the
stronger etale-descent theorem whose statement its own signature does not need.

The original direct proof dependency
`lem-weil-pbc-integral-stratified-perfect-characterization`
(`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`) is not used by this argument.
Its theorem requires dimension and invertibility assumptions absent from the item.
The unchanged existing public import through `IntegralConstantModelRealization`
retains that module, so this is a pruned DAG proof edge, not a module withdrawal or a
claim that the module leaves the targets' import closure. No modules were withdrawn.

The original direct edges to the integral completion theorem, internal-section tensor
comparison and Noetherian global constructibility now belong to the coefficient
comparison's proof plan. The finite-Tor comparison is still used inside the proved
etale-origin theorem. The etale constructibility definition and canonical integral
realization remain in the statements. These dependencies are retained, not claimed
as pruned. The original edge for locally Noetherian quasi-separatedness is supplied
by the unchanged inferred Mathlib instances in the application of etale descent.
Positive-level set-finiteness is unnecessary for the field-valued presentation lemma;
finite generation and finite presentation over the field are the finiteness notions.

## Where the brief, the DAG or earlier work was wrong

No false item statement or source error was found. The unit route (1)--(2) is retained.
The original proof plan omitted interfaces identifying the two literal residue
presentations and the two etale-origin presentations. The existing declarations for
local/global Tor and etale descent do not themselves change coefficient presentations.
The new statements isolate precisely these interfaces. In particular the integral
stratified-perfect characterization cannot be applied directly under this item's
hypotheses, and is not used as a substitute for the residue comparison.

The new statements were checked on empty schemes, zero residues, and unbounded
representatives. The generic presentation lemma allows any field, including infinite
fields; its finite model condition never means a finite underlying set. An empty
scheme uses the empty covering axiom and any ordered interval such as [0,0].

Searches used the authorized LeanSearch, LeanFinder, Loogle and Mathlib grep tools,
plus repository and whole-blueprint searches for scalar restriction, fixed scalar,
residue and module sheaf. Results supplied generic sheafification and equivalence
infrastructure but no existing declaration of the required presentation comparisons.
The proved project descent and constant-scalar equivalences are reused.

## New nodes

`def-sfb-fixed-scalar-complex-model` records
`Sheaf.AlgebraicGeometry.FixedScalarComplexModel`: precompose the fixed-scalar
complex with `AsSmall.down`, apply the inverse of the specified constant-scalar
restriction equivalence termwise, and localize. Its two definitions are real
constructions with no sorry. They are marked irreducible to keep elaboration from
unfolding the composite equivalences in consumers.

`lem-sfb-integral-residue-coefficient-transport` records
`Sheaf.AlgebraicGeometry.IntegralResidueCoefficientTransport`: the first quotient
comparison preserves constructible homology and global relative Tor amplitude.
Its proof plan invokes the normalized common-quotient comparison on flat-term K-flat
representatives, the internal-section tensor comparison, and Noetherian global
constructibility. It has no completeness or etale-origin clause.

`lem-sfb-fixed-scalar-etale-origin` records
`Sheaf.AlgebraicGeometry.FixedScalarEtaleOrigin`: change the presentation of an
existing etale-origin witness from small-site constant-ring modules to original-site
fixed-scalar sheaves. The source is the exact constant-scalar/site equivalences,
Noetherian constructibility comparison and field-valued tensor exactness. It does
not assert the existence of an etale antecedent for a general pro-etale complex.

No change records are needed: all existing public signatures and definitions remain
unchanged; all new public declarations are in new Sheaf modules with their own nodes.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
