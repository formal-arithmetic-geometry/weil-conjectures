## What changed

Replaced the sorry in `AlgebraicGeometry.openOrdinaryTensor_germ_transport_equation`
with a complete proof from the two independent representative lemmas below.
Its signature, hypotheses, conclusion and existing public imports are unchanged.
Added proof-only imports of `OpenTensorRestrictionRepresentative` and
`OpenStalkRepresentativeCoherence`. The main module constructs the termwise
inverse pinned tensor restriction map and its additive stalk chain map. It proves
the chain square by `HomologicalComplex.Hom.ext` and function extensionality,
applies `homologyMap`, and uses both directions of `mapHomologyIso` naturality.
A proved private categorical lemma assembles these equalities. Explicit local
aliases and local irreducibility attributes keep the tensor comparisons folded;
no definition or instance visible to another module changes.

`OpenTensorRestrictionRepresentative` proves the formula for beta before stalks
or homology. Its private generic lemma works for four abelian categories,
additive functors and a natural iso, with only the target restriction functor
required exact. It compares the homotopy and complex localization factors and
uses quotient-comparison naturality. `OpenStalkRepresentativeCoherence` isolates
the remaining exact-functor coherence for arbitrary complexes M,N and an
arbitrary chain map M to restriction(N), without tensor data or a chain-square
hypothesis. The two new modules have matching DAG nodes; the parent proof and
proof dependency records follow the actual Lean proof.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.openOrdinaryTensor_germ_transport_equation`
(`lem-pc-open-ordinary-tensor-germ-equation`). The proof is complete from the
named representative statements; this is a decomposition, not an unconditional
sorry-free proof of the import closure.

Also proved the new declaration
`AlgebraicGeometry.openTensorRestriction_representative`
(`lem-pc-open-tensor-restriction-representative`) and the private helpers
`localize_termwise_comparison` and `assemble_homology_transport`.

Added one hole, the whole public theorem proof `:= by sorry`:
`AlgebraicGeometry.openStalk_representative_coherence`
(`lem-pc-open-stalk-representative-coherence`). It is the only sorry in the
delivered Lean files. No data is chosen from this theorem. The net holes closed
minus added is zero: one upper hole has been reduced to one independent exact
stalk representative coherence hole. The remaining statement has a complete
proof in words and the precise source factorization equations in its docstring.

## No longer needed

No existing import, module or proof dependency is pruned: both original public
imports are required by the unchanged statement, and all five original nodes
remain used for the comparisons and their interfaces. The rejected earlier
`OpenOrdinaryTensorGermFactorization` existential restatement is absent from
this delivery; neither its module nor its node is needed. The unit record
`sk-thm-picard-semicon` and its route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The static preflight classifies the proof-local irreducibility commands as a
possible interface change. Their scope and unchanged signature/users are
recorded in `coord/changes/openOrdinaryTensor_germ_transport_equation-local-elaboration.md`.
No consumer adaptation is required; no exported attribute or definition changes.
The unchanged direct consumer was also copied to a separate scratch check; its
compile cannot start because the published build lacks
`Sheaf.AlgebraicGeometry.OpenOrdinaryTensorGermCoordinates.olean`.
This is an existing publication gap before elaborating the consumer, not a
compiler error caused by this delivery. No consumer file is changed or delivered.

The earlier factorization was equivalent to the full target and is discarded.
The new split is different: one lemma identifies beta before any stalk or
homology operation, and the other concerns arbitrary representatives under
exact open stalk restriction. Neither mentions tau or tensorStalkIso, and the
main module proves the chain-square/homology argument combining them.

The named planned dependencies are mostly constructions, not already stated
coherence equations. Their definitions and the generic Mathlib/upstream
factorization API provide beta's representative formula. The remaining
representative coherence needs its own theorem, rather than pretending that a
construction's signature already asserts the desired compatibility.

Source check: Stacks 08HY constructs base change, and 08DW states compatibility
with restricting to opens; neither is literally a lemma listing the Lean exact
localization coherence equations. Stacks 015F gives the exact-functor
representative principle. The precise equations are in the Mathlib and upstream
ExactFunctor modules recorded in the new nodes. The new proof plans explicitly
name those equations. LeanFinder found short-complex homology naturality,
Loogle found no combined formula, LeanSearch returned Internal Server Error,
and local source/blueprint searches found no duplicate representative theorem.

Edge cases: neither new statement assumes nonzero homology, nonempty opens,
flatness of tensor pullback or K-flatness of P. Empty opens have no point for the
stalk lemma; beta's formula remains valid. Zero maps and complexes use the same
natural-transformation identities, and top opens specialize to the same exact
restriction factors. The generic beta proof uses exactness only for restriction,
not for tensor pullback.

## New nodes

`lem-pc-open-tensor-restriction-representative`, module
`Sheaf.AlgebraicGeometry.OpenTensorRestrictionRepresentative`: the proved
homotopy-to-complex localization formula for beta, strictly before stalks and
homology. No existing interface change is needed.

`lem-pc-open-stalk-representative-coherence`, module
`Sheaf.AlgebraicGeometry.OpenStalkRepresentativeCoherence`: the remaining exact
open-stalk homology coherence for arbitrary representatives and chain maps.
It contains neither a base-change square nor the tensor comparison or tau.
No existing interface change is needed.

The main module's proof-local command delta is documented in
`coord/changes/openOrdinaryTensor_germ_transport_equation-local-elaboration.md`.

## Second reading by C3

1. **Interface unchanged — pass.** Compared the delivered main module with the
   repository using `diff -u`, then compared the entire existing theorem signature
   as bytes, including its let-bound functors and degreewise chain-square hypothesis.
   Restored one extra space before `:= by`; signatures now match byte for byte.
   There are no changed definitions, instances, target statements or public imports.
   The added imports are proof-only. The local irreducibility attributes are scoped
   inside the namespace; the command delta is documented in the change record.

2. **Proof and trust — pass as a decomposition.** Compiled all three delivered
   files with `lcompile.py --all`: stalk coherence 10.5 seconds, tensor restriction
   representative 42.2 seconds, main equation 42.5 seconds, without warnings or
   errors. Inspected all proof bodies and checked for forbidden constructs and
   lines over 100 characters. The only delivered hole is the whole named theorem
   `openStalk_representative_coherence`; no definition contains a hole and no data
   is chosen from a mere existence theorem. A scratch `#print axioms` check
   returned only propext, Classical.choice and Quot.sound for the proved tensor
   representative; the main theorem and open stalk coherence additionally use
   sorryAx, exactly as expected for this decomposition. The categorical assembly helper uses
   only the four equations supplied to it. The main proof derives `hchain` from
   exactly `hτ`, applies homology composition, rewrites beta, and applies the two
   correctly oriented forgetful-homology naturality identities.

3. **New statements and sources — pass.** Read the two new modules and nodes,
   `SingleComplexOpenTensorRestrictionIso`, `OpenDerivedAdditiveStalkIso`, and
   the representative comparisons in `StalkComparisonSourceTransport`. Also read
   `mapDerivedCategoryNatIso_fac`, `mapDerivedCategoryCompIso_fac`,
   `mapDerivedCategoryHomologyFunctorIso_hom_app_Q` in the upstream ExactFunctor
   source and Mathlib's `ShortComplex.homologyMap_mapNatTrans`. Checked Stacks
   [015F](https://stacks.math.columbia.edu/tag/015F),
   [08DW](https://stacks.math.columbia.edu/tag/08DW), and
   [0098](https://stacks.math.columbia.edu/tag/0098): these supply the exact-functor,
   open-restriction and stalk background, while the precise comparison equations
   are the named Lean factorization identities, not assertions literally printed
   in those tags. Beta's new formula is before stalks and homology; its generic
   proof requires exactness only of R. The remaining coherence concerns arbitrary
   representatives M,N and a:M→R(N); it has neither tensor data nor tau or a
   chain-square assumption. Its natural-language proof uses naturality on a,
   then the composition and natural-iso factorization equations at N, then
   forgetful homology naturality. All stalk and restriction functors are exact
   by the imported instances. Thus it is a genuine independent part of the
   argument, rather than an equivalent renamed target. Zero complexes, zero
   maps and zero homology require no element cancellation; empty opens have no
   z, and top opens retain the same canonical factors. Repeated search with
   Loogle (`"homologyMap_mapNatTrans"`) found the generic short-complex formula;
   LeanFinder (`localization exact functor comparison on representative complex
   natural transformation cohomology`) found generic localization factors and
   Ext functoriality. Grepped both library roots and Mathlib homology sources
   for representative coherence and derived natural-iso/homology comparisons.
   No existing declaration gives either new project-specific formula. The
   remaining coherence is not a short direct application of the search hits;
   its named hole and full proof plan are retained.

4. **Top-down proof and pruning — pass.** The main proof supplies the actual
   chain-square-to-homology reduction and uses the representative lemmas only
   for its localization/coherence portion. All five original proof dependencies
   remain present in the statement or comparisons actually used. Both original
   public imports provide statement symbols; each added import supplies its
   named proof lemma. The new modules' public imports provide their statement
   symbols. No removed dependency needs adding to `No longer needed`. Read
   `dag/units/sk-thm-picard-semicon.json`; its `realized` record and unit route
   are unchanged. Net hole reduction remains zero, as explicitly reported.

5. **DAG matches Lean — pass.** Compared parent node records: only `proof`,
   `proof_deps`, and `proof_origin` changed. Its three steps match `hchain`/`hhom`,
   `hc`/`hβ`, and the two naturality equations plus categorical assembly.
   Checked both new nodes' statement dependencies, source, proof steps,
   dependency unions, creation records, blueprint ancestry, chapter/unit and
   Lean declarations against their modules. Neither new node depends on the
   parent, and neither states a hidden tensor-square hypothesis. The new
   representative node is proved; the stalk-coherence node is the one new hole.

Changed only signature-boundary whitespace and added this independent review.
