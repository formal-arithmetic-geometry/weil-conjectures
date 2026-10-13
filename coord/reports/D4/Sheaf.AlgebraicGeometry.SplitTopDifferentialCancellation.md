## What changed

Replaced the earlier invalid two-existential decomposition with the actual Mathlib
canonical truncation `D = B.truncLE m`. The item's signature and original public
imports are unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.SplitTopDifferentialCancellationProperties` and
`Sheaf.AlgebraicGeometry.SplitTopDifferentialCancellationHomotopy`.

Proved the private helper `truncLE_term_retract`: below m use the canonical term
isomorphism; at m the section of the differential gives the projection
`id - δ ≫ section_ δ` onto cycles; above m the truncated term is zero. The item's
proof transfers properties degree by degree along these retractions, uses the
canonical support instances, and applies the homotopy theorem to this fixed D.

The new properties module is fully proved. It identifies a sheaf retract with
the kernel of the complementary idempotent for quasi-coherence, evaluates the
retraction and restricts scalars for flatness, and uses finite projective sections
and the affine finite-presentation criterion for finite presentation. Its proof
imports the existing `QuasicoherentKernel`, `QuasicoherentFiniteTypeAffine`, and
Mathlib `Flat.EquationalCriterion` modules.

All three delivery modules compile together without warnings using lcompile.py.
Two deliver3.py --no-push attempts passed local compilation and axiom probing,
then failed at fetching origin: first an SSH connection timeout, then a closed
SSH connection. The preflight therefore has not printed OK. Nothing was pushed.
The sandbox is complete and ready for a dry-run retry when the server is reachable.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_split_top_differential_cancellation`
(node `lem-pc-split-top-differential-cancellation`). This is a decomposition,
not an unconditional proof: it depends on the following one new hole.

The sole new and remaining sorry is
`AlgebraicGeometry.Scheme.Modules.split_top_differential_cancellation_homotopy`
(node `lem-pc-split-top-differential-cancellation-homotopy`). It states homotopy
equivalence of the *canonical truncation* at m with B, assuming the top split
differential and upper support bound. It does not assert equivalence for an
arbitrary supported complex, and it assumes no termwise sheaf properties.
Its docstring gives the section-based inverse and the identity-pair homotopy.

The other new public theorem,
`AlgebraicGeometry.Scheme.Modules.split_top_differential_cancellation_properties`
(node `lem-pc-split-top-differential-cancellation-properties`), is proved with no
sorry. Also proved the private helper `truncLE_term_retract` in the item.
Holes closed: 1; holes added: 1. Net holes: 0. The substantial sheaf-property and
degreewise-retraction parts are now proved, leaving only the homotopy part.

## No longer needed

No original public import was removed. The second reading removed the redundant
`Mathlib.Algebra.Homology.Embedding.CochainComplex` import from the new homotopy
module; its required declarations are already exposed by DirectImage.Basic. The old sandbox-only
`exists_split_top_differential_cancellation_properties` existential statement
and the arbitrary-D homotopy statement have been replaced; neither is used.

The item's direct planned dependencies
`def-pc-cochain-complex-modules`,
`lem-weil-pbc-quasi-coherent-module-kernel`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`, and
`lem-weil-pbc-finitely-presented-flat-module-projective` are replaced by the two
new proof-dependency nodes. These existing results are not globally pruned:
the homotopy node records the complex dependency; the proved retract-properties
node still uses the three sheaf/algebra results. Their corresponding modules
are needed through that proved theorem. No existing module becomes unnecessary
in the targets' closure as a result of this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's homotopy statement lacked every relation between D and B;
its support bounds cannot imply homotopy equivalence. The repair fixes D to the
actual canonical truncation, so the two theorem applications refer to the same
constructed object. No arbitrary witness of unproved existence supplies data.

The earlier report's suggested counterexample (an identity two-term complex
versus zero) is itself not a counterexample: that complex is contractible.
A correct example against the old universal statement is a nonzero single-term
complex B in degree 0, m=0, with zero D: its top map 0→0 is split, whereas its
nonzero degree-zero cohomology prevents equivalence to D.

The old sandbox nodes had Lean syntax as their mathematical statements and
recorded searches that were not logged. Rewrote both as self-contained
mathematical statements, updated signatures and proof steps, and ran fresh
LeanFinder, Loogle, LeanSearch and grep searches through msearch.py. LeanSearch
returned Internal Server Error and is recorded as unavailable. The other
searches found ingredients, not the exact cancellation theorem.

Stacks 068V gives the perfect-complex recognition context; the explicit
identity-pair calculation is an expansion of the plan and of 00MT, rather than
the literal statement of 068V. New docstrings specify this expansion. The
properties source uses 01PC and 00NX; 058B is not used. The unit route is retained
(`sk-thm-picard-coherence` has empty realized fields), and no existing statement
or definition changes.

## New nodes

`lem-pc-split-top-differential-cancellation-homotopy`:
`lean/Sheaf/AlgebraicGeometry/SplitTopDifferentialCancellationHomotopy.lean`.
This strictly isolates the chain homotopy calculation, without the flatness,
quasi-coherence, finite-presentation or lower-support conclusions of the item.
Tested the statement mathematically at m=0, for zero terms, for a contractible
identity pair, for a nonzero single term below the cutoff, and on the empty
scheme. Canonical truncation yields the expected complex in each case.

`lem-pc-split-top-differential-cancellation-properties`:
`lean/Sheaf/AlgebraicGeometry/SplitTopDifferentialCancellationProperties.lean`.
This proved theorem transfers flatness over the identity, quasi-coherence and
finite presentation along a sheaf retraction. It contains no cochain complex
or homotopy conclusion. Its zero and identity-retract cases are covered by the
same compiled proof. Both nodes inherit the ancestor, chapter and unit of the
item. No change record is needed: all added declarations are new and all new
imports in the existing item are proof-only.

## Second reading by D4

1. Compared the item with the repository using diff. Its existing declaration,
   docstring, hypotheses, conclusion, universe, namespace and original public
   imports are unchanged. Restored the single extra space before `:=`, so the
   existing signature is byte for byte identical. Both other modules contain
   only new declarations; no statement or definition change record is needed.
2. Read all three modules and compiled them in dependency order with lcompile.py.
   The only sorry is the named canonical-truncation homotopy theorem listed above.
   There is no axiom, unsafe/opaque declaration, foreign implementation, hollow
   definition, or arbitrary existence witness used as data. The complex is
   Mathlib's constructed `B.truncLE m`. The private retraction proof checks the
   three degree cases; at the boundary its projection annihilates the differential
   and restricts to identity on cycles. Separate scratch copies contain axiom
   probes for the item, private helper and both new public theorems. These passed:
   helper and properties use only propext, Classical.choice and Quot.sound; item
   and homotopy additionally use sorryAx, exactly from the reported homotopy hole.
3. Read the new node statements against their Lean signatures. The homotopy
   theorem requires only upper support and a split top differential, and fixes
   the truncated complex; it neither duplicates the existential item nor assumes
   any of its three sheaf properties. For m=0 the section contracts degree one,
   retains cycles in degree zero, and retains every negative term (no unjustified
   lower bound is asserted). A nonzero single term below m is unchanged, an
   identity pair is removed, and zero complexes and the empty scheme satisfy the
   construction. The properties theorem handles an actual sheaf retraction: its
   complementary-kernel calculation, scalar-restricted section retractions, and
   finite-projective affine sections prove precisely its three conclusions.
   Read Stacks 00MT, 068V, 01PC and 00NX: 068V is recognition context, 00MT gives
   the identity summand calculation, and the categorical sheaf generalization is
   explicitly expanded in the docstrings, not attributed as a literal statement.
   Fresh LeanFinder search for canonical upper truncation and split surjectivity,
   Loogle `HomotopyEquiv, CochainComplex.truncLE`, and grep with split/truncation
   and quasi-coherent/retract words gave no exact replacement. Also searched
   lean/Sheaf, lean/WeilConjectures, the upstream checkout, and Mathlib homology.
   `SplitIdentityHomotopyEquiv` concerns chain complexes of modules with an
   explicitly supplied rank-one summand; `FiniteFreeSplitTopCancellation` gives
   a quasi-isomorphism of module complexes. Neither directly proves this sheaf
   homotopy theorem. Closing the remaining hole requires constructing the chain
   map and its homotopy, beyond a few-minute lemma application.
4. The proof constructs truncation and degreewise retractions before invoking
   the two lemmas. Kernel quasi-coherence, affine finite presentation, and the
   finite-presentation/flat/projective Mathlib result remain used exactly where
   the properties proof needs them. Removed the redundant public import
   `Mathlib.Algebra.Homology.Embedding.CochainComplex` from the new homotopy module;
   compilation confirms that DirectImage.Basic already exposes what its signature
   needs. Both added imports in the existing item are proof-only. The original
   proof dependencies removed from the item are all listed under No longer needed;
   their uses through the new nodes are retained. The unit record has empty
   `realized.statement` and `realized.steps`, so no realized unit step is bypassed.
5. Compared the existing node records structurally: only proof, proof_deps and
   proof_origin changed. The new nodes carry source, self-contained statement,
   matching Lean declaration, docstring argument, creation record, blueprint
   ancestry, chapter, unit and logged searches. The item records the actual
   truncation/retract construction followed by properties and homotopy; the
   properties node records the three results its compiled proof uses. The one
   remaining homotopy node describes the explicit chain-map and contraction
   calculation rather than introducing unrelated data. Verdict: valid
   decomposition, one original hole closed and one strictly simpler hole added,
   net zero holes, with the property transfer and all degreewise retractions proved.

Second-reading changes: restored signature whitespace, removed one redundant
import from the new homotopy module, and recorded this independent review and
additional searches. No mathematical statement or proof was altered.
