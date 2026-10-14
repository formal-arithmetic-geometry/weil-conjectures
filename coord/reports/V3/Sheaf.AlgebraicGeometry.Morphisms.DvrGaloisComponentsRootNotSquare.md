## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.dvr_galois_components_root_not_mem_square` by a complete
Lean assembly of the integral-closure field-factor identification and the tame
uniformizer calculation. Its statement and original public imports are unchanged.
Added two proof-only imports for the new modules. The Mathlib local-ring
ring-equivalence API is already provided by the existing DVR import. Updated the item's proof plan and proof dependencies.

The proof includes two proved private helpers. `root_factor_ne_zero` proves
nonzeroness of the localized root directly: the image of pi in the generic field
is a unit, left and right tensor images agree, the root equation makes its image
nonzero in the quotient field, and integral-closure inclusion and localization
are injective. `generator_not_mem_square_of_equiv` transports the maximal ideal
and then cancels the nonzero root to contradict 1 belonging to that proper ideal.
Neither helper contains a sorry.

All three delivered modules compile individually in import order with lcompile.py,
without warnings. No definition, target statement, existing signature or visibility
has changed. No other group's module has been adapted.

## Proved and sorry left

Closed:
`AlgebraicGeometry.Scheme.dvr_galois_components_root_not_mem_square`
(node `lem-sbc-dvr-galois-components-root-not-square`).

Added and left as whole named theorem proofs:

- `RingTheory.dvr_galois_root_factor_uniformizer`
  (node `lem-sbc-dvr-galois-root-factor-uniformizer`), in
  `Sheaf.RingTheory.DvrGaloisRootFactorUniformizer`.
- `AlgebraicGeometry.Scheme.dvr_galois_components_stalk_factor`
  (node `lem-sbc-dvr-galois-components-stalk-factor`), in
  `Sheaf.AlgebraicGeometry.Morphisms.DvrGaloisComponentsStalkFactor`.

This is a decomposition: one upper hole closed, two strictly separate lower holes
added, net minus one. The first is a ring-theoretic Abhyankar calculation for one
field tensor factor and contains no schemes; the second is an identification of
actual scheme stalks with localizations, has no tame unit or degree-bound
hypotheses, and asserts no root-square nonmembership. The main theorem proves
nonzeroness, transport and cancellation from these parts. Its transitive axioms
still include sorry through the two named dependencies; this is not a fully
sorry-free proof.

## No longer needed

No original module or proof dependency was pruned. The second reader removed
the redundant newly introduced proof import `Mathlib.RingTheory.LocalRing.RingHom.Basic`;
`Mathlib.RingTheory.DiscreteValuationRing.Basic` already publicly imports it.
No original import was removed, and no original proof dependency existed to prune. The new proof uses both new modules. The analogous
`RootNormalizationRootNotSquare` route is unusable here because it imports
`DvrRootNormalizationMaximalIdeal`, which reaches this item; it was not imported
and is not claimed as pruning. No unit statement or unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan consists of one long source argument with no named proof
dependencies, so the requested plan cannot be assembled from its recorded lemmas.
The two new nodes expose its genuinely distinct algebra and geometry parts.
The original node's blueprint ancestor helper reports None, whereas its parent
root-cotangent node records the correct ancestor
`sbc-thm-spreading-finite-etale-galois`; the new records use that ancestor and the
trait tame-calculation sentence, preserving the unit route.

Mathlib searches ran through msearch.py (LeanSearch was unavailable with HTTP
Internal Server Error, recorded as unavailable; LeanFinder, Loogle and grep ran).
The returned ramification-index-one lemmas require unramified input and do not
prove Abhyankar's lemma. Normalization's binary coproduct and affine integral
closure APIs supply pieces but do not state the full stalk-factor identification.
Searches of existing Sheaf/WeilConjectures modules and blueprint_refs.py found no
matching statement that avoids the import cycle. Source tags 09EV, 09EB, 0BRM,
09E7 and 0307 were read at their Stacks pages.

Edge cases checked: n=1 is evaluation, the empty coproduct admits no x, and
field factors exist by finite separability rather than any normalization-finiteness
hypothesis. In positive residue characteristic, n being a unit excludes that
characteristic from both the ramification index and inseparable residue degree.
The geometric identification intentionally works without invertibility of n;
finite Galois E_i/K still gives the required finite separable tensor decomposition.
Each new ring map is specified, and the stalk equivalence commutes with every
structural germ, so there is no arbitrary or hollow object construction.

## New nodes

`lem-sbc-dvr-galois-root-factor-uniformizer` records the maximal-ideal generation
calculation in one maximal quotient of E tensor_B A, followed by a prime
localization of its integral closure. Its source is 09EV, 09EB, 0BRM and 09E7.
It is needed only for maximal-ideal generation; root nonzeroness is already
proved in the original module.

`lem-sbc-dvr-galois-components-stalk-factor` records the affine normalization,
finite coproduct/field-factor decomposition, and actual-stalk localization
identification, including compatibility with every structural germ. Its source
is 09EV, 035H and 0307. It carries no tame calculation, and applies with the
weaker hypotheses used before Abhyankar.

No change record is required: existing interfaces are unchanged and all new
imports in the existing module are proof-only.


## Second reading by V3

1. **Existing interfaces: pass.** Read the full diff of
   `DvrGaloisComponentsRootNotSquare` against the repository: its sole existing
   declaration, including all let-bound rings, instance binders, qcqs assumptions,
   the point-over-root hypothesis and square-nonmembership conclusion, is byte
   for byte unchanged. Its docstring and six public imports are unchanged.
   Additions are private proved helpers, proof-only imports and the theorem body.
   The other two modules are new; no definition or existing visibility changed,
   and no change record or forced adaptation is needed.

2. **Proof and axioms: pass as a decomposition.** Compiled all three files in
   import order with lcompile.py, without warnings or errors. A scratch-copy
   `#print axioms` check gives only `propext`, `Classical.choice`, `Quot.sound`
   for each private helper. The main theorem and both new theorems additionally
   use `sorryAx`, exactly as the report declares. The only two textual sorries
   are whole named public theorem proofs in the new modules; there are no
   definitions, forbidden declarations, or arbitrary witness definitions.
   The existential stalk-factor witnesses are eliminated inside a proof only.
   Read the nonzeroness proof through the left/right tensor identity, root
   equation, inclusion into the quotient field and injective domain localization;
   read the cancellation proof through transport of the maximal ideal and
   singleton-span multiplication. Both prove the claimed conclusions.

3. **Split statements: pass.** Read [09EV](https://stacks.math.columbia.edu/tag/09EV),
   [09EB](https://stacks.math.columbia.edu/tag/09EB),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [09E7](https://stacks.math.columbia.edu/tag/09E7),
   [035H](https://stacks.math.columbia.edu/tag/035H) and
   [0307](https://stacks.math.columbia.edu/tag/0307). The ring statement specifies
   the right-inclusion algebra structure and requires a prime above the root;
   the Galois degree formula makes both e and f divisors of n, and the unit
   condition rules out residue-characteristic factors. Abhyankar applies since
   e divides the index-n root extension; 09E7 then gives index one and the stated
   generator. Checked n=1, degree-one E, and positive residue characteristic.
   The geometric statement uses finite separability of E/K, including when
   K1/K is inseparable: separable base change still gives a finite product of
   fields. Its finite-product integral-closure argument and affine stalk
   identification give both contraction and compatibility for every s, not
   merely the root. Checked r=0 (no normalization point) and n=1. Each hole is
   a separate part of the argument: geometry contains no tame assertion,
   algebra contains no scheme stalk, and nonzeroness plus cancellation are
   proved in the item. Both have source/proof docstrings and matching nodes.
   Fresh msearch LeanFinder queries for tame integral-closure base change and
   Spec integral-closure stalks, a Loogle query for maximal ideals and ring
   equivalences, and a grep query for stalk isomorphisms found component APIs,
   not either full statement. Read related Sheaf stalk-principal and normal-stalk
   declarations and searched the upstream WeilConjectures checkout: no usable
   duplicate. Neither open theorem admits a few-minute closure from these APIs.

4. **Route and pruning: pass after import repair.** The original node had no
   proof dependencies. Both new imports are used in the main proof; their
   public signatures require their algebra/geometry APIs. Removed the newly
   added local-ring RingHom proof import because DVR.Basic already exposes it;
   the item still compiles. The existing RootNormalization route would cycle
   through DvrRootNormalizationMaximalIdeal back to this item. Read
   `dag/units/sk-prop-input-spreading.json`: the trait tame calculation is kept,
   and no unit statement, step or realized entry is replaced or bypassed.
   No old proof-dependency node is omitted from the pruning report.

5. **DAG agreement: pass after record repair.** The old node changes only proof,
   proof_deps and proof_origin. Its two dependency IDs match the two theorem
   calls; its elementary steps match the two checked private proofs. Each new
   node records its complete setting, source, proof in words, searches, creation
   metadata, chapter/unit, blueprint ancestry and Lean location. Replaced the
   whitespace-flattened Lean statement strings of both new nodes with their
   exact multiline signatures from the delivered modules. No mathematical
   statement was changed. The two holes are explicitly counted as one upper
   hole closed and two lower holes added, net minus one.

Second reading changed only the redundant proof import, exact formatting of
new-node Lean statement records, and this report. No proof correction was needed.
