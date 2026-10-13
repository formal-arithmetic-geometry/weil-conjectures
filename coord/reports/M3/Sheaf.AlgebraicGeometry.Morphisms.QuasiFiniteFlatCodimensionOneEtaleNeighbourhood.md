## What changed

Completed and checked the predecessor's proof of
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_flat_of_quasiFiniteAt_of_codimension_one`
in `Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFlatCodimensionOneEtaleNeighbourhood`.
Its signature and all original public imports remain identical. Removed exploratory
`#print axioms` commands, removed the unused name of the distinguished base point,
and rewrote the proof docstring to describe the actual Lean argument. Restored
the original top-level `open CategoryTheory` and qualified pullback names in
the proof, so no top-level namespace-opening command changes.

The four added imports are proof-only:

- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint` supplies the elementary etale
  localization and finite open piece.
- `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood`
  supplies the existing finite-flat criterion.
- `Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension` converts the descended
  smooth neighbourhood and isolated fibre point into an etale neighbourhood.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` supplies proved
  smooth descent and publicly imports the proved coheight-preservation theorem.

Replaced the item's two unformalized proof paragraphs by five steps matching the
Lean code and recorded their dependencies. Added DAG records for the two already
proved source-library results that the DAG did not name. These are attachments to
existing declarations (`lean.existing = true`), with no new Lean modules or theorems.
The stage-1 attachment rule is used rather than restating a proved declaration.

The source was checked at [Stacks 0BJH](https://stacks.math.columbia.edu/tag/0BJH),
[02LK](https://stacks.math.columbia.edu/tag/02LK),
[05B5](https://stacks.math.columbia.edu/tag/05B5), and
[00ON](https://stacks.math.columbia.edu/tag/00ON), alongside the existing Lean proofs.
Single-file compilation passes without warnings. The compiler checked all four
added import directions: none makes a cycle. Axiom probes show that etale finite
localization, the smooth-zero-dimension neighbourhood theorem, coheight preservation,
and smooth descent use only `propext`, `Classical.choice`, and `Quot.sound`.

The localization and shrinking follow the depth-two extension argument of
`sk-prop-input-spreading`; its statement and steps are untouched. The existing
proper-base-change nodes `lem-weil-pbc-etale-local-finite-at-point-elementary` and
`lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension` are generic tools for
finite localization and the final shrink, respectively. They do not replace a
step of the spreading unit. The first is precisely the existing formalization of
02LK; the second is already proved from source-library relative-dimension charts.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_flat_of_quasiFiniteAt_of_codimension_one`
(node `lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood`).
There is no `sorry` left in the delivered module. Added 0 holes and split off 0
new theorems. No definition or statement changed.

The proof uses the existing declaration
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_finite_flat_of_codimension_one`
in `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood`
(node `lem-sbc-finite-flat-codimension-one-etale-neighbourhood`). Its discriminant
argument remains in that dependency, not a newly introduced hole or a restatement
of this item. During second reading the repository already contained a reduction
of that declaration to its existing lower lemmas; the compiled declaration still
depends on `sorryAx`.
Consequently the delivered theorem still depends transitively on `sorryAx`; this
is a proof from the existing finite-specialization declaration, not a claim that
the target closure is axiom-free.

## No longer needed

None. The original module had no proof-dependency imports and its node had an
empty `proof_deps`. All four newly added proof imports are used. No existing node
or module is declared pruned. The singleton-fibre, residue-field and distinguished
base-point assertions supplied by 02LK are unnecessary for this outer reduction,
but the existing finite-localization theorem is retained and unchanged.

The direct discriminant construction, finite-locally-free reduction, branch-locus
principal-divisor argument and ramified specialization argument need not be
formalized again in this module: they belong to the already existing finite-flat
criterion. This is reuse, not a claim that those ingredients are unnecessary
inside that criterion.

## Where the brief, the DAG or earlier work was wrong

The original node listed no proof dependencies and combined the whole local
finite reduction, dimension transport, branch-locus argument and etale descent
into a single unformalized step. The existing finite-flat criterion gives a
strictly smaller dependency; finite localization, dimension transport,
unramifiedness cancellation and descent have now been written in Lean.

The predecessor already had a compiling proof, but left exploratory axiom prints,
a long-line warning, a changed top-level `open` command, and no report or DAG
update. Those omissions are repaired. The first dry run caught the namespace
opening as an interface change; it was removed instead of changing the interface.
No mathematical error or changed hypothesis was found. In particular, the proof
never assumes the original f is finite or globally locally quasi-finite, and
smooth descent does not require quasi-compactness of the etale map to its image.

Mathlib's available etale-descent instance requires a quasi-compact cover; the
Loogle query for etale and surjectivity found that instance. The source-library
smooth-descent theorem requires only flatness, surjectivity and local finite
presentation, which the constructed etale surjection supplies. This explains the
smoothness route followed by the zero-fibre-dimension shrink.

## New nodes

`lem-sbc-flat-locally-quasi-finite-coheight` records the already proved
`AlgebraicGeometry.Scheme.Hom.coheight_apply_of_flat` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` (lines 94–115).
It justifies the local-dimension comparison for the etale source projection.
No new declaration, module or hole is introduced. The theorem covers zero and
infinite coheight and does not require Noetherian hypotheses.

`lem-sbc-smooth-flat-surjective-source-descent` records the already proved
`AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` (lines 671–692).
It justifies descending smoothness to the open image. No new declaration,
module or hole is introduced. Empty sources are covered by surjectivity; no
quasi-compactness hypothesis is assumed. Both nodes reuse actual three-kind
searches in the predecessor's sandbox log; LeanSearch failures are recorded as
unavailable, not as absence of a match. Searches of the DAG and entire blueprint
found no exact existing records for these two source declarations.

There are no change records because no existing signature, definition or public
import changed. There are no forced adaptations.


## Second reading by M3

1. **Interfaces — pass.** Diffed the only delivered Lean module against the
   repository version. The existing theorem signature is byte-for-byte unchanged;
   all four original public imports, visibility, universe and namespace openings
   are unchanged. The additions are four plain proof imports, a local elaboration
   option, the proof, and its explanation. There are no new definitions or
   statements and no change records are needed.
2. **Proof and trust — pass with the reported existing dependency.** Compiled the
   delivered module locally with no errors or warnings. Searched it for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none occurs.
   Compiled a scratch copy with axiom probes for the item and each of the five
   direct dependency declarations. The item and finite-flat criterion use
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the other four use
   only the three permitted axioms. The proof constructs its open image and lift
   explicitly. Existential eliminations occur inside the theorem proof; there
   is no definition choosing arbitrary data from an unproved existence theorem.
3. **Split statements — pass, none added.** No new Lean theorem or hole is split
   off. The two new DAG records attach existing proved declarations. Read their
   source proofs and signatures: the coheight result covers all scheme points,
   including zero and infinite dimension; smooth descent requires flatness,
   surjectivity and local finite presentation, all supplied by the constructed
   etale surjection. Empty-source cases are vacuous or enforced by surjectivity.
   The finite-flat criterion is a genuinely stricter existing specialization,
   not this item under another name.
4. **Route and pruning — pass.** Read the finite localization, finite-flat
   criterion, smooth descent and final zero-fibre-dimension shrink. The pullback
   preserves dimensions and transports the codimension-one hypotheses; the
   open image contains x and the explicit lift is surjective. The singleton
   fibre neighbourhood proves both bounds on dimension at x. Searched the
   source library and Sheaf by codimension-one, ramification, coheight and
   descent names, and made a fresh Mathlib grep search for etale cancellation,
   descent and singleton dimension. No shorter applicable theorem was found;
   the available etale descent uses a quasi-compact cover. All four new imports
   provide declarations actually used; no old proof dependency exists to prune.
   Read sk-prop-input-spreading, including its realized field (currently empty),
   and verified this is a local purity reduction within its depth-two step;
   no unit statement, step or realized entry is changed or bypassed.
5. **DAG — pass.** Diffed the existing node and checked that only proof,
   proof_deps and proof_origin changed. Its five dependency nodes correspond
   exactly to the five substantive declarations used by the proof. The two
   added nodes record existing source declarations, their exact signatures,
   source and proof explanations, search records, creation metadata, chapter,
   unit and blueprint provenance; they introduce no modules or holes.

Second reading changed only this report: added these checks and corrected the
finite-flat dependency description to account for the repository's newer proof
reduction while retaining the verified `sorryAx` qualification. No Lean or DAG
repair was necessary. Closed 1 existing item hole, added 0 holes, split off 0;
pruned none. Scratch probes are outside the delivered lean directory.
