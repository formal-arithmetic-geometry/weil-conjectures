## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces` by a complete Lean proof
from the existing `PrimeSpectrum.finite_disjoint_basic_constructible_refinement`.
The public theorem's statement and all imports are unchanged.

The proof follows the existing six-step DAG route. Use the canonical isomorphism
`X ≅ Spec Γ(X, ⊤)` to transport the constructible image to a spectrum. Enumerate
its finite basic-set presentation by a `Fin` type and apply the existing disjoint
refinement. A fully proved private helper realizes each basic set as the spectrum
of a localized quotient, mapping by an immersion with exactly the desired image.
Transport these maps back to X and pull them back along ι. The second pullback
projection has full image, hence is a closed immersion. Since its target is affine,
its source is affine. Pullback and composition instances give the two immersion
clauses, and the pullback image formula gives the required ranges. Constructibility,
local closedness, disjointness and the union identity finish the proof.

The empty-image case needs no extra hypothesis or nonempty index: the finite
presentation and refinement allow zero pieces, and every subsequent construction
is indexed by `Fin p`. The argument also allows empty basic pieces and the zero ring.
No node update is needed: the existing node's six proof steps and proof dependencies
are precisely the route implemented. The blueprint unit's realized steps are retained.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_finite_affine_immersion_constructible_pieces`
(node `lem-weil-pbc-immersion-affine-constructible-pieces`): one of one original sorries
removed. Also proved the private helper `basic_constructible_affine_immersion`, which
implements the existing node `lem-weil-pbc-basic-subset-immersion-image`.

No `sorry` remains in the delivered module, and no new one is introduced elsewhere.
The proof still depends on the existing theorem
`PrimeSpectrum.finite_disjoint_basic_constructible_refinement`
(node `lem-weil-pbc-affine-basic-sets-disjoint-refinement`, module
`Sheaf.RingTheory.AffineBasicSetsDisjointRefinement`), whose proof remains `sorry`
in the repository. This is the next existing item, not a new split-off statement.

Validation: the module compiles through `lcompile.py` without errors or warnings.

## No longer needed

None. The original imports are all retained; the existing disjoint-refinement import
is used directly. All six steps of the existing proof plan are implemented, and no
existing proof-dependency node or module is bypassed. Three trial Mathlib imports
were removed after confirming that the original public imports already expose the
needed declarations: `Mathlib.RingTheory.Spectrum.Prime.RingHom`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. These were never imports on the base.

## Where the brief, the DAG or earlier work was wrong

The Mathlib match for `lem-weil-pbc-basic-subset-immersion-image` qualifies
`range_comap_of_surjective` as `PrimeSpectrum.range_comap_of_surjective`; the actual
lemma is at the root namespace. The Lean proof uses the actual root declaration.
The quotient immersion is obtained directly from
`IsClosedImmersion.spec_of_surjective`, since the recorded quotient instance is
parametrized by a bundled `CommRingCat`. This requires no statement correction.

The referenced Stacks TeX files are absent from this machine's repository copy;
the proof uses the supplied node's source references and its complete proof plan,
and the Mathlib declarations were inspected locally.

## Second reading by S2

1. Compared the sole delivered module with the repository using `diff -u` and
   checked the existing theorem's text from `theorem` through its signature by
   exact string equality. Verdict: byte-for-byte unchanged. Its hypotheses remain
   affine X, an immersion ι, E = range ι, and constructible E; every conclusion
   (affineness, both immersions, ranges, local closedness, constructibility,
   pairwise disjointness and union) is supplied. All original imports and the
   existing docstring are unchanged; no definition or change record is added.
2. Compiled the delivered file through lcompile.py with no errors or warnings.
   Inspected every proof and scanned the diff: no sorry, axiom, unsafe, opaque,
   implemented_by, extern or hollow definition is introduced. Compiled a scratch
   copy with #print axioms for both declarations: the private basic-set helper
   uses only propext, Classical.choice and Quot.sound; the public theorem uses
   those and sorryAx from the existing disjoint-refinement dependency. Verdict:
   genuine reduction, not an unconditional claim of axiom-free completion.
3. No statements were split off and no new public statement is introduced.
   The fully proved private helper realizes the existing basic-subset-image node.
   Inspected Mathlib's exists_range_eq_of_isConstructible: its basic-set image
   calculation is exactly the helper's rewrite chain, but the whole theorem gives
   an arbitrary ring map and does not assert an immersion. The helper correctly
   composes the localization open immersion and quotient closed immersion.
   Checked n = 0, f = 0, a unit f, the zero ring and empty basic sets: the quotient,
   localization and range lemmas require no nontriviality or nonempty hypothesis.
   For empty E, Fin p and finite presentations permit zero pieces. Searched
   lean/Sheaf, lean/WeilConjectures and local Mathlib with rg, and separately ran
   msearch.py grep for affine stratification, disjoint constructibles and
   constructible immersions (no hits). Verdict: no unnecessary new open lemma.
4. Read downward from the target: isoSpec transports constructibility; the finite
   basic presentation is enumerated by Fin; the existing disjoint refinement is
   applied; each basic piece is realized by the proved helper; pullback.snd has
   full range and is therefore a closed immersion into an affine scheme;
   pullback.fst gives the required immersion into Z. The pullback range identity
   and homeomorphism preimages give exactly the partition. The helper's argument
   is the short existing Mathlib calculation; no shorter lemma found supplies
   the full affine-immersion partition. All imports support public signatures or
   the refinement proof. Verdict: no proof dependency pruned. Checked
   dag/units/sk-thm-p1.json realized: this subordinate node bypasses no realized
   unit statement or step, and the unit route is unchanged.
5. Opened the item's node and all fifteen proof-dependency records. Matched its
   six steps against the Lean proof and the recorded Mathlib declarations,
   including the pullback range formula, immersion base change/composition,
   closed-image criterion and affine preimage criterion. The mathematical proof,
   proof_deps and proof_origin still describe this route; the helper implements
   the existing Mathlib leaf rather than a new node. Verdict: no node update
   required. The previously reported root-namespace correction for
   range_comap_of_surjective is confirmed in the Mathlib calculation.

Second reading changed only this report. No fault requiring a Lean or DAG repair
was found; the existing upstream refinement sorry is explicitly recorded above.
