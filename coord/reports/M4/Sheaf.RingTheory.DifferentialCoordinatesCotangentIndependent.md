## What changed

Proved `Algebra.linearIndepOn_of_residue_differential_basis` without changing its signature
or public imports. Added two proved modules:
`Sheaf.RingTheory.DifferentialCoordinatesResidueComparison` and
`Sheaf.RingTheory.LocalCotangentComparisonNaturality`.

The first constructs the local map from the polynomial localization into F explicitly,
descends it to the residue field, localizes the polynomial differential basis, and proves
injectivity of the residue differential comparison by mapping its basis to the supplied basis
in F. The second constructs the cotangent comparison using `Extension.Cotangent.map` and
`liftBaseChange`, and proves the commuting square using presentation independence and
`h1CotangentEquivCotangent_comp_map`.

The main proof uses Jacobi–Zariski exactness to prove surjectivity of the upper conormal map,
then field transitivity and the existing geometric-regularity H₁ injection to prove the right
arrow injective. It transports arbitrary independent sets using flat scalar extension and
proved equivalences from extension cotangents to maximal-ideal cotangents.
All three modules compiled together, without warnings, through `lcompile.py --all`.
No other existing module was adapted. No statement or definition was changed.

## Proved and sorry left

Closed one original hole: `Algebra.linearIndepOn_of_residue_differential_basis`
(node `lem-weil-pbc-differential-coordinates-cotangent-independent`).

Added and proved `Algebra.injective_residue_differential_comparison_of_basis`
(node `lem-weil-pbc-differential-coordinates-residue-comparison`) and
`Algebra.exists_localCotangentComparison_naturality`
(node `lem-weil-pbc-local-cotangent-comparison-naturality`).
The private cotangent equivalence and its generator formula are proved as well.
No `sorry` remains in any delivered module; no holes were added or split off.
The proof still uses the existing theorem `Algebra.transitivityGamma`, whose proof contains
`sorry` outside this delivery, and the existing geometric-regularity H₁ theorem and its
transitive dependencies. This is closure of the item's own hole, not a claim that its entire
axiom dependency closure is complete.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.JacobiZariskiHomologySequence` (the canonical exactness lemmas are in
  Mathlib; this project module remains transitively imported by TransitivityGamma).
- `Mathlib.RingTheory.Kaehler.Polynomial` and `Mathlib.RingTheory.Etale.Kaehler` from the
  item (their basis/localization facts are used in the new residue-comparison module).
- `Mathlib.RingTheory.Localization.BaseChange`.
- `Mathlib.RingTheory.TensorProduct.MvPolynomial`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` (the item's proof does not
  establish regularity of the polynomial localization).

The proof route no longer needs these nodes for proving geometric regularity of B:
- `lem-weil-pbc-finite-type-algebra-noetherian`;
- `lem-weil-pbc-field-regular-ring`;
- `lem-weil-pbc-localization-noetherian`;
- `lem-weil-pbc-polynomial-scalar-extension`;
- `lem-weil-pbc-polynomial-ring-field-regular-ring`.

The associated localization base-change, polynomial scalar-extension, polynomial-regularity
and Noetherian-localization work is unnecessary on this branch. These are branch-specific
prunings; other users may still require those nodes. The statement still uses the Noetherian
and geometric-regularity definitions for A.
Polynomial differential basis/localization and presentation functoriality remain needed,
now in the two proved lemmas, and are not claimed pruned from the overall route.
The direct dependency `lem-weil-pbc-jacobi-zariski-differential-maps` is replaced by
the canonical homology exactness lemmas in this argument.
Additional old direct proof dependencies are now used through the proved supporting
lemmas: `lem-weil-pbc-polynomial-ring-kahler-basis`,
`lem-weil-pbc-kahler-differentials-localization`,
`lem-weil-pbc-nl-presentation-h1-functoriality`, and
`def-weil-pbc-kahler-differentials`. The old direct proof dependencies
`def-weil-pbc-g-ring` and `def-weil-pbc-noetherian-ring` remain statement dependencies.
These are removals from the item’s direct proof-dependency list, not claims of pruning
from the targets’ import closure. All statement public imports stay unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan proves more than needed: the upper
H₁-to-conormal comparison only needs to be surjective. Its injectivity and geometric
regularity of B can be omitted. Jacobi–Zariski exactness and differential injectivity give
this surjectivity directly. This is a simplification below the unit level, not a change to
any realized unit statement or step.

The source checkout lacks `literature/stacks-project/more-algebra.tex` on this machine;
read the actual source online at https://stacks.math.columbia.edu/tag/07E6, including its
commutative square and the cited injectivity argument. The new proofs expand those
comparisons in Mathlib's canonical presentation language.

Searches in Mathlib, Sheaf, WeilConjectures and the DAG found components rather than
an existing declaration for either new lemma. LeanSearch was unavailable (HTTP internal
server error); LeanFinder and actual source searches were successful and recorded in
`searches.jsonl` and each node. The new naturality proof needs no specially compatible
choice of residue sections: presentation independence gives equality for the default maps.

Edge cases checked against the proofs: m=0 gives a zero-dimensional differential source;
empty and infinite independent sets are handled by the unrestricted subtype family and
flat tensor lemma; ψ is an arbitrary local extension of φ and its restriction identity
establishes the scalar tower; F need not be finite over k or even finitely generated for the
new comparison theorem. The unchanged main signature retains its original hF hypothesis.

## New nodes

`lem-weil-pbc-differential-coordinates-residue-comparison` records the proved, strictly
smaller differential comparison step, with no characteristic or geometric-regularity
hypothesis. Its module is `Sheaf.RingTheory.DifferentialCoordinatesResidueComparison`.

`lem-weil-pbc-local-cotangent-comparison-naturality` records the proved general local-map
commuting square and its pure-tensor formula. Its module is
`Sheaf.RingTheory.LocalCotangentComparisonNaturality`. It makes no injectivity claim.
Both inherit the item's chapter, unit and blueprint ancestry. Neither adds a hole.
The item's proof and proof dependencies were updated to the Lean route.
No change record is needed: the original interface and statements are unchanged.

## Second reading by M4

1. Interface: compared the delivered item against the repository by diff and compared
its theorem header byte for byte. All hypotheses, universes, binders, the arbitrary
local extension ψ and its restriction equation, and the arbitrary independent set s
are unchanged. All six public imports are unchanged. The two other modules are new;
there are no adaptations or changes requiring a change record. Verdict: pass.

2. Proof and axioms: all three files compiled cleanly with lcompile.py --all.
Explicit #print axioms probes of the item, both supporting theorems, and both private
helpers show only propext, Classical.choice, Quot.sound, with sorryAx additionally
in the item through existing dependencies. The two supporting theorems and private
helpers are free of sorryAx. There is no sorry or forbidden declaration in delivered
code. The equivalence is constructed from existing quotient equivalences, not chosen
from an unproved existence theorem; μ is explicitly constructed in its proved theorem.
Verdict: pass. One original hole is closed, no hole added; this does not close the
existing field-transitivity and geometric-regularity dependency holes.

3. Supporting statements: checked their Lean headers against the node lean.statement
records and their mathematical statements. The first builds the local map to F, uses
its residue-field embedding, and maps the localized differential basis to b; it needs
neither geometric regularity nor hF. For m=0 its source is zero. The second constructs
a scalar-extended quotient map and proves its generator formula and commuting square;
it asserts no injectivity and allows general commutative base rings. Neither restates
the target, and neither is left unproved. Their source/proof docstrings and complete
new-node records are present. Repeated LeanFinder search using local-ring conormal
naturality and source searches using residue/cotangent and differential/basis found
components (map_eq, map_comp_apply, map_cotangentComplex), not an existing theorem
with either complete statement. Verdict: pass.

4. Route and pruning: read Tag 07E6 and dag/units/sk-thm-p1.json, including realized.
The item is below the unit's realized statement and steps; these remain unchanged.
The proof uses differential comparison and the same cotangent square as the source.
Surjectivity of c₀ suffices: lift both source elements, then use injectivity of the left
and bottom maps to identify the lifts. This avoids unnecessary geometric regularity
of B. Flat scalar extension and two actual quotient equivalences preserve arbitrary
independent families, including empty and infinite sets. No shorter matching library
result was found. Added to No longer needed every remaining old direct proof edge
removed, distinguishing edges relocated into helpers and statement dependencies from
actual branch pruning. Replaced the new residue-comparison module's unnecessary
public JacobiZariski import with the smaller public Kaehler.Basic import; its statement
needs differentials, while its proof does not need Jacobi–Zariski. Verdict: pass.

5. Nodes: checked the existing node changes are confined to proof, proof_deps and
proof_origin; its lean.statement is unchanged. All three proof_deps lists equal the
unions of their proof steps' uses. The new node headers match Lean verbatim, their
chapter/unit and blueprint ancestry match the item, and their source, search, status,
created and lean records are present. The canonical Mathlib exactness and surjection
comparison facts implement the corresponding old nodes without using their project
wrapper declarations. Verdict: pass.

Changes by the second reader: replaced the unnecessarily broad public differential
import with Kaehler.Basic and completed the direct-dependency pruning report.
The mathematical proofs and DAG route required no repair.
