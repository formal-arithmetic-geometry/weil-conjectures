## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.GeometricallyRegularOverFieldFlat` by a
compiling proof with the identical public signature and public imports. The proof constructs
`ψ` using `IsLocalization.lift` and proves that it is local by the unit criterion for
fractions. Mathlib supplies regularity of the polynomial localization; the existing 07E5
declaration supplies regularity of `A`.

The completed private helper `Algebra.extend_parameters_of_cotangent_independence` proves
the parameter-extension argument. It chooses a finite cotangent basis in the source,
preserves its independence in the target, extends it to a cotangent basis, and uses Nakayama
to recover maximal-ideal generators. The image set is enumerated first, with every image,
span, cardinality and ordered-list identity proved in Lean. The existing 00NQ theorem gives
regularity of the sequence and its initial quotient; the proved 07DY theorem gives flatness.
The equality `p.map φ = Ideal.ofList (x.map ψ)` identifies that quotient with the original
conclusion.

The new module `Sheaf.RingTheory.DifferentialCoordinatesCotangentIndependent` isolates only
the preservation of independent cotangent classes (the comparison square in steps 2–5).
It contains one public named theorem with a complete sourced proof in words. Its proof-plan
imports retain 07E5, Jacobi–Zariski, and field transitivity for the next worker. The original
node and the new node record the actual route. No other existing module was adapted.

Validation: both modules compile together without warnings through `lcompile.py --all`.
The new assertion was checked mathematically for the empty independent set, an empty
polynomial-variable basis (`m = 0`, where the source is a field), a field target (the square
forces zero source cotangent space), and an arbitrary residue field of infinite degree.
None of the Lean constructions requires a nonempty basis or a finite target residue field.
The original node is not a realized statement or step of `sk-thm-p1`; its unit route stays.

## Proved and sorry left

Closed: `Algebra.exists_flat_polynomialLocalization_of_isGeometricallyRegular`
(node `lem-weil-pbc-geometrically-regular-over-field-flat`), from the new cotangent lemma and
the existing declarations. There is no `sorry` in the item's module.

Completed proof helper: `Algebra.extend_parameters_of_cotangent_independence` (private).

Added hole: `Algebra.linearIndepOn_of_residue_differential_basis`, in
`Sheaf.RingTheory.DifferentialCoordinatesCotangentIndependent`, node
`lem-weil-pbc-differential-coordinates-cotangent-independent`. This is the only `sorry`
in the delivery. It asserts only linear independence, with no flatness or quotient
regularity conclusion. The construction of the localization map, parameter extension,
regular sequence, flatness criterion, and quotient identification are completed here.

This is a decomposition: one upper hole closed and one strictly smaller hole added, net zero
holes before pruning. The upper declaration still depends on `sorryAx` through that lemma
and the existing 07E5 theorem; it is not reported as an axiom-free completed target proof.
No definition obtains data from an unproved existence theorem: the localization map is a
real lift, and parameter lists are constructed in a proved private theorem from established
basis-extension results.

## No longer needed

Removed direct proof imports from the item's module:

- `Sheaf.RingTheory.JacobiZariskiHomologySequence` and
  `Sheaf.RingTheory.TransitivityGamma`: needed only for the remaining differential-square
  argument, so imported by the new lemma's module instead. Their nodes are retained there;
  they are not claimed as globally pruned.
- `Sheaf.RingTheory.LocalizationOfRegularRing` and
  `Sheaf.RingTheory.RegularRingSmoothAscent`: the route uses the already-proved
  `IsRegularRing.localization` and Mathlib polynomial regular-ring instance instead.

Below this item, neither the main theorem nor the new lemma uses
`lem-weil-pbc-regular-ring-smooth-ascent`, `lem-weil-pbc-localization-of-regular-ring`, or
`lem-weil-pbc-polynomial-ring-smooth`. The polynomial-regularity leaf
`lem-weil-pbc-polynomial-ring-field-regular-ring` supplies polynomial regularity directly.
The removed modules might still be reached through independent branches such as 07E5;
this report makes no assertion that they leave the entire targets' import closure.

All other original dependency nodes remain either in the main argument or in the new
cotangent-comparison lemma's sourced plan. In particular, Noetherian localization,
polynomial/localized differentials, the conormal/H₁ equivalence, and H₁ functoriality
were delegated, not discarded. The separate dimension bound is absorbed by the established
cotangent-basis cardinality identity and regularity, which the private helper uses directly;
`lem-weil-pbc-noetherian-local-dimension-le-generators` is not needed by that helper, although
other retained theorems may use it.


Exact old dependency audit: these nodes leave the main node's direct `proof_deps` and are
retained in the new cotangent lemma's proof plan:

- `def-weil-pbc-g-ring`
- `def-weil-pbc-kahler-differentials`
- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-jacobi-zariski-differential-maps`
- `lem-weil-pbc-jacobi-zariski-homology-sequence`
- `lem-weil-pbc-jacobi-zariski-surjection-h1`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-nl-presentation-h1-functoriality`
- `lem-weil-pbc-polynomial-ring-kahler-basis`
- `lem-weil-pbc-polynomial-scalar-extension`
- `lem-weil-pbc-transitivity-gamma`

These old dependencies are absent from both delivered proof plans (proved instances or the
cotangent-basis cardinality argument replace them):

- `lem-weil-pbc-localization-of-regular-ring`
- `lem-weil-pbc-noetherian-local-dimension-le-generators`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`

## Where the brief, the DAG or earlier work was wrong

No statement correction or false lemma was found. The plan's smooth-ascent detour for
polynomial regularity is unnecessary: Mathlib already has the regular-polynomial instance,
and the source library proves localization regularity. The supplied repository snapshot
has no local `literature/stacks-project/more-algebra.tex`; the exact source was read from
[Stacks Tag 07E6](https://stacks.math.columbia.edu/tag/07E6), together with the detailed
existing node proof and the signatures of the cited Lean declarations. LeanSearch returned
an internal-server error; that search is recorded as unavailable, without a no-match verdict.
LeanFinder and local Mathlib/source/DAG searches found no statement replacing the remaining
cotangent comparison.

## New nodes

`lem-weil-pbc-differential-coordinates-cotangent-independent`, in
`dag/nodes/sec-proper-base-change/`, states preservation of independent maximal-ideal
cotangent classes over the target residue field. It is exactly the conclusion of the
comparison square in Stacks 07E6, followed by preservation of independence under field
extension and an injection. Its proof in words constructs the residue subfield, proves the
differential comparison is an isomorphism, makes the polynomial localization geometrically
regular, uses 07E5 and Jacobi–Zariski to identify its H₁ with its cotangent space, and uses
07E2 plus functoriality for injectivity of the right vertical map. The final transfer of
independence is elementary linear algebra. The docstring spells out the square's
commutativity via presentation morphisms and evaluation under compatible residue sections.

The three kinds of search are recorded, including the unavailable LeanSearch service.
The existing separable-residue injection and regular-quotient independent-generator nodes
have different hypotheses and maps; neither states this result. No change record is needed:
all existing signatures, definitions, visibility, and public imports are unchanged.

## Second reading by V2

1. Compared the delivered main module with the read-only repository by `diff`, and checked
   the signature bytes separately. The existing declaration signature, visibility, and all
   public imports are identical. There are no definitions or forced adaptations. The only
   existing-node changes are `proof`, `proof_deps`, and `proof_origin`. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py --all`, without errors or
   warnings. Scanned both sources: the only remaining `sorry` is the named public theorem
   `Algebra.linearIndepOn_of_residue_differential_basis`; no forbidden declarations or data
   holes occur. Scratch-copy `#print axioms` reports only `propext`, `Classical.choice`, and
   `Quot.sound` for the private parameter-extension helper. The main theorem and new lemma
   additionally have `sorryAx`, as declared above. The localization lift is constructed;
   parameter lists are obtained in a fully proved theorem. Verdict: valid decomposition,
   one hole closed and one added, not an axiom-free proof of the target.
3. Read the complete split-off statement and docstring against Stacks Tag 07E6. Its
   conclusion is precisely independence under the injective scalar-extended cotangent
   comparison, strictly part of the original argument, with neither flatness nor quotient
   regularity asserted. Checked empty sets, zero variables (source a field and cotangent
   space zero), and field targets (injectivity forces source cotangent space zero).
   Arbitrary infinite residue extensions cause no issue: independence is tested by finite
   relations. Independently searched LeanFinder for injectivity on Zariski cotangent spaces
   from differential coordinates in a geometrically regular local algebra, Loogle for
   `LinearIndepOn, IsLocalRing.maximalIdeal` (zero hits), and local Mathlib/Sheaf/source
   files for cotangent injection and residue differentials. The closest Mathlib results
   concern presentation cotangent complexes or require flatness/formal smoothness; the
   separable-residue theorem has different hypotheses. No direct replacement found, and
   closing the remaining comparison requires substantial formalization. Verdict: pass.
4. Read the proof from the conclusion downward. The localization, parameter enumeration,
   regular-sequence prefix, flatness criterion and quotient equality are all proved, and
   the source regularity takes the shorter existing polynomial/localization instance route.
   Original public imports stay fixed; the added proof imports are private. The remaining
   lemma retains its proof-plan imports. The exact removed/delegated old-node lists are now
   recorded under `No longer needed`. Read `dag/units/sk-thm-p1.json`: this item is not a
   realized unit statement or step, and no realized node or unit record is changed.
   Verdict: pass; no unsupported claim of global module pruning.
5. Checked both nodes against the Lean declarations and argument. Each `proof_deps` is
   exactly the union of its proof steps' `uses`; the new node has its source, full proof,
   search record, creation metadata, blueprint origin, chapter/unit and verbatim Lean
   signature. The old node's unchanged statement is proved by the displayed reduction.
   Verdict: pass.

Second-reading changes: replaced the main theorem's outdated natural-language proof,
which still cited the removed smooth-ascent detour, with the route implemented in Lean;
expanded the report's pruning audit into explicit dependency lists; added this independent
review. No proof term, signature, definition, or node statement was changed.
