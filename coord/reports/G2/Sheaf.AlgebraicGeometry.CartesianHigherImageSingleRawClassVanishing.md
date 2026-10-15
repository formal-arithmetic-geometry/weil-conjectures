## What changed

Proved `AlgebraicGeometry.Etale.exists_cartesianHigherImage_single_raw_class_eq_zero`
without changing its signature. The proof obtains a finite-stage chart representative,
reflects the assumed limit zero through the specified chart isomorphism, constructs
the restricted-over cohomology presentation, invokes complex cohomology continuity,
and uses the filtered-colimit equality criterion to kill the representative at a
later stage. Its transition identity gives exactly the required raw derived morphism.
The private helper `restrictedOver_eventually_zero` proves this filtered-colimit
argument for any fixed restricted-over abelian coefficient sheaf.

Added `Sheaf.AlgebraicGeometry.CartesianRawClassChartRepresentative`, containing
one theorem for the first-continuity/descent part and its specified map identities.
It has no vanishing hypothesis and no eventual-zero conclusion. Its docstring gives
the full source proof. The second-continuity/injectivity step is implemented in the
item itself, rather than included in the new obligation.

Registered the item's missing docstring node and the new representative node.
The proof follows the two uses of continuity in the existing parent node's plan.
No target statement, existing definition, or other group's module was changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.exists_cartesianHigherImage_single_raw_class_eq_zero`.
There are no `sorry`s in the item module.

Added one hole:
`AlgebraicGeometry.Etale.exists_cartesianRawClass_chart_representative`, node
`lem-sc-cartesian-raw-class-chart-representative`.
This is a decomposition, not a net reduction in the count of holes. It still needs
first-continuity surjectivity with the fixed original stage derived coefficient
complex, followed by the chart adjunction and the two canonical transport identities.
It does not need to prove eventual vanishing or filtered-colimit injectivity.

The sandbox scratchpad records substantial attempts to prove this new obligation:
`DerivedDescent.lean` proves finite-stage representatives in derived cohomology of
an arbitrary fixed bounded-below complex from the existing continuity theorem;
`Geometry.lean` proves affine etale descent above the specified original index and
the geometry of a restricted system; `Eval.lean` proves arbitrary-coefficient raw
evaluation invertibility and generator pullback compatibility; `ClassComp.lean`
proves chart-class pullback composition. They were compiled separately. These are
research scratch files, not delivered modules. Combining evaluation with the exact
cohomology and chart-map definitions remained unfinished, as detailed below.

## No longer needed

No original imports were removed: the original module had only its two public
statement imports, both preserved. The proof imports only the chart representative,
restricted-over cohomology presentation, complex-cohomology presentation, and
Mathlib filtered abelian-group colimits.

The item's proof does not need finite-family assembly, common-index equalization,
sheafification of local representatives, a cover of V, stalk calculations, or the
module `Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly`. That module
remains needed by the finite-family parent; this delivery does not withdraw it.
No existing DAG dependency is declared globally obsolete: the original item's
DAG node was missing, and its parent still uses the two continuity steps retained
here. Unused exploratory composition and evaluation modules were removed from
`lean/` and kept only in `scratchpad/`; they add no library imports or holes.

## Where the brief, the DAG or earlier work was wrong

The docstring id `stage3-cartesian-higher-image-single-raw-class-vanishing` had no
matching node JSON or Lean attachment in the supplied DAG. This delivery registers
that existing statement using the source and the one-class specialization of its
parent's proof, with no change to its Lean signature.

The existing parent plan requires two uses of continuity. Descending only the affine
etale test object does not descend an arbitrary derived class. The new lemma makes
first-continuity surjectivity with the original stage complex fixed explicit; the
item proves second-continuity injectivity with the original sheaf F fixed.

The difficult remaining glue compares unbounded cohomology's
`presentationDerivedMap` with bounded-below restricted-section evaluation, then
with the specified chart lift. The exploratory triangle calculation was reduced
to inverse-image composition coherence but did not finish its normalization of
bounded-below inclusions and over-category fibre-product projections. The chart
naturality calculation similarly reached the canonical raw-pullback identity but
some full combinations exceeded the 60-second per-file limit. No limit was raised,
no definition was changed, and these incomplete attempts are excluded from delivery.

Edge cases were checked in the source argument: empty affine V gives zero groups,
q=0 uses the same evaluation and continuity maps, and a zero class is handled by
functoriality without selecting any object from an unproved mere existence theorem.
The Lean proof chooses witnesses only inside theorem proofs.

## New nodes

`stage3-cartesian-higher-image-single-raw-class-vanishing` registers the existing
item declaration and records its implemented representative/continuity/zero route.
Its source is Stacks 0EYM with 0EYL and 0GIT.

`lem-sc-cartesian-raw-class-chart-representative` records the strictly earlier
surjectivity and comparison step, in its own new module. Its source is the first
continuity application and comparison square of Stacks 0EYM's second proof, using
0EYL and 0GIT. There are no interface changes. The change record
`coord/changes/G2-single-raw-class-proof-local.md` explains the private proof imports
and section-local irreducibility attributes flagged by the static preflight.

## Second reading by G2

1. Interface: PASS. Read both delivered modules and compared the item with the
   repository using `diff -u`. The complete signature of
   `exists_cartesianHigherImage_single_raw_class_eq_zero`, including all typeclass
   hypotheses, the limit-zero hypothesis, the shift, and the prescribed raw
   transition, is byte-identical. The two original public imports remain necessary:
   `CartesianHigherImageTransitions` defines the transition and
   `AbelianHigherDirectImageClassCompatibility` defines `abelianComparisonFree`.
   No existing definition, visibility, target, or other group's module changes.
   The added irreducibility attributes are explicitly local and end before the
   public theorem; they do not modify imported declarations for later users.

2. Proof: PASS, with the one explicitly reported open dependency. Both delivered
   modules compiled using `lcompile.py --all` (13.8 and 53.3 seconds). There is no
   sorry in the item and exactly one in the new public representative theorem;
   no definition or private helper contains a sorry. No forbidden declaration or
   kernel bypass occurs. Read the private continuity proof: `hleg` transports the
   zero equality to the cocone, `isColimit_eq_iff'` supplies a single arrow in the
   opposite index category, and `hm` transports the resulting zero back to the
   specified restricted cohomology map. In the main proof the chart isomorphism
   reflects zero, the chart-system properties supply every continuity hypothesis,
   and `htrans` gives precisely the witness arrow `a.left ≫ b`. All witnesses are
   eliminated inside theorem proofs; no definition selects an arbitrary object
   from an unproved existence theorem. Scratch copies print the axioms of both
   private helpers, the item, and the new representative theorem: the helpers
   use only `propext`, `Classical.choice`, and `Quot.sound` (the zero-reflection
   helper needs no choice); the public theorems additionally use `sorryAx`,
   as expected from the one open representative theorem.

3. Split statement: PASS as a decomposition. Read [0EYL](https://stacks.math.columbia.edu/tag/0EYL),
   [0GIT](https://stacks.math.columbia.edu/tag/0GIT), and the second proof and map
   construction of [0EYM](https://stacks.math.columbia.edu/tag/0EYM). The new lemma
   uses qcqs stages, affine transitions, an affine etale test object, and the fixed
   bounded-below original stage complex exactly where required. It descends an
   arbitrary class and supplies two identities, without a zero hypothesis or a
   later-stage vanishing conclusion. Thus it leaves surjectivity and comparison
   coherence open, while the item actually proves the subsequent injectivity and
   eventual-zero argument. It is not the item under another name. Checked the
   singleton index category, the zero class, empty V, and degree zero: choose an
   identity chart object after descent, use the zero representative when appropriate,
   and use the same canonical unit/composition and shift identities in degree zero.
   Cofilteredness supplies nonemptiness; no empty-index exception is suppressed.
   Repeated LeanFinder and Mathlib grep searches with hypercohomology/descent
   wording and searched `lean/Sheaf` and `lean/WeilConjectures` for representatives,
   continuity, and eventual zero. The structure-sheaf section vanishing results
   returned by LeanFinder do not apply to these coefficients or derived degrees.
   Existing `derivedEtaleCohomology_limit`, raw evaluation, raw naturality, and
   exchange lemmas are precisely the ingredients of the remaining comparison
   obligation, rather than duplicates of its conjunction. Its complete proof in
   words and its DAG node are present. The unfinished scratch comparison work is
   substantial; the remaining obligation cannot be closed by a short application
   of an existing theorem.

4. Route and pruning: PASS. Read the finite-family parent's two-continuity plan
   and `dag/units/sk-thm-vanishing.json`. This is a reduction below that unit; its
   route and realized fields are unchanged. The private helper uses existing
   restricted cohomology presentation and complex continuity, then Mathlib's
   filtered-colimit equality criterion, instead of introducing another vanishing
   hole. Every added import supplies a declaration used by the proof; the new
   module's public import supplies its signature's chart constructions. No old
   proof dependency exists for the previously unregistered item node to remove.
   The parent's finite-family assembly remains necessary for that parent and is
   not falsely reported as pruned. One original hole is closed and one new hole
   is added: zero net hole reduction, no module pruned.

5. DAG: PASS. Both stored Lean signatures match their files verbatim, every
   dependency id exists, and each `proof_deps` list is exactly the union of the
   proof steps' `uses`. The item node records the implemented chart-zero,
   presentation-colimit, and transition argument. The new node records only the
   representative and canonical-map comparison step and has the required source,
   creation, blueprint, chapter, unit, search, and Lean fields. The original item
   node really was absent from the repository. No existing node or unit is
   silently overwritten.

Changes made in this reading: clarified the new lemma's proof in words by
explaining arbitrary bounded-below evaluation and base change of the affine model
to the representative's stage. Corrected its source attribution: the first use
of 0GIT is the parent plan's extra reduction for arbitrary raw classes, not an
explicit citation in 0EYM itself. Added the independent searches to its node and
wrote this review. No Lean statement or proof term was changed.
