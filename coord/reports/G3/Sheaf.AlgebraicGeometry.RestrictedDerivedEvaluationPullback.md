## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedEvaluation_pullback`
by a compiling naturality and cancellation proof. Its signature and all three existing
constructions (`Hzero`, `transportZero`, `pullbackHom`) are unchanged. Added the private
proof import `Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison`.

`RestrictedDerivedSectionZeroComparison` explicitly constructs `derivedSectionPullback`
from the derived adjunction unit and the same Leray isomorphism used by
`rawAffineComplexPullback`. It constructs `derivedRestrictionIso` from the two
inverse-image composition comparisons and the equality of the pullback projections,
then constructs the natural transformation `restrictedSectionPullback` by whiskering
and taking zeroth homology. No data is selected from an existence theorem.

Two comparison calculations are split into separate modules. The zero lemma concerns
only a single sheaf and an arbitrary coefficient map. The shift lemma concerns only a
shifted single sheaf and its coefficient map. Neither contains the arbitrary derived
morphism `t` or the source isomorphism `e` of the original theorem. The main proof combines
them by actual naturality, maps composition by the functor, and cancels the single of
`e.hom` with the single of `e.inv`, together with the inverse single comparison.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedEvaluation_pullback`
(node `lem-sbc-restricted-derived-evaluation-pullback`). No sorry remains in the item.

Added two holes, each the whole proof of a public theorem with a source and proof docstring:

- `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedSectionPullback_zero`,
  node `lem-sbc-restricted-derived-section-zero-comparison`.
- `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedSectionPullback_shift`,
  node `lem-sbc-restricted-derived-section-shift-comparison`.

This is a decomposition of one hole into two comparison calculations, not a complete
sorry-free proof and not a net reduction in holes. The natural transformation, restriction
isomorphism, naturality argument, and cancellation argument are fully implemented.
The three delivery modules compile locally without warnings.

The new statements were checked on p = 0, an empty restricted scheme, zero sheaves,
identity maps, and noninvertible coefficient maps: the constructions require no inverse
of the coefficient map or section pullback. The zero lemma does not assume psi is an
isomorphism. The main theorem alone uses the given source isomorphism for cancellation.

## No longer needed

None. No original import is removed, and no original dependency module is pruned from
the import closure. The original five direct proof dependencies are used in the explicit
construction and the two comparison calculations; the parent node now points to these
two nodes, with those original dependencies below them. This preserves the existing
unit route. No represented generator or continuity theorem is introduced into this square.

## Where the brief, the DAG or earlier work was wrong

The recorded dependencies provide constructions of inverse image, the derived adjunction,
and the restricted-cohomology and evaluation comparisons. They do not state the compatibility
of the constructed derived pullback with the zero and shifted-single comparisons. The
original one-step proof plan combined those two calculations with naturality; this delivery
separates precisely the missing calculations and implements the naturality step.

Read Stacks Tags 07A6 (derived adjunction), 0D6F (localized cohomology), and 03Q8
(higher-direct-image presentation). These supply the source framework; the detailed
comparison calculations are expansions of the parent's proof plan, not quotations of
an exact theorem in those tags. Their docstrings explain the injective-resolution and
single/shift calculations needed next. Local literature files are absent on this machine,
so the cited Stacks pages were read online. The sites-cohomology TeX source was
then obtained in the sandbox scratchpad to check the labels `lemma-adjoint`
(07A6) and `lemma-unbounded-cohomology-of-open` (0D6F).

Searches were run through msearch.py (LeanSearch unavailable with HTTP Internal Server
Error; Loogle naturality; LeanFinder pullback/naturality and shift/Leray queries; grep),
and by rg in both library roots. The generic ingredients exist, including
`RightDerivedSingleUnitHomologyComparison` and the shift compatibility infrastructure in
`RightDerivedFunctor.AdjunctionShift` and `Etale.Derived.LowerShriekBaseChangeShift`;
none states either complete restricted comparison. The blueprint search for derived
sections and shift comparisons found no duplicate of these new statements.

## New nodes

`lem-sbc-restricted-derived-section-zero-comparison`, in
`Sheaf.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison`, records the degree-zero
comparison. The module also holds the explicit derived section natural transformation
needed by both comparisons. Its proof is the parent's degree-zero comparison step,
expanded through the defining right-derived units and Leray comparison.

`lem-sbc-restricted-derived-section-shift-comparison`, in
`Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison`, records the comparison
on shifted single sheaves with the explicitly defined restricted cohomology map. Its
proof is the parent's shifted-single comparison step, expanded through shift compatibility,
localization factorization, and the inverse-image composition comparisons.

No existing interface was changed and no forced adaptation or change record is needed.

## Second reading by G3

1. Interface: compared the complete item with the repository using diff. The only
   changes are the private shift-comparison import and the body of
   `restrictedDerivedEvaluation_pullback`. Its signature, `Hzero`, `transportZero`,
   and `pullbackHom` are byte-for-byte unchanged. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`. No target or existing interface changed.

2. Kernel and constructions: compiled all three modules in dependency order with
   lcompile.py (8.1, 5.2, and 15.6 seconds), without errors or warnings. Inspected
   every declaration and scanned for forbidden declarations and overlong lines.
   The only two sorries are the entire public zero and shift comparison proofs
   listed above. A scratch copy with #print axioms checked all nine declarations:
   all six constructions use only propext, Classical.choice, and Quot.sound;
   the three theorems additionally use sorryAx, as expected for this decomposition.
   In particular, none of the three new constructions depends on sorryAx.
   The Leray comparison is characterized by the right-derived universal property,
   not by an arbitrary existence witness. The main proof applies naturality at t,
   uses the zero and shift component equations, and cancels alpha with alpha-inverse
   using e.hom followed by e.inv and the single-comparison inverse.

3. Split statements: read both signatures, docstrings, and node records against
   the definitions of rawAffineComplexPullback, rawAffineRestrictedCoefficient,
   zeroIso, and shiftIso. The zero lemma permits an arbitrary coefficient map psi;
   it identifies the derived adjunction unit and Leray map with ordinary sections.
   The shift lemma computes just the component at F[0][p], including the shift,
   single, and restricted coefficient comparisons. Neither asserts naturality at
   an arbitrary derived t, and neither has the source identification e: these are
   strict component calculations, not renamed copies of the parent square.
   Checked the restriction comparison direction explicitly: q-star r-star goes
   via upperStarComp(q,r).inv, then upperStarComp(r-prime,a).hom, exactly as the
   coefficient definition requires. For p=0 the shift comparison removes the zero
   shift; a zero coefficient map makes both sides zero by additivity; for an empty
   restricted scheme both section groups vanish. Identity maps use the same
   canonical composition comparisons on both sides. No invertibility of psi or
   phi, affineness of U, or nonemptiness is assumed or used.
   Read Stacks [07A6](https://stacks.math.columbia.edu/tag/07A6),
   [0D6F](https://stacks.math.columbia.edu/tag/0D6F), and
   [03Q8](https://stacks.math.columbia.edu/tag/03Q8), and checked the labels
   lemma-adjoint and lemma-unbounded-cohomology-of-open in the scratch TeX source.
   These justify the derived-adjunction and restriction framework; they do not
   state these exact Lean comparison equations. The docstrings correctly supply
   the remaining calculation rather than claiming an exact quoted theorem.
   Independent msearch queries used "Derived adjunction pullback on sheaf cohomology
   compatible with single complexes and shifts" (LeanFinder: eight sheaf-of-modules
   ingredients, no match), CategoryTheory.Functor.rightDerivedZeroIsoSelf (Loogle:
   the zero comparison and inverse identities, no restricted square), and
   homologyRightDerivedFunctorObjSingleFunctorIso|rightDerivedFunctorCompUnit|
   mapDerivedCategoryCompIso (grep: zero hits). Local rg over both library roots
   and upstream found no duplicate. Read RightDerivedSingleUnitHomologyComparison
   and RightDerivedFunctor.Comp: these give a unit calculation and the Leray
   construction, not either complete component equation. Neither split can be
   closed by a direct application of these declarations in a few minutes.

4. Route and pruning: the shortest remaining parent argument is the implemented
   naturality and cancellation calculation. The main module needs its public raw
   comparison import for its signatures and its private shift import for proofs.
   Both new public imports are needed for new signatures or construction bodies.
   Read dag/units/sk-lem-failure-field.json: its realized statement and step lists
   are empty, and this delivery changes no unit record or unit route. The original
   five dependency nodes are all retained below the comparison nodes:
   def-weil-pbc-inverse-image, lem-weil-pbc-inverse-image-composition,
   prop-weil-pbc-derived-inverse-image-adjunction,
   def-sbc-raw-restricted-cohomology-comparison-map, and
   def-sbc-raw-affine-restricted-cohomology. They supply the actual constructions
   and the comparisons being computed; none is no longer needed. No imports or
   modules are pruned. This remains one closed parent hole and two added holes,
   a decomposition with net hole change -1, not a sorry-free proof.

5. Nodes: checked that each proof_deps list is the union of step citations and
   that the parent uses the zero equation, shift equation, and naturality exactly
   as its three steps record. New nodes have source, complete proof sketches,
   actual recorded searches, creation metadata, blueprint ancestry, matching
   chapter/unit, and Lean records. Corrected both new lean.statement fields from
   whitespace-flattened signatures to the verbatim multiline Lean signatures.
   No mathematical statement, proof, construction, or import required repair.

Second reading changed only the two new node signature records and this report.
The compiled proof is accepted as a decomposition; the two component calculations
remain explicitly open.
