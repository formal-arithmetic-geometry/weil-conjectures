# Q06: lem-sfb-polynomial-derived-bar-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-derived-bar-comparison.json`: item, statement, now split into seven steps; statement and statement dependencies unchanged. Existing Mathlib searches retained and five fresh searches added.
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-translation-acyclic.json`: new statement-only analytic lemma; unsplit, no Mathlib match. Polynomial direct sums with simultaneous lattice translation and arbitrary finitely many spectator variables are acyclic for internal derived invariants.
- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-resolution-bar-normalization.json`: new statement-only formal lemma; unsplit, no Mathlib match. An augmentation-preserving map from an equivariant resolution into the homogeneous bar gives the normalized derived-invariants arrow, even without acyclicity of the bar terms.
- `citations.json`: exact statement quotations for all six step/node pairs.
- `searches.jsonl`: fifteen actual msearch records; retained without alteration. The JSON search entries copy these actual records and their query strings.

No Lean source, repository file, launcher file, unit record or chapter record was written. Mathematical formula checks are in the sandbox's `check_formulas.py`; they use integer polynomial substitutions, not Lean or a compiler. No earlier split/report/search log existed in this sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for polynomial/bar, lattice and translation-resolution notions. No project declaration states the item or the new lemmas. Mathlib's `Rep.standardComplex` is an abstract group representation resolution, not this internal condensed comparison. Upstream sorry declarations were not treated as proofs.

## WANTED

WANTED: an exact reference for internal derived-invariant acyclicity of the polynomial translation direct sum over all-continuous norm-topological E and noncomplete Omega, for `lem-sfb-polynomial-translation-acyclic`. The complete-coefficient Mahler theorem alone does not supply it.

WANTED: an exact reference for the homogeneous internal bar/derived-unit normalization equation in `lem-sfb-equivariant-resolution-bar-normalization`. Its formal ingredients are the existing internal bar comparison and derived-unit naturality; the blueprint does not supply this equation.

## Source, route and issues found

Read the current main-20261015 direct-images proof paragraph (3) named in the item's source, the chapter record `sec-six-functors-basics`, the unit record `sk-thm-sf-ctf-stability`, and the parent split `lem-sfb-trivial-ladic-derived-exterior`. Paragraph (3) delegates the open-coefficient calculation; it does not prove a polynomial comparison. The item already labels the exact analytic reference WANTED. Accordingly this split is honestly agent-written; it claims neither a sourced proof of the analytic lemma nor a finished analytic result.

For the homological input I read Stacks Tag 015E, `derived.tex`, `lemma-leray-acyclicity` (including the bounded-below proof), and Tag 0156, `section-right-derived-functor`, especially `lemma-injective-acyclic`. Only the existing `sk-thm-acyclicity` is used for Leray's lemma. No Stacks tag is represented as proving the analytic assertion. I also converted the local Scholze Six-Functor Formalisms PDF to text and inspected its coefficient discussion; it does not provide the exact noncomplete polynomial-translation assertion. No SGA source is cited.

The generic acyclic-resolution lemma `sk-thm-acyclicity` is declared as a tool use in `split_report.tool_uses`: it supplies formal homological algebra, not a replacement route. The two new lemmas remain inside the item's unit. `blueprint_refs.py ancestor` returns None, which is inherited from this created-node chain; the existing null ancestor was retained, with the full via chain and precise paragraph places. The item is not the unit key theorem, so no unit realization fields were changed.

No statement dispute was found in this item. In particular no completeness hypothesis, finite-subextension-valued replacement, underived-column acyclicity assertion or conclusion about cohomology only was added. The analytic content was isolated rather than justified by a completeness assumption that Omega lacks.

## Not duplicates

Whole-DAG keyword searches and `blueprint_refs.py search` were made for polynomial, polynomial cochain, polynomial translation, derived bar, homogeneous, acyclic resolution, translation and resolution comparison. The searches found no existing statement of either new fact. Search hits and actual verdicts were read, including Mahler's `CompleteSpace` hypothesis and the abstract module coefficients in `Rep.standardComplex`.

- lem-sfb-polynomial-translation-acyclic vs lem-sfb-polynomial-derived-bar-comparison: the new lemma is about higher invariants of a nontrivial polynomial translation representation, with spectator variables; it states no polynomial-to-bar comparison, no exterior cohomology and no claim about trivial-coefficient derived objects. The item now constructs the resolution, proves its exactness, computes its invariants and identifies the actual arrow.
- lem-sfb-polynomial-translation-acyclic vs lem-sfb-rational-polynomial-bar-contraction: the latter is an algebraic contraction of the invariant additive polynomial bar over any Q-algebra; the new lemma concerns acyclicity before taking invariants in an internal lattice action category. Neither supplies the other by a one-line specialization.
- lem-sfb-polynomial-translation-acyclic vs lem-sfb-dense-lattice-derived-invariants-comparison: the latter concerns finite-dimensional continuous representations and its proof depends on the parent of this item. Our polynomial direct sum is unbounded in degree and is not finite dimensional. Citing that ancestor would create a cycle.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-condensed-derived-invariant-bar: the bar node gives a normalized isomorphism from derived invariants of a module, but does not state the equation for an arbitrary equivariant resolution K mapping to the underived homogeneous bar. The new lemma gives this arrow equality, without asserting that it is an isomorphism.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-resolution-inflation-comparison: the latter is for projective resolutions of integral abstract group modules and only per-degree inflation maps. It does not cover internal A-modules, arbitrary equivariant cochain resolutions or the derived internal bar equation.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sfb-internal-bar-ordered-cup: the latter treats the cocycle made from an ordered list of additive characters and compares cup products; the new lemma concerns arbitrary resolutions and augmentation-preserving evaluation, with no cup assertion.
- lem-sfb-equivariant-resolution-bar-normalization vs lem-sp-derived-injective-resolution-naturality: the latter assumes specified injective resolutions and gives naturality between their derived-object computations; the new lemma identifies the map from a possibly noninjective equivariant resolution into an internal homogeneous bar.

Neither new source carries a Stacks tag shared by existing nodes: both are explicitly agent-formulated sub-obligations under paragraph (3), with exact references WANTED. The existing generic Stacks result is reused, not duplicated.

## Review by Q06

I reviewed delivery-errors B through E, both copies, against the actual JSON and the sources. Every new node introduces its ring, group, variables, action, topology and universes, and cites the definitions it uses. Both are statement-only with empty proof and proof dependencies. Neither is an elementary fact or a clause of the item's trivial-coefficient comparison. In particular the nontrivial translation representation is a smaller effacing object, and the normalization lemma supplies a formal arrow identity rather than the item's isomorphism. I wrote out the elementary polynomial arguments instead of making more nodes.

Step 1 cites the statement of `lem-sfb-condensed-derived-restriction-calculus` only for exactness detection after forgetting actions. That statement explicitly says kernels/cokernels are underlying ones and forgetting is exact and detects exactness. The finite substitutions, action law and cancellation for delta squared are written out in the step; polynomial and action definitions are already statement dependencies.

Step 2 has no non-elementary citation: insertion of zero contracts the augmented underlying complex. I checked the signs: deleting the inserted zero has sign +1, and all other terms cancel in pairs; in degree zero the remaining augmentation term is evaluation at zero. The contraction need not preserve actions, and the proof uses only exactness detection from step 1 to obtain the equivariant quasi-isomorphism. No projectivity of represented free modules is assumed.

Step 3 uses exactly the vanishing statement of `lem-sfb-polynomial-translation-acyclic`. The invertible polynomial coordinate change is explicit, and its r translation variables and nr spectator variables match that node. All required indices are nonnegative; F has exactly the permitted norm topology. The new node asserts acyclicity of the full direct sum, so there is no silent assertion that derived invariants commute with an unbounded filtered union. This is the analytic input still to be split below this delivery, and it was not replaced with the complete-field Mahler theorem.

Step 4 is a polynomial calculation. I checked the leading-coefficient argument over A(S), which can have zero divisors: multiplication by a positive integer remains invertible since F contains Q, so the conclusion does not require A(S) to be an integral domain. Invariance under the whole group implies invariance under the integer unit translations used; independence of the translated variables conversely gives invariance under all parameter-dependent translations. Internal direct-sum sections are locally finite polynomials; the argument is local and glues, so it does not assume every sheaf colimit is a naive sectionwise colimit. Consecutive differences give exactly the first, interior and last bar faces, including n=0 where the two terms cancel.

Step 5 cites `lem-sfb-condensed-derived-restriction-calculus` for the Grothendieck action category, left exact invariants and derived-functor properties, and the exact derived-object clause of `sk-thm-acyclicity` for the canonical comparison on a bounded-below acyclic complex. K is zero in negative degrees; step 3 verifies termwise acyclicity. Step 2 supplies a quasi-isomorphism in the correct action category. These hypotheses make both factors defining c invertible. I did not use a bare list of cohomology isomorphisms to identify a derived arrow.

Step 6 cites the full equality of `lem-sfb-equivariant-resolution-bar-normalization`, after checking N=A with trivial action, the equivariant quasi-isomorphism a and the evaluation map e. I checked continuity with a varying profinite parameter, equivariance, deletion compatibility, and preservation of the constant augmentation. The specified homogeneous tuple in additive notation has consecutive differences g_1,...,g_n, so rho is the precise evaluation map in the item, without an arbitrary choice of an isomorphism. `lem-sfb-condensed-derived-invariant-bar` is used for epsilon being an isomorphism, which its statement supplies. The new normalization lemma carries the formal comparison theorem explicitly instead of hiding it in the word 'canonical'.

Step 7 checks the trivial group r=0 explicitly. Then all variables disappear, the polynomial terms are A, invariants are the identity and the constant cosimplicial contraction is the same inserted-zero calculation. Empty parameter sets, zero coefficients and zero spectator variables introduce no exception. Rank one and two were checked with the formulas below. No step exceeds 2000 characters.

For the analytic new lemma I checked r=0 (invariants identity), m=0, and r=1 where polynomial antidifferences are finite rational polynomials; the latter is a plausibility check, not a claimed proof of internal derived acyclicity. I did not infer internal vanishing merely from ordinary cohomology on the one-point parameter. For the formal new lemma I checked G=1, N=0 and K=N[0] when G=1: its equation reduces to naturality of the derived unit with the constant augmentation. The underlying homogeneous complex is contracted by insertion of the identity. A route for its later proof is evaluation into the homogeneous bar of one equivariant injective resolution: forgetting preserves injectives by the flat represented-free-module induction adjunction already exposed in the bar node, and homogeneous coinduction preserves injectives as the right adjoint of exact forgetting. This gives the equivariantly injective total resolution on which the equation is derived-unit naturality. This proof plan is in the report, not in the new statement.

Exact integer-coefficient checks in `check_formulas.py` passed 132 monomials for the inserted-zero homotopy (r=0..2, cochain degree 0..3, total polynomial degree at most 2), including the augmented degree-zero identity. Separate symbolic linear-coordinate checks passed every deletion/addition face for r=1..2, n=1..3. These checks verify the finite algebra only; they do not certify the analytic new lemma. An initial optional SymPy invocation found that package unavailable; I replaced it with a dependency-free integer polynomial check, without installing anything.

The citations file contains verbatim statements, with each use justified above. The proof dependency list is exactly their union. I checked no new node depends on the item or its parent and that no cyclic ancestor comparison was cited. I preserved all imported metadata, the item statement and its statement dependencies. All new searches have actual msearch records; none was invented, and none of the services used was unavailable.

## Unfinished below this one-level split

The two new statement-only obligations remain unsplit, as required. In particular this delivery does not certify the analytic incomplete-coefficient theorem. The complete proof of the item is conditional on those named DAG lemmas, with all remaining non-elementary inputs exposed.

## Validation

The required server `review_split` check passed before this report was written. The final combined delivery dry run is run after this report; its result is recorded below when it exits.

Combined dry run exited successfully: `OK (not pushed) deliver/Q06/lem-sfb-polynomial-derived-bar-comparison at 26ae30de9fe: preflight passed`. The push command performs preflight again with this validation note included.
