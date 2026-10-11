## Worker report

The module defines `HasProjectiveResolutionLE` using `ComposableArrows.Exact`, endpoint zero modules, and `Module.Projective`, then states the three requested padding and least-bound clauses with `sorry`.

The endpoint modules are `ModuleCat.of R (Fin 0 → R)`, a canonical zero module. The sequence has `n+3` arrows and objects indexed 0 through n+3; projective terms are indices 1 through n+1, the module is at n+2, and the terminal zero at n+3. The theorem's first clause quantifies the exact sequence data and yields the padded bound; clauses two and three state least natural-number bounds exactly as in the node.

Dependencies used: `CategoryTheory.ComposableArrows.Exact` from `Mathlib.Algebra.Homology.ExactSequence`, and `Module.Projective` from `Mathlib.Algebra.Module.Projective`; the new definition node records the projective-resolution notion needed by the statement.

Edge cases checked: n = 0, m = n, and zero modules are represented by the `Fin 0 → R` module; `Fin` bounds are discharged by `omega`.

Searches recorded in the item found no existing resolution-length notion in the pinned Mathlib or project; Mathlib's projective-dimension declarations are Ext-based and do not state this resolution notion.

## New nodes

The first worker added `def-weil-pbc-projective-resolution-length`. The second reader
dropped it and its module: the landed `def-weil-pbc-finite-global-dimension` already
carries precisely this notion. No new nodes remain in the delivery.

## Earlier second reading (a previous round; superseded)

The statement mirrors the three clauses and records all endpoint and projectivity hypotheses.

## Second reading by H1

Read the item JSON, both original sandbox modules, both dependency nodes and their
recorded Mathlib signatures, the landed GlobalDimension module and its node, and
Stacks algebra.tex Definitions 00O4/00O6 and the chapter's Conventions. The local
source copy is /home/ubuntu/c1-stacks-review/algebra.tex, with labels
`definition-finite-proj-dim`, `definition-finite-gl-dim`, and `section-conventions`.
Stacks explicitly defines rings to be commutative with 1 and includes the zero ring.
The item statement itself is correct; no statement correction was made.

Object/hypothesis/conclusion checklist (the node's statement, item by item):

- Commutative ring R: `∀ (R : Type u) [CommRing R]`. Corrected the original `[Ring R]`,
  which admitted noncommutative rings beyond the node and source conventions.
- R-module M: `(M : ModuleCat.{max u v} R)`, whose bundled carrier has exactly an
  additive commutative group and an R-module structure. No finite generation,
  Noetherian, nonzero-ring, characteristic or field hypothesis. Verdict: matches.
- Integers m ≥ n ≥ 0: `(m n : ℕ), n ≤ m →`. Nonnegative integers are naturals.
  Verdict: matches, with m and n in the node's order.
- Supplied exact projective resolution of M of length ≤ n: `∀ P :
  ProjectiveResolution M, (∀ i : ℕ, n < i → IsZero (P.complex.X i)) →`.
  The fields of Mathlib's `ProjectiveResolution` give projective terms and an
  augmentation quasi-isomorphism to M in degree zero. In ModuleCat this gives
  exactness in positive degrees and the exact augmentation onto M (read
  `complex_exactAt_succ`, `exact_succ`, and `isColimitCokernelCofork`). Its zero
  continuation is exactly a finite exact sequence 0 → P_n → ... → P_0 → M → 0.
  Conversely, extend any such finite sequence by zero terms to get this encoding.
  Verdict: matches the input sequence, with no extra mathematical assumption.
- Clause (1), putting zero terms at n < i ≤ m while retaining old terms/maps:
  `∃ Q : ProjectiveResolution M, Q = P ∧ (∀ i, m < i → IsZero (Q.complex.X i)) ∧
  (∀ i, n < i → i ≤ m → IsZero (Q.complex.X i))`. In the zero-continuation encoding
  the same resolution, truncated at the larger bound, is the padded sequence.
  `Q = P` retains its terms, differential and augmentation, and the last conjunct
  names exactly the newly included zero degrees. IsZero means canonically
  isomorphic to the zero module, independent of a chosen presentation of zero.
  All Q terms remain projective and the sequence exact by Q's structure fields.
  Corrected the original existential bound conclusion, which did not assert that
  padding retained the input sequence. Verdict: every part of (1) is present.
- Clause (2), if M has a resolution of length ≤ n: `ModuleCat.HasProjectiveResolutionLE
  M n →`; least nonnegative d: `∃ d : ℕ, ModuleCat.HasProjectiveResolutionLE M d ∧`;
  all k: `∀ k : ℕ, ModuleCat.HasProjectiveResolutionLE M k ↔ d ≤ k`.
  The equivalence includes minimality and upward closure, exactly as in the node.
  Verdict: matches, including quantifier order and both directions.
- Clause (3), existence of a finite uniform bound: `(∃ b : ℕ,
  Ring.HasGlobalDimensionLE.{u, max u v} R b) →`; least g attaining the bound:
  `∃ g : ℕ, Ring.HasGlobalDimensionLE.{u, max u v} R g ∧`; all k and both directions:
  `∀ k : ℕ, Ring.HasGlobalDimensionLE.{u, max u v} R k ↔ g ≤ k`.
  Opened `Ring.HasGlobalDimensionLE`: it quantifies over every object of ModuleCat,
  with no finiteness hypothesis. Verdict: matches.

Dependencies and the discarded new node:

`def-weil-pbc-exact-sequence` records `ComposableArrows.Exact` and also
`ShortComplex.Exact`; the original finite-arrow indexing was correct. The revised
encoding uses the exactness carried by the existing `ProjectiveResolution`.
`def-weil-pbc-projective-module` records `Module.Projective`. Read its split-free
surjection field and Mathlib `IsProjective.iff_projective`: it is equivalent to
categorical Projective in ModuleCat when R is small in the carrier universe.
Our carrier universe is max u v, so that condition is available without an extra
binder. The dependency notion is therefore the same projective-module notion.

Opened all six declarations recorded by `def-weil-pbc-finite-global-dimension` in
`Sheaf.RingTheory.GlobalDimension`. `ModuleCat.HasProjectiveResolutionLE` is a
resolution with zero terms above n, not the unrelated Ext-based projective
 dimension predicate. It is exactly the finite-resolution notion required here.
Its definitions contain no sorry data, and `Nat.find` defines the minima from the
existential hypotheses without a theorem hole. Added this landed node to stmt_deps
under STMT_DEPS MAY GAIN LANDED NODES (tools/stage2_delivery.py). No dependency
module is needed. The proposed new definition node duplicated this already-landed
notion and its DAG carrier, so both the new node and its module were removed.
Its source describes finite projective resolutions correctly, but H4/H12 require
reuse rather than a second predicate. The old Worker report remains above as the
record of what was submitted; its no-existing-definition conclusion is superseded.

Edge cases:

- n = 0 gives a projective degree-zero term mapping isomorphically onto M; higher
  terms are zero. Exactness at the left endpoint follows from degree-one exactness.
- m = n has no newly included degrees; Q = P and its existing bound suffice.
- M = 0 and the zero ring are included, with the all-zero resolution. No Nontrivial
  binder excludes either, and the minimum convention is d = g = 0 when appropriate.
- Empty bases and zero projective terms are allowed; Module.Projective includes the
  zero module. There is no index-family or scheme parameter whose empty case could
  be excluded, and no characteristic restriction.
- u and v are explicit arbitrary universes. Using max u v for module carriers
  includes modules at least as large as the ring, ensures categorical/projective
  agreement, and avoids vacuous tests over a universe too small for R. Larger
  carriers are covered by choosing v larger; smaller ones by their canonical lifts.

Independent searches (performed through msearch.py and direct rg):

- LeanSearch: `finite length projective resolution padding with zero modules`:
  service returned Internal Server Error; recorded unavailable, not evidence of
  absence.
- Loogle: `"ProjectiveResolution"`: ProjectiveResolution, its fields, self resolution,
  and unbounded HasProjectiveResolution/HasProjectiveResolutions. None is this
  three-clause statement.
- LeanFinder: `bounded projective resolution with zero terms above degree n and
  least global dimension`: Ext-based HasProjectiveDimensionLE/LT and dimension
  comparison lemmas; these are different notions, not usable as this statement.
- msearch grep: `HasFiniteResolution|resolutionLength|finiteProjective|
  projectiveResolution|globalDimension`: unbounded resolutions in the pinned
  Mathlib; no matching bounded-resolution/padding/minimum statement.
- Direct rg in repository lean/Sheaf and source WeilConjectures for
  HasProjectiveResolutionLE, HasGlobalDimensionLE, finiteResolutionOfLength and the
  theorem name found the landed GlobalDimension module (and its citers), but no
  existing copy of this theorem. Also checked dag/lean_names_upstream.json and DAG
  records: finite-global-dimension already carries the finite-resolution notion.

Changes: removed the duplicate predicate module and new definition node; reused
GlobalDimension and added its landed dependency; replaced Ring by CommRing;
made padding preserve the input resolution; generalized the universe encoding;
added the required copyright/module header and a docstring carrying all five
proof steps. Kept the item's mathematical statement and proof unchanged. The
lean.statement record is copied verbatim from the revised theorem signature.
No theorem was proved: the sole theorem still has proof `sorry`. No hollow
 definition, implicit variable or implicit universe was introduced. The revised
single module compiled on the server in 1.3 seconds with no errors or warnings.
