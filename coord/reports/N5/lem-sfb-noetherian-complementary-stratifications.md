## Worker report

Stage-2 repair of the returned delivery c33ad70c655f. The module
`Sheaf.AlgebraicGeometry.NoetherianComplementaryStratifications` states
`AlgebraicGeometry.Scheme.noetherian_complementary_stratifications`, with exactly one
postponed proof, `by sorry`. It defines no notion and proves no lemma. Its module and
theorem docstrings identify main-20261015
`sk-lem-integral-models/sk-lem-integral-models-operations.proof.md`, paragraph (3).
The theorem docstring carries all eight reviewed proof steps and their dependency nodes.
I read that blueprint paragraph and Stacks topology.tex, labels
lemma-Noetherian-quasi-compact (04ZA) and lemma-constructible-Noetherian-space (005L).

Return H1 repaired: the packet now contains the Lean module, its complete verbatim
signature in the node's lean record, this stage-2 report and the second-reading section.
Return H2 repaired: the node was restored from the current live read clone before adding
lean. The eight Q06-reviewed proof steps, proof_deps, proof_origin, split_report,
mathlib_searches, reviewed record and all other fields are preserved. Neither statement
nor stmt_deps changes. In particular the old four-step replacement is not delivered.
The delivery wrapper rebases the packet on the current server branch.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary schemes are `{T U Z : Scheme.{u}}`, with the universe explicitly bound.
  No finite-type-over-a-field, reducedness, separatedness or nonemptiness is assumed.
- Noetherian T, explicitly meaning locally Noetherian and quasi-compact, is precisely
  `[IsLocallyNoetherian T] [CompactSpace T]`. Mathlib's `IsNoetherian` extends exactly
  those two classes; I read its definition in Noetherian.lean.
- The specified maps are `(j : U ⟶ T) (i : Z ⟶ T)` with `[IsOpenImmersion j]` and
  `[IsClosedImmersion i]`. Complementarity is `hji : Set.range j = (Set.range i)ᶜ`,
  in the orientation of the node. Scheme.Hom coercions are the maps on points.
- Noetherianity of all three schemes is the first three conjuncts
  `IsNoetherian T ∧ IsNoetherian U ∧ IsNoetherian Z`.
- Each scheme's qcqs assertion is the separate pair `CompactSpace W ∧ QuasiSeparatedSpace W`
  for W = T, U, Z. This topological quasi-separatedness is scheme quasi-separatedness,
  as identified by `quasiSeparatedSpace_iff_quasiSeparated`.
- Every subset, with no openness or constructibility restriction, is covered by
  `∀ A : Set T, IsCompact A`. This is quasi-compactness without a Hausdorff condition.
- The asserted quasi-compact morphism is `QuasiCompact j`. Its Mathlib definition tests
  preimages of compact opens and implies the affine-open formulation in the node.
- The first universal clause takes every `S : FiniteLocallyClosedStratification U`.
  This is the exact recorded def-constructible-stratification interface: finite locally
  closed, disjoint, covering strata with domain schemes, immersions, and prescribed ranges;
  constructibility of input strata is not an extra hypothesis.
- It produces `R : FiniteLocallyClosedStratification T` and a bijection
  `e : Fin (S.n + 1) ≃ Fin R.n`. Thus the output consists of exactly the old finite family
  plus one complementary stratum, with no additional strata hidden in the existential.
- For every a, the dependent pair of `R.domain (e a)` and `R.immersion (e a)` equals
  `Fin.snoc` of the old pairs `⟨S.domain b, S.immersion b ≫ j⟩` with last pair `⟨Z, i⟩`.
  Mathlib `Fin.snoc_castSucc` and `Fin.snoc_last` express the first entries and last entry.
  Equality of these dependent pairs retains the actual domain schemes and maps, including
  nilpotents, not merely the same topological images or abstractly isomorphic schemes.
  `S` itself is unchanged; its maps into U are used in the actual composites.
- `∀ a : Fin R.n, Topology.IsConstructible (R.stratum a)` explicitly states constructibility
  of every resulting stratum, including the complement. Local closedness, immersion,
  disjointness and coverage are fields of R, and range_immersion identifies the images.
- The second universal clause repeats precisely these assertions for every stratification
  of Z, with old composites `S.immersion b ≫ i` and last pair `⟨U, j⟩`. The input maps
  into Z and all original source schemes are retained, and every output image is constructible.
- There is no nonempty-stratum field and no assumption `0 < S.n`. Thus empty strata,
  empty complementary schemes and the cases n=0 or m=0 remain included.

Recorded dependency declarations reused, with their full source signatures and docstrings read:

- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; its affine-cover and open-immersion interfaces
  confirm agreement with the node's locally Noetherian notion.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`;
  `IsCompact` in the same module is used for arbitrary subsets.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; the immersion interface is in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- def-weil-pbc-scheme-conventions is a convention record with no separate declaration.
  Quasi-separated spaces are `QuasiSeparatedSpace`, from Mathlib.Topology.QuasiSeparated.
- def-weil-finite-type-morphism: the recorded `AlgebraicGeometry.QuasiCompact`, in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; finite type is not assumed here.
- def-constructible-stratification: `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` and its topological parent.
- def-weil-constructible-subset has no lean record and needs none: its Mathlib match is
  `Topology.IsConstructible`, from `Mathlib.Topology.Constructible`, the Boolean algebra
  generated by retrocompact opens. No replacement definition was introduced.

All applicable proof inputs are already in the Mathlib imports: open-subscheme
Noetherianity, locally finite type immersion permanence, locally Noetherian
quasi-separatedness, immersion composition and locally closed images. The composite
statement is not assumed as a dependency of itself. No new nodes or dependency modules.

Searches before writing:

- msearch.py leanfinder: "For a Noetherian scheme complementary open and closed immersions
  extend any finite stratification by adjoining the complementary scheme, giving
  constructible strata". Eight hits included IsNoetherian.noetherianSpace,
  finite_irreducibleComponents_of_isNoetherian, IsLocallyNoetherian.quasiSeparatedSpace,
  and constructible-set induction; none states all clauses of this node.
- msearch.py loogle: "AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.QuasiCompact".
  Successful query, zero hits.
- msearch.py grep: "stratification|noetherianSpace" in AlgebraicGeometry/Noetherian.lean.
  Five hits, all Noetherian-space ingredients, no composite statement.
- rg on lean/WeilConjectures and lean/Sheaf for openClosed, Noetherian stratification,
  complementary stratification; grep for the item id in lean/WeilConjectures.
  The relevant existing construction is `Scheme.Stratification.openClosed` in
  `WeilConjectures.ConstructibleSheaf.OpenClosed`, read in full with its surrounding
  binders and its input definition in `WeilConjectures.ConstructibleSheaf.Defs`.
  It requires QuasiCompact j and already constructible input stratifications, and supplies
  concatenation only. It does not establish the Noetherian/qcqs/compact-subset conclusions
  or accept the recorded general locally closed stratification interface. It can be used
  in a future proof after supplying constructibility and converting the input interface;
  recording it as existing:true for this entire node would omit multiple conclusions.
- rg for noetherian_complementary_stratifications in both library roots and
  dag/lean_names_upstream.json: no prior declaration. The other library hits concern
  constructible sheaves and use openClosed, not this exact statement.

Edge-case reading before writing: T empty forces U and Z empty by injectivity; all
assertions remain meaningful. U empty with n=0 gives a singleton output consisting of
its given complementary Z. Z empty with m=0 gives just the given U. With empty strata
already present, Fin.snoc adds rather than discards the complement, even when it is
empty. For U=T the empty closed scheme retains its given structure; for Z=T the open
scheme is empty. A nonreduced closed complement is retained as the exact scheme Z,
not replaced by a reduced closed subscheme. A DVR with its generic open and closed point
has two distinct retained strata. No finiteness hypothesis beyond the input finite
stratification is imposed. No statement dispute or source correction was needed.

Validation: scompile.py compiled both its sandbox probe and the named library module
cleanly (1.6 seconds each), with no non-sorry warning. The initial elaboration errors
were repaired by explicitly specifying the constant dependent family parameter of
Fin.snoc. Every theorem proof remains sorry. The delivery dry run recompiles the final file.

## Second reading by N5

The worker delivers directly under the current launcher instructions; no other agent
was started, and the maintainer performs the independent review. This section records
a separate in-session rereading of the node, declaration and restored metadata, not a
claim of an independent second worker review.

I matched the two Noetherian hypotheses and complementary immersion hypotheses against
all binders, and checked each conjunct listed above. In particular the arbitrary-subset
quantifier is not restricted to locally closed subsets; qcqs appears for T as well as U
and Z; both universal extension clauses are present; and both last dependent pairs use
the originally supplied complementary schemes and morphisms. The finite index equivalences
force exactly S.n+1 output entries, including when S.n=0. The structure fields enforce
covering and disjointness, while separate IsConstructible clauses enforce constructibility
for every output image. No nonempty condition excludes empty strata. The recorded signature
was extracted verbatim from the theorem keyword to its proof separator.

I checked the full openClosed construction: its domain and immersion fields use actual
composites, consistent with our equalities, but its input is more specialized than the
recorded FiniteLocallyClosedStratification, so it is not substituted for that dependency.
No mathematical mismatch remained. The two dependent-family elaboration annotations were
added; the final formatting only indents the lambda bodies. All original eight proof
steps and every other non-lean field match the current read-clone node exactly.
