## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianAffineDimOneOpen` states
`AlgebraicGeometry.isAffineOpen_spec_of_isNoetherianRing_of_topologicalKrullDim_le_one`.
Its sole proof is `sorry`; it introduces no definitions or helper statements.

The previous worker confused completion of stage 1 with completion of stage 2:
the Q06 merge at coord/ledger.md:38834 split the proof plan and introduced a
proof prerequisite, but the item still has no `lean` field. This delivery changes
only that field and supplies its statement module.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- “A commutative ring” is `(A : Type u) [CommRing A]`, with an explicit universe.
- “Noetherian” is `[IsNoetherianRing A]`, whose definition is Noetherianity as a
  module over itself, equivalently every ideal finitely generated.
- “X = Spec A” is substituted throughout as `Spec (CommRingCat.of A)`; there is
  no independently quantified scheme or additional identification to assume.
- “Topological Krull dimension of X at most one” is
  `(hdim : topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 1)`. Mathlib's dimension
  is valued in `WithBot ℕ∞`, defined from chains of nonempty irreducible closed
  subsets, exactly as the recorded dependency requires.
- “Every open subscheme U ⊆ X” is the unrestricted binder
  `(U : (Spec (CommRingCat.of A)).Opens)`. Its induced open scheme is Mathlib's
  `U.toScheme`; every open subscheme is represented this way, up to its canonical
  isomorphism over X.
- “Is affine” is `IsAffineOpen U`, defined in Mathlib as `IsAffine U.toScheme`.
- “Including the empty open” is covered by `U = ⊥`; no nonemptiness, domain,
  reducedness, field, smoothness, or finite-type assumption occurs.

Statement dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`, module
  `Mathlib.RingTheory.Noetherian.Defs`; also read `isNoetherianRing_iff` and
  `isNoetherianRing_iff_ideal_fg` at lines 192–205.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, module
  `Mathlib.AlgebraicGeometry.Scheme`; the scheme definition's local-affine
  presentation and its docstring were read.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, same
  module, lines 469–480. `Spec (CommRingCat.of A)` is the specified affine scheme.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`, module
  `Mathlib.Topology.KrullDimension`, lines 35–40.

The statement additionally uses Mathlib's existing `IsAffineOpen`/`IsAffine`
from `Mathlib.AlgebraicGeometry.AffineScheme`, read at lines 58–60 and 250–252;
these implement affineness and the induced open subscheme in `def-pc-scheme`.
The module imports the recorded modules of the stated proof dependencies as
ordinary imports and includes all seven proof steps, with their node names, in
the theorem docstring. `lem-a1-open-dimension-one-higher-image-vanishing` has no
recorded declaration or Mathlib match yet: it is a proof-only prerequisite and
is named in the docstring; no premature import or duplicate statement is added.
The missing local upstream source for the pushforward theorem was read with
`scompile.py --source WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`;
it supplies exactly the recorded qcqs quasi-coherent-pushforward theorem.

Source checked: `literature/stacks-project/varieties.tex`, label
`lemma-open-in-affine-curve-affine` (Tag 09N9), lines 7772–7794. It assumes an
affine scheme with Noetherian local rings of dimension at most one and a
quasi-compact open. The node is explicitly its Noetherian affine specialization:
Noetherianity of A supplies quasi-compactness of every open and Noetherianity
of stalk localizations; the global dimension bound supplies the local bounds.
No correction to the node is needed.

Edge cases checked before writing: `U = ⊥` (empty affine scheme), `U = ⊤`
(the original spectrum), the zero ring (empty spectrum of dimension bottom),
Artinian rings (dimension zero), and nonreduced or reducible Noetherian rings
of dimension one. All are admitted. The dimension bound is an inequality,
not equality, so zero-dimensional and empty spectra remain included.

Searches for an existing statement:

- `msearch.py ... leanfinder` query “Every open subscheme of a Noetherian affine
  scheme of topological Krull dimension at most one is affine”: eight hits,
  including Noetherian spectrum/space results and the dimension-zero Artinian
  criterion, but no affine-open theorem under this dimension-one hypothesis.
- `msearch.py ... loogle` query
  `AlgebraicGeometry.IsAffineOpen, topologicalKrullDim`: zero hits.
- `msearch.py ... leansearch` query “Every open subset of the spectrum of a
  Noetherian ring of Krull dimension at most one is affine”: eight hits,
  including `IsAffineOpen`, basic opens, `isAffine_Spec`, and Noetherian
  components. No theorem covers arbitrary opens in this setting.
- `msearch.py ... grep` query
  `open_in_affine_curve|09N9|[Aa]ffine.*[Oo]pen.*[Dd]imension`: zero hits.
- Direct `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and Mathlib
  for the node id, `open_in_affine_curve`, `09N9`, and affine/dimension name
  patterns found dimension invariance on affine opens, affine complements of
  integral curves, and dimension-zero affineness, not the desired theorem.
  A further search for `isAffineOpen_of.*[Nn]oether` and
  `isAffineOpen_of.*[Dd]im` found no existing declaration. No new notion is needed.

No STATEMENT-DISPUTED flag or mathematical node fault.

## Second reading by NN

Independent maintainer reading, 2026-10-18, of immutable delivery
c3b1f0164bf230f303425aaa0fa43c592b7572d0. This replaces the original
same-worker second pass with the completed independent reading.

I read packet.md, check-brief2.md in full, the item JSON, all four statement
dependency JSON records, the actual delivered module and this report. I read
Stacks varieties.tex:7744–7794 (Tags 09N8 and 09N9) and the exact Mathlib
source declarations and docstrings used by the signature.

Clause-by-clause verdicts:

- `(A : Type u) [CommRing A]`: precisely an arbitrary commutative ring;
  `u` is explicitly bound and unrestricted. PASS.
- `[IsNoetherianRing A]`: the recorded Noetherian-ring notion, defined as
  `IsNoetherian A A`, equivalent to finite generation of all ideals by
  `isNoetherianRing_iff_ideal_fg`. PASS.
- `Spec (CommRingCat.of A)`: the actual affine spectrum, using the recorded
  `AlgebraicGeometry.Spec` in `Mathlib.AlgebraicGeometry.Scheme`. PASS.
- `topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 1`: precisely the required
  topological dimension bound, using chains of nonempty irreducible closed
  subsets and values in `WithBot ℕ∞`. PASS.
- `(U : (Spec (CommRingCat.of A)).Opens)`: every open with its induced scheme,
  without any extra quasi-compactness or nonemptiness binder. PASS.
- `IsAffineOpen U`: Mathlib's affineness of that induced open scheme; hence
  exactly the conclusion. PASS.

The source assumes Noetherian local rings of dimension at most one and a
quasi-compact open in an affine scheme. The seven-step docstring correctly
verifies these hypotheses in the stated specialization: Noetherian topology
makes all opens retrocompact and quasi-compact; localized stalks are Noetherian;
chains computing stalk dimension are among the global chains. Then 09N8,
qcqs quasi-coherent pushforward, affine vanishing, Leray and the quasi-compact
H1 criterion give affineness. The diagonal argument correctly establishes
quasi-separatedness. No source hypothesis has been lost.

Edge cases: empty and whole opens, the zero ring (empty spectrum with bottom
dimension), dimension zero, nonreduced and reducible dimension-one rings,
and arbitrary ring universe are all included. There is no extra domain,
field, separatedness, finite-type, smoothness or reducedness hypothesis.

The four recorded statement dependencies are used directly, with no private
notions or hollow definitions. There is precisely one theorem, with proof
`by sorry`; all variables are bound, autoImplicit is disabled, no line exceeds
100 characters, and both module and theorem docstrings give the source place
and blueprint id. The theorem docstring contains all seven proof steps.
The JSON `lean.statement` equals the file signature verbatim.
The higher-image vanishing lemma is only a proof dependency: no missing notion
or interface prevents stating this theorem, so no extra helper is required.

I independently searched the Mathlib algebraic-geometry tree, upstream
WeilConjectures and project lean/Sheaf for affine-open/dimension/curve patterns,
09N9, the item id, and dimension-at-most-one bounds. Nearby statements concern
dimension zero or integral/proper curves and do not duplicate this statement.
The worker records LeanSearch, LeanFinder, Loogle and textual searches.
An additional independent LeanSearch request returned HTTP 403; it is recorded
as unavailable, not as a negative mathematical search result.

The available origin/newtargets-dag route-pivot dropped list contains none of
the item's statement or proof dependencies; no item-specific repair note
exists there. The proof uses ordinary sheaf cohomology and no dropped machinery
or pro-etale substitute.

Compiler reproduction: invoked
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NN lem-a1-affine-curve-open-affine snapshot/lean/Sheaf/AlgebraicGeometry/NoetherianAffineDimOneOpen.lean`.
Exit code 0; sandbox check 3.1 s, library-path check 5.2 s; no diagnostics.
The currently installed wrapper sends the immutable source to its server-side
private overlay (`/dev/shm/nt-tmp/nt-local-compile-a7etcm56/.lbuild`) and confirms
the library-path compile. It is not the locally running lcompile wrapper
mentioned in the brief; no manual SSH or alternative build was used.
The delivered report had no saved per-file compiler transcript, so this is
fresh reproducibility evidence rather than confirmation of an archived log.

Finding and correction: the original section explicitly described a second
pass by the same worker. Under H11 and brief-stage2 §6 that did not document an
independent reading. This complete replacement report records the independent
review actually performed and adds the compiler evidence. No Lean or node
correction is needed. No mathematical defect was found.
