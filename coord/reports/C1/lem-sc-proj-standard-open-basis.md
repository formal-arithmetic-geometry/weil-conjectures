## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProjStandardOpenBasis.lean` states
`AlgebraicGeometry.Proj.isBasis_positiveDegree_basicOpen_and_isAffineOpen` with a
single `sorry` proof. No definitions, dependency modules, new nodes, or statement
corrections were needed.

Hypothesis and clause correspondence:
- A graded commutative ring S: `{S : Type u} [CommRing S]`, with
  `{σ : Type v} [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]`.
  This is Mathlib's full nonnegative grading interface, not a grading generated in
  degree one; `σ` has its own explicit universe. All variables and universes are bound.
- X = Proj(S): `(Proj 𝒮).Opens`, using Mathlib's scheme directly. An additional
  scheme variable and equality binder are unnecessary because X is introduced by
  definition in the node.
- Standard opens for positive-degree homogeneous f: the family
  `{U : (Proj 𝒮).Opens | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒮 d ∧ U = basicOpen 𝒮 f}`.
  Membership in `𝒮 d` expresses homogeneity, and `0 < d` expresses positive degree.
  Multiple representations of an open do not matter since this is a set of opens.
- They form a basis for the topology: `TopologicalSpace.Opens.IsBasis` of exactly
  that family, rather than of the larger family indexed by every ring element.
- Each D_+(f) is affine: the second conjunct is
  `∀ (f : S) (d : ℕ), 0 < d → f ∈ 𝒮 d → IsAffineOpen (basicOpen 𝒮 f)`.
  Both clauses apply to the same unrestricted graded ring.

Dependency declarations read and used:
- `def-nagata-affine-proj`: `AlgebraicGeometry.Proj`, module
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`; read its complete
  definition and the surrounding chart construction. Imported transitively by Basic.
- `def-pc-proj` (Mathlib leaf): `AlgebraicGeometry.Proj`,
  `AlgebraicGeometry.projIsoSpec` in that Scheme module, and
  `ProjectiveSpectrum.basicOpen` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology`. Read their docstrings
  and signatures. `AlgebraicGeometry.Proj.basicOpen` in Basic is the scheme-open
  wrapper of this same `ProjectiveSpectrum.basicOpen`, not a private definition.
- `def-nagata-homogeneous-localization-degree-zero`:
  `HomogeneousLocalization.Away`, module
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`. Read the abbreviation
  and `Away.mk` fraction constructor. The localization is not itself a binder of
  the node's conclusion, so its declaration occurs in the proof docstring; Basic
  imports it through Scheme and its `basicOpenIsoSpec` uses this exact localization.

The declaration docstring includes both DAG proof steps, naming clause (0) of
`lem-weil-pbc-proj-standard-open-inclusion` and the affine identification supplied
by `def-nagata-affine-proj`; it also explains the homogeneous-component and
positive-degree refinement argument from the source. No proofs were filled.

Edge cases checked before writing:
- Zero ring and rings concentrated in degree zero have empty Proj. No nontriviality
  hypothesis is added; the empty-space basis claim and affine empty opens remain valid.
- Zero and nilpotent homogeneous elements of positive degree are included; their
  opens are empty and affine. No nonzero or nonnilpotent hypothesis is added.
- Degree zero is excluded from the indexing family by `0 < d`, as the node requires.
- No hypothesis of Noetherianity, finite generation, generation in degree one,
  quasi-compactness, a field, or a characteristic is imposed. In particular the
  infinitely generated polynomial-ring example of Tag 00JP is allowed.
- Arbitrary ring and grading-representation universes are retained independently.

Searches (all made with group C1 and item lem-sc-proj-standard-open-basis):
- `msearch.py leanfinder "The standard opens of homogeneous elements of positive degree
  form a topological basis of Proj and are affine"`: eight hits, including
  `Proj.isBasis_basicOpen`, `Proj.isAffineOpen_basicOpen`, and affine open covers.
  Reading the actual source signatures shows that the basis theorem indexes all
  elements, while the affine theorem supplies only the second clause. No exact match.
- `msearch.py loogle "AlgebraicGeometry.Proj.basicOpen, TopologicalSpace.Opens.IsBasis"`:
  only `AlgebraicGeometry.Proj.isBasis_basicOpen`, whose family is the range over all
  elements, not positive-degree homogeneous elements.
- `msearch.py grep "isBasis|isTopologicalBasis|isAffineOpen_basicOpen"
  AlgebraicGeometry/ProjectiveSpectrum`: ten hits, confirming the unrestricted basis
  theorem and the positive-degree affine theorem, with no exact combined statement.
- `msearch.py leansearch "Homogeneous positive degree standard opens form a basis of
  Proj"`: unavailable, Internal Server Error; no search verdict assigned.
- `rg` of the upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `isBasis.*basicOpen|homogeneous.*basis|
  standard.*basis|lem-sc-proj-standard-open-basis`: unrelated affine-scheme basis
  uses and the existing consumer's docstring, no matching declaration.
- Reading Mathlib Basic, Topology, Scheme, and HomogeneousLocalization confirmed
  the complete interfaces and that no private notion is necessary.

Source verification: local Stacks sources are absent on this machine, so read
[Stacks Tag 00JP](https://stacks.math.columbia.edu/tag/00JP), especially (3)--(5),
and [Stacks Tag 01MB](https://stacks.math.columbia.edu/tag/01MB) directly. They
support exactly the positive-degree basis and affine-open assertions. The node's
source description mentions Algebra inside the constructions.tex record, but the
explicit tag/place identifies the intended lemma unambiguously; no node change
is needed. No STATEMENT-DISPUTED issue was found.

Validation: single-file server compile and delivery dry run are performed before
handing this sandbox to the independent second reader. The second reading is
intentionally left for that reader.

## Second reading by C1

Independent second reader, 2026-10-11. Opened the sandbox node and Lean module,
all three statement-dependency nodes and their actual Mathlib declarations, and
clause (0) of the proof-dependency node. No mathematical or Lean mismatch found;
the module and node record are retained verbatim. No new definition nodes,
dependency modules, or statement corrections are present or needed.

Source reading: the local Stacks checkout is absent. Independently read the raw
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
label `lemma-topology-proj` (Tag 00JP), including the preceding definitions, and
[constructions.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/constructions.tex),
section `section-proj` and label `lemma-proj-scheme` (Tag 01MB).
Also checked the rendered tags linked in the worker report. The constructions
section explicitly says standard opens always mean homogeneous positive-degree
ones. The source assumes only a nonnegatively graded commutative ring: no
Noetherian, finite generation, degree-one generation, field, or characteristic
condition is hidden in the section. The node's mixed chapter description still
identifies the two source lemmas unambiguously; no correction is required.

Object, hypothesis, and conclusion checklist (H3):

1. Ring S, commutative and nonnegatively graded: `{S : Type u} [CommRing S]`,
   `(𝒮 : ℕ → σ) [GradedRing 𝒮]`, with `{σ : Type v} [SetLike σ S]
   [AddSubgroupClass σ S]`. Verdict: exact. Read `GradedRing` in
   `Mathlib.RingTheory.GradedAlgebra.Basic`: it is a multiplicative internal
   direct-sum decomposition. The additive-subgroup representation is available
   for every graded ring, so these interface instances add no mathematical
   hypothesis. Independent universes `u v` impose no smallness restriction.
2. X = Proj(S): `(Proj 𝒮).Opens`. Verdict: exact substitution of a defined X.
   Read `AlgebraicGeometry.Proj` and `projIsoSpec` in ProjectiveSpectrum/Scheme;
   this is the full scheme on homogeneous primes avoiding the irrelevant ideal,
   not `Proj.projectiveSpaceOverAffine` (the latter is only a specialization).
   Both `def-pc-proj` and `def-nagata-affine-proj` use this same general scheme.
3. Index every positive-degree homogeneous f: `∃ (f : S) (d : ℕ),
   0 < d ∧ f ∈ 𝒮 d ∧ U = basicOpen 𝒮 f`. Verdict: exact. Existential degree
   witnesses allow every such element, including zero. A set of opens discards
   duplicate representations without losing any open.
4. D_+(f) is the standard open in that scheme: `basicOpen 𝒮 f`. Verdict: exact.
   Read the scheme wrapper in Basic and the underlying
   `ProjectiveSpectrum.basicOpen` in Topology: membership is precisely
   `f ∉ x.asHomogeneousIdeal`. No private notion was introduced.
5. These opens form a basis for the topology: `TopologicalSpace.Opens.IsBasis`
   of exactly the set in item 3. Verdict: exact. Read Opens/IsBasis: it is
   `IsTopologicalBasis` of the underlying sets, not merely a cover or a finite
   subcover assertion.
6. Each such open is affine: the second conjunct is
   `∀ (f : S) (d : ℕ), 0 < d → f ∈ 𝒮 d → IsAffineOpen (basicOpen 𝒮 f)`.
   Verdict: exact, for the same ring and grading. Read `IsAffineOpen` in
   AffineScheme: the open subscheme is affine. The degree-zero localization is
   not an extra conclusion or binder in this node. Read
   `HomogeneousLocalization.Away` and its homogeneous fraction constructor,
   along with `Proj.basicOpenIsoSpec`: they are exactly the recorded dependency
   notion and chart identification used by the proof docstring.
7. Logical order: the ring and grading precede both conjuncts; the basis family
   existentially indexes all positive-degree elements, while affineness is
   universal over them. Verdict: no hypothesis added or clause lost, and no
   stronger claim about arbitrary nonhomogeneous or degree-zero elements.

Edge cases: S = 0 and gradings concentrated in degree zero give empty Proj and
are allowed; the empty open is affine (Spec of the zero ring). Positive-degree
zero and nilpotent elements give empty standard opens and are included. The
index family has no finiteness/nonemptiness assumption; it includes zero with
witness degree 1 even if all positive components vanish. There is no parameter n
or imposed characteristic; polynomial rings with zero or one variable, and
infinitely many variables, are covered by the same general statement. Degree
zero is deliberately excluded. All variables and both universes are explicitly
bound; no Nontrivial, Noetherian, or finite-generation instance occurs.

Independent H4 searches, using different wording from the worker:

- `msearch.py leanfinder "Every open neighborhood on the projective spectrum
  contains a basic affine open defined by a homogeneous element of strictly
  positive degree"`: eight hits. The closest are `Proj.isBasis_basicOpen` and
  `Proj.isAffineOpen_basicOpen`; actual signatures in Basic show respectively
  an all-elements basis and just the affine conjunct. No exact match.
- `msearch.py loogle "ProjectiveSpectrum.basicOpen, IsTopologicalBasis"`:
  identifier rejected; corrected to `ProjectiveSpectrum.basicOpen,
  TopologicalSpace.IsTopologicalBasis`, returning only
  `ProjectiveSpectrum.isTopologicalBasis_basic_opens`, again all elements.
- `msearch.py grep "IsBasis|IsTopologicalBasis|isBasis|isTopologicalBasis"
  AlgebraicGeometry/ProjectiveSpectrum`: nine hits; inspected both basis
  signatures and the scheme charts, no positive-degree combined statement.
- `msearch.py leansearch "The affine standard opens indexed by homogeneous
  elements of strictly positive degree form a basis on Proj of any graded
  commutative ring"`: Internal Server Error, recorded unavailable, no verdict.
- Independent `rg` across upstream `WeilConjectures`, project `lean/Sheaf`,
  and `dag/lean_names_upstream.json`, with `positiveDegree_basicOpen`,
  homogeneous/basis in either order, standard/open/basis, and
  `isBasis.*basicOpen`: affine-scheme basis uses and unrelated homogeneous
  polynomial bases, plus the existing consumer's docstring, no matching
  declaration. Read upstream ProjectiveSpectrum/Basic and
  `Proj.iSup_basicOpen_homogeneous_eq_top` in Functor; the latter is a cover,
  not the basis assertion. The chosen full declaration name is unused.

H5/H6/H8/H9: no definitions or hollow data; one theorem with exactly `by sorry`.
The single Basic import supplies every mathematical notion used. The module
and theorem docstrings name both source places and the correct blueprint id.
The proof docstring reproduces both DAG steps in order: clause (0) of
`lem-weil-pbc-proj-standard-open-inclusion`, including the homogeneous-component
and degree-zero refinement argument, then the affine identification from
`def-nagata-affine-proj`. Namespace and topic directory follow Mathlib; all
lines fit the width bound. The node's `lean.statement` is the exact signature
in the file. No mismatches and no edits to correct Lean were warranted;
this reading adds only the independent report and search evidence.

Second-reader validation: `scompile.py C1 lem-sc-proj-standard-open-basis`
compiled the unchanged module on the server in 1.6 seconds with no errors or
warnings. Independently checked the signature string verbatim and the Lean
line widths. `deliver2.py C1 lem-sc-proj-standard-open-basis --no-push` printed
OK: compilation and stage-2 preflight passed. Delivery follows that clean run.
