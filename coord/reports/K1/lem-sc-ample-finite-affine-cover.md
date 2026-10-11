## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleFiniteAffineCover` states
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_finite_affine_cover`, with proof `sorry`.
No definitions, new nodes, dependency replacements or statement corrections are needed.

Hypothesis and clause correspondence:

- An arbitrary scheme X: `(X : Scheme.{u})`, with explicit universe `u`.
- An invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`.
- Absolute ampleness: `(hL : IsAmple X L)`, using the dependency definition, not the
  source repository's relative/projective `AlgebraicGeometry.IsAmple`.
- Finitely many indices: `∃ m : ℕ`, with all families indexed by `Fin m`.
  Every finite family can be enumerated this way, and `m = 0` is permitted.
- Positive integers n_i: `n : Fin m → ℕ` and `∀ i, 0 < n i`.
  Positive naturals represent exactly the positive integers appearing in the statement.
- Global sections of L tensor n_i: the dependent family
  `s : (i : Fin m) → (L.tensorPow (n i)).val.presheaf.obj (Opposite.op ⊤)`.
- X_s_i as an open subscheme: `U : Fin m → X.Opens`, with the biconditional
  `x ∈ U i ↔ germ (s i) ∉ maximalIdeal • ⊤` on the stalk module. This is exactly the
  nonvanishing condition in the recorded ampleness definition, so these are the
  actual X_s_i rather than smaller neighbourhoods or unspecified affine opens.
- Every X_s_i affine: `∀ i, IsAffineOpen (U i)`.
- X equals the union of these opens: `∀ x : X, ∃ i : Fin m, x ∈ U i`.
  Since each U i is an open subset of X, this pointwise condition is precisely equality
  of their union with X.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is Mathlib `IsAffineOpen` from
  `Mathlib.AlgebraicGeometry.AffineScheme` (open subscheme is affine).
- `def-sc-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`. Its local triviality condition
  is the node's locally free rank-one condition. The same module defines `tensorPow`:
  zero power is the unit module and successor powers are tensor products.
- `def-weil-pbc-ample-invertible-module`: `AlgebraicGeometry.Scheme.Modules.IsAmple` in
  `Sheaf.AlgebraicGeometry.Ample`, with quasi-compactness and the exact affine
  nonvanishing-neighbourhood condition. Its imported stalk and ideal operations are
  reused verbatim in the conclusion, without defining a second notion.

Edge cases: empty X allows m = 0 (all family conditions and coverage are vacuous);
nonempty X forces a nonempty family by the cover condition. Zero exponents are excluded
by the strict positivity clause. For an affine scheme with the trivial line bundle,
the constant section 1 and n = 1 give a single chart. On projective space the usual
coordinate sections supply the familiar affine charts. Nothing assumes a base field,
properness, separatedness, Noetherianness, reducedness, dimension or characteristic.
Fin m places no size restriction on X or its modules.

Source checked: [Stacks Definition 01PS](https://stacks.math.columbia.edu/tag/01PS)
is exactly quasi-compactness plus the pointwise affine nonvanishing condition;
[Stacks Lemma 01Q1](https://stacks.math.columbia.edu/tag/01Q1), first proof paragraph,
chooses the finite positive-degree homogeneous sections with affine loci covering X.
The local literature/stacks-project tree is absent on this machine, so these official
source pages were read online. No node fault or STATEMENT-DISPUTED issue was found.
The docstring carries both steps of the node's proof: the affine nonvanishing open
cover from ampleness and finite-subcover extraction from quasi-compactness.

Searches (2026-10-11):

- msearch.py leansearch, query "An ample invertible module admits a finite cover by affine
  nonvanishing loci of global sections of positive tensor powers": unavailable, Internal
  Server Error; no mathematical verdict inferred.
- msearch.py leanfinder, query "An ample invertible sheaf has a finite affine cover by
  nonvanishing loci of sections of positive tensor powers": eight hits, including
  `isAffine_of_isAffineOpen_basicOpen`, `affineOpenCoverOfSpanRangeEqTop` and Proj covers;
  none is this theorem for arbitrary ample invertible modules.
- msearch.py loogle, query `AlgebraicGeometry.IsAffineOpen, CompactSpace`: three hits,
  a quasi-affine criterion for structure-sheaf sections and inverse-limit cover lemmas;
  none states this theorem.
- msearch.py grep, regex `ample.*affine.*cover|finite.*principal.*open`, in
  Mathlib/AlgebraicGeometry: zero hits.
- rg of the project's lean/Sheaf and the source WeilConjectures for
  `IsAmple|nonvanishing|Nonvanishing|ample_finite|ample.*affine`, plus
  `ample.*finite|finite.*ample|exists_finite_affine`: no exact theorem.
  Read source Modules/AmpleFamily.lean: `HasAmpleFamily` existentially chooses a line
  bundle with sections of that one bundle; it does not state the finite cover conclusion
  for the given ample L with varying positive powers. Its lemmas concern pullback and
  disjoint unions. Source Modules/Ample.lean uses a relative, projective-over-field notion.
- rg for the node id in source WeilConjectures: no hits. rg for the proposed full-name
  suffix `exists_finite_affine_cover` in source, lean/Sheaf and dag/lean_names_upstream.json:
  no collision.

Server validation: scompile.py compiled the module in 1.7 seconds with exit code 0 and
no warnings. The only theorem is intentionally left `sorry` for stage 3.


## Second reading by K1

Independent second reading of the node copy and module, the three statement-dependency
nodes, their recorded declarations, and the Stacks source. Verdict: the Lean states
exactly the node's assertion. No mismatch was found; the Lean and node are unchanged.
Only this independent review section was appended.

Object, hypothesis and conclusion checklist:

- Object X, an arbitrary scheme: `(X : Scheme.{u})`. Read Mathlib's `Scheme`
  structure in `Mathlib.AlgebraicGeometry.Scheme`: a locally ringed space with local
  affine charts. Verdict: the same scheme notion as `def-pc-scheme`.
- Object L, an invertible O_X-module: `(L : X.Modules) [L.IsInvertible]`.
  Read `Modules` in Mathlib Modules/Sheaf and `IsInvertible` in source
  Modules/Invertible: a sheaf of modules locally isomorphic to the structure sheaf.
  This is locally free of rank one; quasi-coherence follows locally from this
  condition, so omitting an independent quasi-coherence instance drops no hypothesis.
  Verdict: exactly `def-sc-invertible-module`, with no curve restriction.
- Hypothesis L ample: `(hL : IsAmple X L)`. Read the entire definition in
  `Sheaf.AlgebraicGeometry.Ample`: `CompactSpace X` and a positive-power global
  section at every point whose exact nonvanishing open is affine.
  Verdict: precisely `def-weil-pbc-ample-invertible-module`, absolute ampleness;
  no field, projectivity, properness, separatedness or Noetherian hypothesis.
- Finite collection: `∃ (m : ℕ)`, with all three families indexed by `Fin m`.
  Verdict: enumeration of an arbitrary finite collection, including the empty one.
- Positive integer degrees: `(n : Fin m → ℕ)` with `(∀ i, 0 < n i)`.
  Verdict: positive natural degrees correspond bijectively to positive integers;
  no uniform degree, distinctness or upper bound is imposed.
- Global sections: dependent `s : (i : Fin m) →
  (L.tensorPow (n i)).val.presheaf.obj (Opposite.op ⊤)`.
  Read source `tensorPow`: power zero is the monoidal unit, successor is tensor
  product over O_X. The presheaf at the top open is the module of global sections.
  Verdict: exactly Gamma(X, L tensor n_i), not structure-sheaf sections.
- Nonvanishing loci: `(U : Fin m → X.Opens)` together with, for every i and x,
  `x ∈ U i ↔ germ (s i) ∉ maximalIdeal • ⊤` on the stalk module.
  The precise germ, maximal ideal and stalk expressions match the dependency
  definition. The ideal scalar action on the whole module is m_x times the module.
  Verdict: U i is exactly X_s_i; the extra existential open variable is only a
  representation of that uniquely determined set, not an additional choice of
  smaller affine neighbourhood. No separate private definition is introduced.
- Affineness: `(∀ i, IsAffineOpen (U i))`.
  Read Mathlib's `IsAffineOpen`: it is `IsAffine U` for the open subscheme.
  Verdict: exactly the affineness of each X_s_i.
- Coverage: `(∀ x : X, ∃ i : Fin m, x ∈ U i)`.
  Verdict: exactly X = union_i X_s_i, because every U i is already an open in X.
  The witnesses m, n, s and U all occur before these conjunctions, as the node
  requires; neither a fixed family nor a specified degree is assumed.

Source check: the local Stacks .tex tree is absent. Read the official raw
[properties.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex),
labels `section-ample`, `definition-ample`, and `lemma-ample-immersion-into-proj`,
alongside the official [01PS](https://stacks.math.columbia.edu/tag/01PS) and
[01Q1](https://stacks.math.columbia.edu/tag/01Q1) pages. The section opening defines
X_s by the maximal-ideal stalk condition, with openness for invertible sheaves.
The definition assumes just a scheme and an invertible module, and includes
quasi-compactness. The first paragraph of 01Q1 chooses the finite homogeneous
positive-degree sections with affine loci covering X; quasi-separatedness there
is a consequence, not an extra assumption. The node's two proof steps and the
Lean docstring match: pointwise affine nonvanishing opens from ampleness, then a
finite subcover from quasi-compactness. No unit-statement error or correction.

Edge cases: m = 0 is permitted and gives the empty cover of the empty scheme.
For nonempty X the last clause rules out m = 0. All exponents n_i = 0 are ruled
out exactly by positivity; tensorPow nevertheless has the correct zero-power
convention. The zero sheaf is not invertible on a nonempty scheme (locally the
structure sheaf has nonzero stalk), and on the empty scheme all conditions are
vacuous. A zero section has empty nonvanishing locus; such an empty chart is
allowed but cannot cover any point. The zero ring's empty spectrum is included.
There is no base ring or field binder, hence no characteristic restriction.
The explicit arbitrary universe u agrees with the recorded dependency's
Scheme/Modules universes, and Fin m restricts only the finite indexing family,
not the size of X. Every binder and universe is explicitly bound.

Independent searches, using different wording from the worker:

- msearch.py leanfinder: "A line bundle that is ample has a finite collection of
  sections in positive degrees whose distinguished affine opens cover the scheme".
  Eight results, including `isAffine_of_isAffineOpen_basicOpen`,
  `isAffineOpen_of_isAffineOpen_basicOpen`, and Proj affine covers. The printed
  signatures concern structure-sheaf sections with a unit-ideal hypothesis or
  graded rings; none asserts the present result for a given ample line bundle.
- msearch.py loogle: `"IsAmple"`, zero hits.
- msearch.py grep: `ample|Ample|generatingLocus`, broad search returned substring
  matches in "example"; these give no mathematical evidence. Refined direct rg
  to word-boundary `(IsAmple|Ample|ample|generatingLocus)` throughout Mathlib's
  AlgebraicGeometry directory: no ampleness declaration. Also searched source
  WeilConjectures/AlgebraicGeometry/Modules and project lean/Sheaf for finite
  affine covers, nonvanishing loci, IsAmple and HasAmpleFamily.
- Opened source Modules/AmpleFamily.lean: `HasAmpleFamily` existentially chooses
  an invertible module with sections of that same module; it does not give this
  finite cover for the given L and varying positive powers. Its affine pullback,
  isomorphism and finite-disjoint-union statements are also different.
  Source Modules/Ample.lean's `AlgebraicGeometry.IsAmple` requires a morphism to
  Spec of a field and positive very ample power; it is the documented stronger
  projective-relative notion, not the dependency's absolute ampleness.
  The project affine-generating-loci criterion is likewise relative over a field
  and concludes ampleness rather than the present finite cover.

No new definition nodes or dependency replacement modules occur in this delivery,
so H12/H13 introduce no additional items to review. The only import is needed for
absolute ampleness and its underlying operations. There are no definitions and no
proved statements; the sole theorem ends in `by sorry`. Module and theorem
docstrings name the source and blueprint; the theorem docstring gives both proof
steps. All lines meet the 100-character convention, and the node's lean.statement
was checked literally equal to the complete file signature before `:=`.

Validation: scompile.py on the absolute sandbox module path compiled on the server
in 1.7 seconds, exit code 0, with no diagnostics. No unbound variable or universe
was found by eye. An initial invocation using a relative path from the read-only
repository failed to locate the sandbox file; rerunning with its absolute path
resolved this invocation error without changing any source.
