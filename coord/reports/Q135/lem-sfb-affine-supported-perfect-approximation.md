## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSupportedPerfectApproximation` states
Stacks Project Tag 08EQ (`perfect.tex`, `lemma-approximation-affine`) in two named
theorems. Both proofs are `sorry`; their docstrings contain the node's induction,
TR3 and stalkwise diagram chase, followed by the uniform-property argument.
There are no definitions, new nodes, dependency repairs or statement corrections.
The node's natural-language statement and all dependencies are preserved.

Clause-by-clause correspondence:

- The affine scheme Y is `(Y : Scheme.{u}) [IsAffine Y]` in both declarations.
  The three `HasDerivedCategory.{w}` instance families are exactly the shared
  derived-category choices required by the recorded definitions: modules on Y,
  modules on each open subscheme, and modules on the corresponding over-site.
  The universes `u w` are explicit and independent; no equality is imposed.
- A closed subset T is `(T : Set Y) (hT : IsClosed T)`.
- The integer m is `(m : ℤ)`; the nonnegative integer s is `(s : ℕ)`.
  Naturals encode all nonnegative integers, including zero; the degree bound
  casts s to ℤ explicitly.
- F in D_QCoh(O_Y) is `(F : schemeDerivedCategory Y)` together with
  `(hF : schemeDerivedQCohProperty Y F)`, using the existing full-subcategory
  predicate rather than another notion of derived quasi-coherence.
- m-pseudo-coherence is precisely `(hFm : IsMPseudoCoherent Y m F)`.
- The complement is a union of s affine open subschemes exactly when
  `hcover` supplies `U : Fin s → Y.Opens`, `∀ k, IsAffineOpen (U k)`, and
  `(⋃ k, (U k : Set Y)) = Tᶜ`. It does not require principal, distinct,
  nonempty or disjoint opens; equality ensures that each lies in the complement.
- The hypothesis on cohomology stalks is `hvanish`: for every integer i with
  `m - (s : ℤ) + 1 ≤ i` and every y outside T, the underlying additive group of
  the stalk of the i-th derived homology sheaf of F is `Subsingleton`.
  A stalk is a group with zero, so this says exactly that it vanishes.
- The existential conclusion supplies `P : schemeDerivedCategory Y` and
  `v : P ⟶ F`; `IsPerfect Y P` uses the recorded perfectness definition.
- The second conjunct of the conclusion quantifies over every integer i and
  point y outside T and says its cohomology stalk is `Subsingleton`, giving
  all-degree support on T without any extra cohomology vanishing on T.
- The third conjunct is `∀ i, m < i → IsIso ((homologyFunctor ... i).map v)`.
  Thus it concerns the cohomology maps of this same v, in every degree above m.
- The last conjunct is `Epi ((homologyFunctor ... m).map v)`. This is a
  surjection of module sheaves, not surjectivity of every open-section map.
- The node's final assertion is the separate theorem
  `hasSupportedPerfectApproximation_of_isAffine`, with only Y affine and the
  required derived-category choices, concluding `HasSupportedPerfectApproximation Y`.
  In particular it is independent of the particular T,m,s,F of the first theorem.

Statement dependency declarations read in full and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  affine scheme/open predicates are the Mathlib `IsAffine` and `IsAffineOpen`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`;
  `schemeDerivedQCohCategory` was read and its defining predicate is used.
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent`.
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsPerfect` (and its `IsStrictlyPerfect` definition).
- `Sheaf.AlgebraicGeometry.SupportedPerfectApproximation`:
  `AlgebraicGeometry.Scheme.HasSupportedPerfectApproximation`.

All statement-dependency modules are public imports. The stated proof dependencies
are ordinary imports: Mathlib's affine quasi-compactness/quasi-separatedness,
finite affine cover, tilde/global-sections adjunction, triangulated categories,
derived homology exact sequence and stalk-isomorphism criterion; the recorded
`QuasicoherentFiniteTypeAffine`, `PerfectThickClosure`, `SupportedQCohTriangulated`
and `ModuleStalkExact` modules are also imported. Three proof dependencies have
no recorded declaration or module at this snapshot and hence cannot yet be
imported: `lem-sfb-ringed-site-pseudocoherent-top-finite-type`,
`lem-sfb-affine-supported-class-lift`, and
`lem-sfb-ringed-site-m-pseudocoherent-triangle`. Their mathematical steps remain
explicit in the proof docstring; they are not statement prerequisites.

Edge cases checked before writing:

- If s=0, the empty indexed union is empty, so `hcover` forces T=Y. All
  outside-support hypotheses and conclusions are vacuous, with the expected
  ordinary perfect approximation remaining.
- The empty scheme is permitted; the empty cover works and the zero perfect
  object supplies the mathematical witness. No nonemptiness assumption is used.
- For F=0 the zero perfect object and zero morphism satisfy every clause.
- If T is empty, the hypothesis forces F to vanish in degrees at least
  m-s+1, hence at least m for s>0; taking P=0 is consistent with the conclusion.
  The case s=0 forces Y empty.
- If T=Y and s>0, a family of empty affine opens is permitted. No requirement
  that the cover has minimal cardinality has been silently added.
- Arbitrarily negative m are retained, and the support bound uses integer
  subtraction, never truncated natural subtraction.
- In the final assertion r is chosen from a finite affine cover of the
  retrocompact complement before m and F. It depends only on Y,T as required.

Searches made for existing declarations (2026-10-24 UTC):

- `msearch.py leanfinder`: “An m pseudo coherent derived object on an affine
  scheme admits a supported perfect approximation inducing cohomology
  isomorphisms above m and surjection at m”. Eight results, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE`, `exists_iso_Q_obj_of_isLE`,
  and related bounded representatives/fractions. None provides a perfect
  approximation with prescribed support.
- `msearch.py leansearch`: “On an affine scheme a pseudo coherent complex has
  a perfect approximation supported on a closed subset”. Eight results about
  `Module.isClosed_support`, ideal-sheaf support and affine closed immersions;
  none states this derived approximation.
- `msearch.py loogle`: `"Perfect", "Complex"`: zero hits.
- `msearch.py grep`: `pseudo.?coher|perfect.*approximat|approximat.*perfect`:
  zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for supported
  approximation terminology and this exact node id found the existing property
  definition and the algebraic-space approximation theorem, which cites this
  scheme lemma in its proof but does not state it. The upstream
  `OpenSupportedHomologyApproximation` concerns a different ringed-space
  homology construction. Neither is a duplicate of Tag 08EQ.
- `rg` for the two proposed declaration names in Mathlib, WeilConjectures and
  Sheaf found no existing declaration. No new notion needs a definition node.

Source check: the local Stacks source `perfect.tex`, lines 3667–3728, has exactly
m-pseudo-coherence, vanishing for i ≥ m-s+1, a union of s affine opens, the
supported approximation and the final assertion for every affine scheme. No
source-based correction or unresolved mathematical dispute was found.

Validation: the prescribed `scompile.py Q135` compiled this single delivered
module on the server against the published library, first as a sandbox and then
at its library module name, with no errors or warnings (5.4 s and 9.5 s).

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
