## Worker report

The module `Sheaf.AlgebraicGeometry.ProjDegreeMultipleAffineRefinement` states
`AlgebraicGeometry.Proj.degreeMultiple_affine_refinement`, with a single `sorry` and no
new definitions. The node is unchanged except for its `lean` field.

Hypotheses and conclusions, clause by clause:

- The nonnegatively graded commutative ring is `{A : Type u} {σ : Type v}` with
  `[CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]`.
  Both universes are explicitly declared and independent. `Proj 𝒜` is the actual scheme.
- The prescribed integer is `(d : ℕ) (hd : 0 < d)`, exactly `d ≥ 1`.
- The arbitrary open subscheme is `(U : (Proj 𝒜).Opens)` with its canonical restricted
  scheme `U.toScheme` and open immersion `U.ι`. There is no quasi-compactness binder.
- Every point and neighbourhood are `∀ (x : U.toScheme) (N : U.toScheme.Opens), x ∈ N →`.
  Thus `x ∈ U` and `N ⊆ U` are intrinsic, without extra hypotheses.
- The witnesses are `∃ (q : ℕ) (g : A), 0 < q ∧ g ∈ 𝒜 q`.
- The degree clause is `g ^ d ∈ 𝒜 (q * d)`.
- The point and equality clauses are `U.ι x ∈ basicOpen 𝒜 (g ^ d)` and
  `basicOpen 𝒜 (g ^ d) = basicOpen 𝒜 g`.
- The neighbourhood inclusion is `basicOpen 𝒜 g ≤ U.ι ''ᵁ N`. The latter is the open image
  of `N` in Proj and is contained in `U`. This asserts containment of the entire standard
  open, as required, rather than asserting affineness of an arbitrary intersection.
- Affineness is `IsAffineOpen (basicOpen 𝒜 g)`.
- The canonical scheme identification is `IsIso (basicOpenToSpec 𝒜 g)`. This existing
  canonical map has type `(basicOpen 𝒜 g).toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
  𝒜 g))`. Thus it asserts that this particular canonical map is invertible, not merely
  existence of an unspecified scheme isomorphism. The existing `basicOpenIsoSpec 𝒜 g hg hq`
  is precisely `asIso` of that map; no replacement of the canonical construction occurs.
- The final family, as opens of `U`, is the set of `V : U.toScheme.Opens` for which
  `∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 (n * d) ∧ basicOpen 𝒜 f ≤ U ∧
  V = U.ι ⁻¹ᵁ basicOpen 𝒜 f`. `TopologicalSpace.Opens.IsBasis` asserts it is a basis.
  The last universal conjunct asserts `IsAffineOpen` of every member represented this
  way. Containment in `U` makes the preimage the same whole standard open as a scheme.

Dependency declarations read and reused:

- `def-pc-proj`: its Mathlib matches `AlgebraicGeometry.Proj` (scheme construction in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`), `AlgebraicGeometry.projIsoSpec`,
  and `ProjectiveSpectrum.basicOpen`; the scheme-level interface used is
  `AlgebraicGeometry.Proj.basicOpen` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`. I also read the audited upstream
  `Proj.isAffineOpen_basicOpen_and_nonempty_iso`; no duplicate definition is introduced.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`. `U.toScheme` and `U.ι` are the canonical open
  subscheme and its open immersion from `Mathlib.AlgebraicGeometry.Restrict`.
- `def-nagata-homogeneous-localization-degree-zero`: `HomogeneousLocalization.Away` in
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`; I read its numerator/denominator
  representation and `Away.mk`, `Away.mk_surjective`, including the nilpotent case.
- Proof dependency `lem-sc-proj-standard-open-basis` is imported privately from
  `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis`, with declaration
  `AlgebraicGeometry.Proj.isBasis_positiveDegree_basicOpen_and_isAffineOpen`.
- Proof dependency `prop-nagata-proj-standard-open` uses existing
  `Proj.basicOpenIsoSpec` and `Proj.iSup_basicOpen_eq_top` in Mathlib's projective-spectrum
  Basic module. I read their full signatures and docstrings, as well as
  `basicOpenToSpec`, `basicOpen_pow` and `isAffineOpen_basicOpen`.

Sources checked locally: `literature/stacks-project/constructions.tex`,
`lemma-proj-scheme` (Tag 01MB), including the canonical structure-sheaf identification,
and `lemma-ample-on-proj` (Tag 01MW), including its proof of (6)--(7).
The quasi-compactness there is used to choose one twisting degree; this item fixes an
arbitrary positive `d` and uses only local power refinement, so does not require it.

Edge cases checked before writing: `U = ∅`, empty Proj (including a zero ring or a grading
with nilpotent positive-degree part), empty neighbourhoods, `d = 1`, missing graded pieces,
and nilpotent or zero candidate elements. Empty opens give a vacuous neighbourhood clause
and a basis on the empty space. A nilpotent cannot supply a chart containing a point;
its empty standard open remains affine (the localization may be the zero ring).
Zero belongs to every graded component and the family may include the empty open, which
is allowed in `Opens.IsBasis`. No degree-one generation, nonzero ring, finite generation,
Noetherian, or quasi-compactness hypothesis is introduced. `d = 0` is excluded by the
node itself. The independent `σ` universe excludes no grading allowed by Mathlib.

Searches (all `msearch.py Q28 lem-trf-proj-degree-multiple-affine-refinement`):

- LeanFinder: `For every open U of Proj and positive d, homogeneous elements with positive
  degree divisible by d define an affine open basis of U`. Eight hits, including
  `Proj.isBasis_basicOpen`, `Proj.isAffineOpen_basicOpen`, and standard affine covers.
  These give components, not the prescribed-degree refinement on an arbitrary open.
- Loogle: `AlgebraicGeometry.Proj.basicOpen_pow, AlgebraicGeometry.Proj.isBasis_basicOpen`.
  Zero hits for this combined query.
- Grep: `basicOpen_pow|isBasis_basicOpen|basicOpenIsoSpec`, restricted to
  `AlgebraicGeometry/ProjectiveSpectrum`. Nine hits; read the relevant Basic signatures.
- LeanSearch: `Positive degree homogeneous elements of degree divisible by a fixed
  positive integer give an affine basis of every open in Proj`. Eight hits, including
  `Proj.basicOpenToSpec`, powers, affine charts and covers; no full statement match.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `degree_multiple|degreeMultiple|multiple.*basicOpen|basicOpen.*multiple|lem-trf-proj-degree-multiple-affine-refinement`
  found no full statement or competing name. The exact node-id `grep -rn` on
  `lean/WeilConjectures` likewise found no match. A broader search found the already-used
  positive-degree basis and the audited affine-chart lemma, whose sources were read.

No new nodes, dependency repairs, statement correction, or disputed statement.
The dispatcher brief assigns the maintainer's independent review; no second-agent reading
is claimed here, and no agents were started.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
