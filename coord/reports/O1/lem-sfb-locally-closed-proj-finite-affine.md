## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyClosedProjFiniteAffine` states
`AlgebraicGeometry.Proj.exists_basicOpen_subset_isAffineOpen_preimage` and
`AlgebraicGeometry.Proj.exists_isAffineOpen_of_isImmersion`. Both proofs are
`sorry`; there are no definitions, additional nodes, dependency repairs, or
statement corrections. Only the item's `lean` field changes.

I read the node, all three statement-dependency nodes and their recorded
Mathlib signatures/docstrings, and Stacks `properties.tex`,
`lemma-ample-finite-set-in-affine` (Tag 01ZY), especially case (4) and its proof.
The source chooses finitely many standard opens avoiding the boundary, then
uses graded prime avoidance on their generated ideal. Choosing them inside
the prescribed open O gives exactly the item's ambient refinement.

Hypotheses and conclusions, clause by clause:

- The nonnegatively graded commutative ring is `{S : Type u} [CommRing S]`
  with `{σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]`,
  `(𝒜 : ℕ → σ) [GradedRing 𝒜]`. This is Mathlib's grading, with independent
  carrier and subobject universes, and no generation assumptions.
- The open of Proj is `(O : (Proj 𝒜).Opens)`; openness is bundled in `Opens`.
- The scheme is `{X : Scheme.{u}}`, and the closed immersion into O is
  `(j : X ⟶ O.toScheme) [IsClosedImmersion j]`. These are exactly the
  dependency nodes' scheme and closed-immersion notions.
- The finite subset is `(E : Set X) (_hE : E.Finite)`. In particular it need
  not be nonempty, reduced, or a set of closed points.
- The positive integer degree and homogeneous element are
  `∃ (d : ℕ) (f : S), 0 < d ∧ f ∈ 𝒜 d`. Positive natural degrees are the
  positive integer degrees of this nonnegative grading. There is no
  nonzero-element assumption.
- The image of E in the ambient Proj is `(j ≫ O.ι) '' E`. The clause
  `(j ≫ O.ι) '' E ⊆ (basicOpen 𝒜 f : Set (Proj 𝒜))` is j(E) ⊆ D₊(f),
  using the open inclusion `O.ι` to view j as an ambient morphism.
- `basicOpen 𝒜 f ≤ O` is D₊(f) ⊆ O.
- `IsAffineOpen ((j ≫ O.ι) ⁻¹ᵁ basicOpen 𝒜 f)` says the actual inverse-image
  open subscheme of X is affine. Preimage notation produces an open of X;
  `IsAffineOpen` is Mathlib's `IsAffine` on its open subscheme. Because the
  standard open lies in O, this is precisely j⁻¹D₊(f).
- The second declaration renders the entire “in particular” clause:
  `(i : X ⟶ Proj 𝒜) [IsImmersion i]` is a locally closed immersion, and
  `∃ U : X.Opens, E ⊆ (U : Set X) ∧ IsAffineOpen U` is an affine open
  containing the finite subset. Mathlib's immersion condition is equivalent
  to a closed immersion followed by an open immersion.
- The negative-assumption sentence is respected: no finite generation,
  degree-one generation, field, reducedness, or closed-point hypothesis is
  present in either declaration.

Statement dependencies used:

- `def-pc-proj`: `AlgebraicGeometry.Proj` and `AlgebraicGeometry.projIsoSpec`
  in `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, and
  `ProjectiveSpectrum.basicOpen` in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology`. The public import
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` exposes these and the
  scheme-level wrapper `AlgebraicGeometry.Proj.basicOpen`. I read the
  definitions and docstrings, including the affine chart identification.
  The node is a Mathlib leaf; no replacement declaration is necessary.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme` (exposed by the public imports).
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, plus the node's
  `mathlib_match` for `AlgebraicGeometry.IsImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`. Both are public imports;
  there is no private copy of the immersion notion.

The already stated proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`
(`AlgebraicGeometry.Proj.standardOpenProperties`, clause (0)) and
`WeilConjectures.RingTheory.GradedPrimeAvoidance`
(`HomogeneousIdeal.exists_homogeneous_mem_notMem_of_isPrime`). I read their
full theorem signatures and proof docstrings. The other proof dependencies
are the Proj and closed-immersion notions already exposed above. There are
no omitted proof imports and no import cycles identified.

Edge cases checked before writing:

- E empty: take d = 1 and f = 0. Zero belongs to every graded piece,
  D₊(0) is empty and contained in every O, and its inverse-image open is
  empty and affine. The signature allows exactly these witnesses.
- O empty, X empty, the zero ring, and vanishing irrelevant ideal: the
  same empty standard-open choice applies; existence of a morphism into
  empty O forces X to be empty. No nontriviality assumptions exclude them.
- S₁ = 0 and generators of unequal positive degrees: no degree-one or
  common-degree input is imposed. The sought degree is existential.
- Generic/nonclosed points, repeated image primes, nilpotents, and
  arbitrary non-Noetherian rings: the proof uses homogeneous prime
  avoidance and ideal membership, with none of the excluded assumptions.
- The corollary explicitly quantifies the immersion, rather than
  assuming a stronger projective or finite-type embedding.

Searches for existing statements/notions (2026-10-24):

- `msearch.py ... leanfinder`: “Given an open subset O of Proj of a
  nonnegatively graded ring and a closed subscheme X in O, every finite
  subset of X is contained in one positive degree standard open inside O
  with affine inverse image”. Eight hits: Proj affine covers and
  `isAffineOpen_basicOpen`, and finite-type structure maps. None gives
  one standard open for an arbitrary finite set inside a prescribed O.
- `msearch.py ... loogle`: `AlgebraicGeometry.Proj.basicOpen, Set.Finite`.
  Zero hits.
- `msearch.py ... grep`: `finite.*basicOpen|basicOpen.*finite|finite.*affine|affine.*finite`
  in `AlgebraicGeometry/ProjectiveSpectrum`. Zero hits.
- `msearch.py ... leansearch`: “Every finite set in a locally closed
  subscheme of Proj has a standard affine open neighbourhood contained in
  a prescribed ambient open”. Eight hits, including the single-point
  `exists_isAffineOpen_mem_and_subset`, `Scheme.affineOpens`,
  `IsAffineOpen`, `Proj.isAffineOpen_basicOpen`, `Proj`, and
  `affineOpensRestrict`. None states this finite-set ambient refinement.
- `rg -n 'locally.closed|LocallyClosed|projective.*finite|finite.*affine'`
  over `lean/WeilConjectures` and `lean/Sheaf`, followed by focused
  `finite.*(affine|basicOpen)|exists.*isAffineOpen` searches in their
  algebraic geometry modules: unrelated finite-type affine charts,
  affine covers, Proj ample criteria, and single-point neighbourhoods;
  no exact existing statement found.
- `grep -rn 'lem-sfb-locally-closed-proj-finite-affine' lean/WeilConjectures`:
  no tagged declaration.
- Exact-name `rg` searches for both proposed declarations in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  zero hits before writing.

No statement dispute or mathematical node fault was found. The supplied
example `lean/Sheaf/CategoryTheory/CompactObject.lean` is withdrawn in the
current checkout; its node now points to the upstream module. I used the
required module-mode header, public statement imports, ordinary proof
imports, and exposed public section.

Validation: `scompile.py O1 lem-sfb-locally-closed-proj-finite-affine` on the
single delivered module passed both sandbox and library-path compiles
(1.4 seconds each), with no errors or unexpected warnings.

## Second reading by O1

This is the assigned worker's separate second pass, not a claim of review
by another agent: the dispatcher expressly forbids starting other agents
and assigns independent delivery review to the maintainer.

With the node and the completed module open, I checked each binder and
conjunct again. The ambient image uses j followed by O's inclusion, and
its inverse-image affine open is in X, not in the ambient scheme. The
containment in O is an explicit conclusion. The grading has no extra
finiteness or generation assumptions. The second declaration includes the
in-particular immersion statement as well as the first declaration's
ambient refinement. Empty subsets and f = 0 are permitted; d remains
strictly positive. All variables/universes are explicitly bound; both
proofs are exactly `sorry`. No mismatch or subsequent change was found.
