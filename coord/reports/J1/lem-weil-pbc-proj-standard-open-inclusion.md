## Worker report

The module `Sheaf.AlgebraicGeometry.ProjStandardOpenProperties` states
`AlgebraicGeometry.Proj.standardOpenProperties`. Its one theorem has proof `sorry`.
There are no new definitions, new nodes, dependency modules, or statement corrections.

Hypotheses and clauses, matched to the node:

- An N-graded commutative ring S is `{S : Type u} [CommRing S]`,
  `(𝒜 : ℕ → σ) [GradedRing 𝒜]`, with `[SetLike σ S] [AddSubgroupClass σ S]`.
  This is Mathlib's grading representation, without any finiteness or domain assumption.
  `Proj 𝒜` is the scheme of homogeneous primes avoiding the irrelevant ideal.
  `basicOpen 𝒜 f` is exactly the open of primes not containing f.
  Positive homogeneous degree is expressed by `0 < d` and `f ∈ 𝒜 d`;
  all later elements have their own degree and membership binders.
- The canonical chart identification in the introductory notation is the existing
  `Proj.basicOpenIsoSpec 𝒜 f hf hd`, whose signature and docstring were read.
  It is context fixing the meaning of standard opens, not an extra assumption.
  The degree-zero localization is the dependency's `HomogeneousLocalization.Away 𝒜 f`.
- Clause (0), basis: `TopologicalSpace.Opens.IsBasis {U | ∃ (f : S) (d : ℕ),
  0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f}`. Only positive homogeneous elements
  index this basis. The next conjunct, universally quantified over f,g,d,k,
  asserts `basicOpen 𝒜 f ⊓ basicOpen 𝒜 g = basicOpen 𝒜 (f * g)`.
- Clause (1), equivalence: for every positive homogeneous f,g, the first conjunct is
  `basicOpen 𝒜 g ≤ basicOpen 𝒜 f ↔ ∃ (e l : ℕ) (a : S),
  0 < e ∧ a ∈ 𝒜 l ∧ g ^ e = a * f`.
  The parenthetical degree necessity is the next universally quantified conjunct:
  any such witness with `a * f ≠ 0` satisfies `l = e * k - d`.
  Degrees are natural numbers, so subtraction is natural subtraction; the relation
  and the nonzero product imply `d ≤ e * k` by the grading.
  The final implication asserts both `IsUnit (algebraMap S (Localization.Away g) f)`
  and `IsUnit (HomogeneousLocalization.Away.mk 𝒜 hg d (f ^ k) ...)`.
  The latter constructor represents precisely `f ^ k / g ^ d`, with the equal-degree
  proof furnished by Mathlib's `SetLike.pow_mem_graded` and commutativity of multiplication.
- Clause (2): for every positive homogeneous f and arbitrary index type `I : Type w`,
  an open family `U : I → (Proj 𝒜).Opens` with `⨆ i, U i = basicOpen 𝒜 f`
  has a finite refinement. The witnesses `n`, `g : Fin n → S`, `k : Fin n → ℕ`
  have positive homogeneous degrees, their union is exactly `basicOpen 𝒜 f`,
  and `∀ i, ∃ j, basicOpen 𝒜 (g i) ≤ U j` expresses refinement.
  This treats an open cover of D₊(f) as ambient opens lying in D₊(f), which is
  equivalent to opens in its subspace since D₊(f) is open.
- Clause (3): for every n and every family of positive homogeneous g_i of degree k_i,
  `basicOpen 𝒜 f ≤ ⨆ i, basicOpen 𝒜 (g i)` is equivalent to
  `Ideal.span (Set.range (fun i ↦ HomogeneousLocalization.Away.mk 𝒜 hf (k i)
  (g i ^ d) ...)) = ⊤`. The constructor represents `g_i ^ d / f ^ k_i`;
  its proof only checks degree equality, and introduces no extra hypothesis.

Dependencies used:

- `def-nagata-affine-proj`: `AlgebraicGeometry.Proj`, defined in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`. The full definition and
  docstring were read. Its chart signature was read in
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`, which is the sole import
  and imports both dependency modules transitively. `Proj.basicOpen` was also read.
- `def-nagata-homogeneous-localization-degree-zero`: `HomogeneousLocalization.Away`,
  in `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`. Its full abbreviation,
  `Away.mk` signature and fraction docstring, and ordinary-localization `val` were read.

Edge cases checked before writing: zero ring and empty Proj; positive-degree zero
and nilpotent denominators (their localizations are zero rings, where zero is a unit);
a grading concentrated in degree zero (Proj empty); degree-zero f or g excluded exactly
as in the node; n=0 and empty cover admitted (`Fin 0`, and no Nonempty assumption on I).
For an empty finite family the unit ideal condition reduces to the degree-zero ring
being the zero ring, exactly the empty-chart case. Nonzero homogeneous witnesses have
unique degrees; the degree parenthetical is restricted to nonzero products. S, grading
carrier σ, and arbitrary cover index I have explicit independent universe binders.

Searches made:

- `msearch.py ... leansearch "Standard opens D_+(g) contained in D_+(f) iff a positive
  power of g is a homogeneous multiple of f in a graded ring"`: UNAVAILABLE, Internal
  Server Error; no verdict assigned to this unavailable service.
- `msearch.py ... leanfinder "Standard opens of Proj form a positive degree homogeneous
  basis, inclusions are powers divisible by f, finite covers correspond to unit ideal
  in degree zero localization"`: eight hits, including `Proj.isBasis_basicOpen`,
  `Proj.iSup_basicOpen_eq_top`, and open cover constructions. None states this node:
  the basis theorem allows arbitrary elements; the cover criterion concerns all of Proj.
- `msearch.py ... loogle "AlgebraicGeometry.Proj.basicOpen, HomogeneousLocalization.Away"`:
  twelve chart hits, including `basicOpenIsoSpec`, `awayι_preimage_basicOpen`, and
  `basicOpenToSpec`. These identify charts but do not state this combined theorem.
- `msearch.py ... grep "basicOpen_le_basicOpen|isBasis_basicOpen|away.*[Ff]raction"
  AlgebraicGeometry/ProjectiveSpectrum`: the all-element basis theorem and a use
  of the Spec inclusion criterion; no matching Proj theorem.
- `rg` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `standardOpenProperties`: no existing name. `rg` for the item id in
  `WeilConjectures`: no hit. Searches for standard opens, `basicOpen.*iff`, and
  `exists_factor_of_isUnit` found the ordinary charts, twist unit criterion and
  homogeneous-localization factorization, and the landed graded module restriction
  theorem; none states the basis/inclusion/refinement/unit-ideal conjunction here.
  The landed module restriction theorem was opened; it concerns restriction maps
  for modules and assumes homogeneous power relations, not the inclusion equivalence.

Source checked: the local Stacks checkout is absent on this machine, so the official
[Stacks Tag 01M4](https://stacks.math.columbia.edu/tag/01M4) was opened. Parts (1)(a),(b),
(2),(3) and their proof agree with the node. The basis context and proof of the
positive-degree basis are also explicit in the node's steps 1 and 2.
No STATEMENT-DISPUTED issue or dependency fault was found.

Validation: server single-file compilation passed in 1.7 seconds without errors or warnings.

## Second reading by J1

I independently opened the delivered node and Lean module, both statement-dependency
nodes and their actual Mathlib declarations. I read the Stacks constructions.tex
source from https://raw.githubusercontent.com/stacks/stacks-project/master/constructions.tex,
from `section-proj` through `definition-standard-covering`, including the entire
`lemma-standard-open` proof. The local Stacks checkout is absent. I also checked
[01M3](https://stacks.math.columbia.edu/tag/01M3),
[01M4](https://stacks.math.columbia.edu/tag/01M4), and
[00JP](https://stacks.math.columbia.edu/tag/00JP).
The section assumes only an N-graded commutative ring. Its convention makes every
standard-open denominator homogeneous of strictly positive degree. No Noetherian,
domain, nonzero-ring, generation-in-degree-one or characteristic hypothesis occurs.

Object/hypothesis/conclusion inventory and matching:

1. The ring S and its N-grading are `{S : Type u} [CommRing S]`,
   `{σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]`,
   `(𝒜 : ℕ → σ) [GradedRing 𝒜]`. These are the binders of the recorded Mathlib
   Proj implementation, not additional mathematical restrictions. Verdict: exact.
2. X is the full `Proj 𝒜` from `def-nagata-affine-proj`. I read the `Proj`
   scheme definition in ProjectiveSpectrum/Scheme.lean: its underlying locally
   ringed space is that of relevant homogeneous primes, not projective space of
   a polynomial ring. Verdict: correct dependency, no specialization.
3. D_+(f) is `basicOpen 𝒜 f`. In ProjectiveSpectrum/Basic.lean I read
   `basicOpen` and `mem_basicOpen`: membership means precisely nonmembership in
   the point's homogeneous ideal. Each standard-open clause binds a natural
   degree with `0 < d` and `f ∈ 𝒜 d` (and similarly `k`, `g`). Verdict: exact.
4. S_(f) is the recorded `HomogeneousLocalization.Away 𝒜 f`. I read its
   abbreviation, the equal-degree fraction constructor `Away.mk`, `Away.val_mk`,
   and `Away.mk_surjective` in HomogeneousLocalization.lean. The chart is the
   existing `basicOpenIsoSpec` with binders `f_deg : f ∈ 𝒜 m`, `hm : 0 < m`;
   I opened its definition, not just its name. The chart in the introductory
   notation is supplied canonically without an extra assumption. Verdict: exact.
5. Clause (0), basis: `Opens.IsBasis {U | ∃ (f : S) (d : ℕ),
   0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f}`. This restricts the basis to positive
   homogeneous elements, unlike Mathlib's all-element basis. Verdict: exact.
6. Clause (0), intersections: the next conjunct universally quantifies f,g,d,k,
   their positivity and membership, and asserts
   `basicOpen 𝒜 f ⊓ basicOpen 𝒜 g = basicOpen 𝒜 (f * g)`.
   The product's positive homogeneous degree follows from those assumptions.
   Verdict: exact, with no condition added.
7. Clause (1), inclusion equivalence: for every positive homogeneous pair,
   `basicOpen 𝒜 g ≤ basicOpen 𝒜 f ↔ ∃ (e l : ℕ) (a : S),
   0 < e ∧ a ∈ 𝒜 l ∧ g ^ e = a * f`. In particular the witness a need not
   have positive degree. Verdict: exact quantifier order and witness strength.
8. Clause (1), degree necessity: the universal statement over e,l,a and their
   relation concludes `l = e * k - d` only under `a * f ≠ 0`. Nonzero equal
   homogeneous products force `l + d = e * k`, hence natural subtraction has
   the intended integer value. Verdict: exact; zero witnesses are retained.
9. Clause (1), units: inclusion implies
   `IsUnit (algebraMap S (Localization.Away g) f)` and
   `IsUnit (HomogeneousLocalization.Away.mk 𝒜 hg d (f ^ k) ...)`.
   By the constructor signature the latter is exactly f^k/g^d, not g^d/f^k.
   The inline `pow_mem_graded` proof only types the existing fraction.
   Verdict: both clauses present, no substantive result proved.
10. Clause (2): for each standard f, arbitrary `I : Type w` and ambient-open
    family `U`, the hypothesis `(⨆ i, U i) = basicOpen 𝒜 f` describes an open
    cover of the chart. Since the chart is open, subspace opens are precisely
    ambient opens contained in it; equality implies each `U i` is contained.
    The existential n,g,k over `Fin n` asserts positive homogeneous generators,
    equality with their union, and `∀ i, ∃ j, basicOpen 𝒜 (g i) ≤ U j`.
    Verdict: exact finite refinement, including empty covers.
11. Clause (3): all n,g,k and positive homogeneous membership proofs are bound
    before the iff. The inclusion into their union is equivalent to
    `Ideal.span (Set.range (fun i : Fin n ↦ Away.mk 𝒜 hf (k i) (g i ^ d) ...)) = ⊤`.
    These are g_i^d/f^k_i in S_(f), with correctly equal numerator and
    denominator degrees. Verdict: exact unit-ideal criterion.

Edge cases: no `Nontrivial S`, `IsDomain S`, `Nonempty I`, `n > 0` or nonzero
homogeneous-element condition is imposed. For nilpotent g (including zero), the
chart is empty, a positive power is zero with homogeneous witness a=0, and both
localizations are zero rings, where every element is a unit. A zero ring or a
ring concentrated in degree zero has empty Proj and satisfies the stated basis
and covering clauses. With n=0, clause (3) reads empty-chart inclusion iff the
zero ideal equals the unit ideal of S_(f), as required. An empty I is allowed,
and its covering equality forces the empty chart, refined with n=0. Degree-zero
f,g are excluded exactly by the source; degree-zero a is allowed. All
characteristics are covered. Universes u,v,w are explicitly bound; w is an
arbitrary cover index universe, not a test-algebra universe creating vacuity.

Independent searches (different queries from the worker):

- `msearch.py J1 lem-weil-pbc-proj-standard-open-inclusion leanfinder
  "Homogeneous principal opens in projective spectrum finite refinement radical
  divisibility criterion"`: eight hits. I opened `Proj.iSup_basicOpen_eq_top`,
  `Proj.mem_basicOpen` and the surrounding basis/cover declarations in Basic.lean.
  These concern the whole Proj, membership or chosen affine covers; none states
  the inclusion equivalence plus refinement and degree-zero ideal criterion.
- `msearch.py ... loogle "HomogeneousLocalization.Away.mk, IsUnit"`: zero hits.
- `rg` in Mathlib's ProjectiveSpectrum, upstream WeilConjectures (including its
  ProjectiveSpectrum extension), and repository lean/Sheaf for
  `basicOpen.*(iff|[Uu]nit|[Ss]pan|[Ff]inite)`, `standardOpenProperties`, and
  `[Ff]inite.*basicOpen`: no matching conjunction. The nearby Mathlib line 484
  uses a PrimeSpectrum inclusion iff while constructing a Proj morphism;
  upstream line 267 uses `Scheme.basicOpen_of_isUnit` for a different purpose.
  I read the actual `isBasis_basicOpen`, `basicOpen_mul`, `basicOpen_mono`,
  `iSup_basicOpen_eq_top` and `basicOpenIsoSpec` declarations: they provide
  constituent facts and charts, not this node's statement. The worker's recorded
  LeanSearch attempt was unavailable; its other searches and my successful
  LeanFinder/Loogle/grep searches supply independent coverage.

No mismatch found; no Lean, signature, node statement or dependency changes were
needed. There are no new definition nodes or dependency modules, and no statement
correction requiring citer review. The module uses the recorded definitions
transitively through its sole Mathlib import, introduces no private or hollow
definitions, and leaves its one theorem as `sorry`. The source/blueprint docstrings
are present, and their seven proof steps track all seven node steps, including
the separate basis, forward, converse, compactness and ideal-generation arguments.
No variables or universes are unbound. The existing node `lean.statement` is
verbatim the file signature. Second reading changed only this review report.
