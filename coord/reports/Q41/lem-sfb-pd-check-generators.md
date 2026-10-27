## Worker report

The module `Sheaf.RingTheory.DividedPowersCheckGenerators` states
`DividedPowers.exists_of_axioms_on_generators`, with its entire proof `sorry`.
It states Tag 07GP of `literature/stacks-project/dpa.tex`, read together with
Tag 07GL. Its docstring carries all seven steps of the node's proof, including
its integral coefficient argument. No definitions, new nodes, dependency
repairs, or statement corrections are needed. Only the node's `lean` changes.

The statement matches each hypothesis and conclusion as follows:

- The commutative ring is `{A : Type u} [CommRing A]`, with an explicitly
  declared, unrestricted universe `u`; the ideal is `I : Ideal A`.
- The generating set is `S : Set A` and `hS : I = Ideal.span S`.
  This expresses generation as an ideal and implies `S ⊆ I` by
  `Ideal.subset_span`; there is no finiteness assumption.
- The family of maps `I → I` for positive indices, with zeroth value one,
  uses the total-map representation expressly permitted in the recorded
  dependency. It is `g : ℕ → A → A`, `g_null` (extension by zero off `I`),
  `g_zero` (value one at degree zero on `I`), and `g_mem` (positive maps
  preserve `I`). These are representation conditions, not additional
  mathematical hypotheses: any maps in the node have exactly this extension,
  and restriction of such an extension recovers the maps in the node.
  In particular, degree zero need not preserve the ideal.
- Identity is `g_one`, for every element of `I`.
- Homogeneity is `g_mul`, for every positive `n`, every scalar `a : A`, and
  every `x ∈ I`; it uses ordinary multiplication `a * x`.
- Addition is `g_add`, for every positive `n` and `x,y ∈ I`. The finite sum
  over `Finset.range (n + 1)` includes both endpoints and uses `g_zero` there.
- Multiplication on generators is `g_mul_gens`, quantified over every `s ∈ S`
  and every positive pair `n,m`. Its coefficient is the natural binomial
  coefficient `((n + m).choose n : A)`.
- Iteration on generators is `g_comp_gens` with the same quantifiers. Since
  `S ⊆ I`, `g_mem` ensures `g m s` is again a legitimate ideal input.
  The coefficient `(Nat.uniformBell n m : A)` is the integer
  `(n*m)! / (n! * (m!)^n)`. Specifically `Nat.uniformBell_mul_eq` and
  `Nat.uniformBell_eq_div` identify this number when `m > 0`.
  There is no field structure, invertibility, division in `A`, or cancellation
  of an element of `A` in the signature.
- The conclusion `∃ γ : DividedPowers I, γ.dpow = g` means exactly that the
  supplied maps form the ordinary divided-power structure. It does not merely
  assert that some unrelated structure exists. Equality also fixes degree zero
  and values outside `I`, which are already fixed by the representation.
  The zero-index instances of the axioms in Mathlib are automatic from
  `g_zero`/`g_one` and the corresponding zero-index binomial/Bell formulas.

Dependency declarations read and used:

- `def-sfb-ordinary-divided-power-structure` is a Mathlib match, not an unstated
  node: `DividedPowers` in `Mathlib.RingTheory.DividedPowers.Basic`, lines 78--92.
  Read its full structure, documentation of the extension-by-zero convention,
  and the signatures of its five axioms. This module is publicly imported.
- The stated proof dependency `lem-sfb-pd-colour-profile-coefficients` is
  `Nat.colourProfile_coefficients` in
  `Sheaf.Combinatorics.ColourProfileCoefficients`; read its full signature and
  proof docstring. Its module is imported without `public` for stage 3.
- `Nat.uniformBell` and `Nat.uniformBell_eq_div` in
  `Mathlib.Combinatorics.Enumerative.Bell` (publicly available through Basic)
  supply the exact integral iteration coefficient.

Edge cases checked before writing: `S = ∅` forces `I = ⊥`, where homogeneity
with scalar zero forces all positive values at zero to vanish; the conclusion
is the ordinary zero-ideal structure. Infinite generating sets are allowed
because generation only uses finite sums. The zero ring is allowed. Arbitrary
positive characteristic and torsion are allowed because only natural-number
casts act in `A`. For `n = 1` or `m = 1`, the relevant binomial/Bell identities
specialize correctly. Degree zero is assigned one only on `I` and has no
ideal-membership requirement; this also covers proper ideals not containing
one. No operations in the proof require treating `g 0 x` as an ideal element.

Searches for an existing statement (2026-10-24):

- `msearch.py leanfinder`: “Divided power multiplication and iteration can be
  checked on an ideal generating set assuming addition and scalar homogeneity”.
  Eight hits, including `DividedPowers.dpow_eq_from_gens`,
  `DividedPowers.IsDPMorphism.on_span`, and `DividedPowers`; no constructor
  from the partial axioms. Read `DPMorphism.lean` lines 235--255: the first two
  require already supplied divided-power structures.
- `msearch.py loogle`: `"DividedPowers", "generat"`: zero hits.
- `msearch.py grep`: `generat|ofAxiom|check|dpow_eq_from_gens` in
  `RingTheory/DividedPowers`: ten hits; sub-DP ideals and uniqueness/morphism
  results do not establish the present construction.
- `msearch.py leansearch`: “A family of divided power maps satisfying addition
  and scalar homogeneity forms a divided power structure when multiplication
  and iteration hold on ideal generators”. Eight hits, principally
  `DividedPowers.mk` and the rational-algebra construction. The constructor
  requires all identities everywhere and the latter assumes rational scalars.
- `rg` in `lean/WeilConjectures/RingTheory`, `lean/Sheaf/RingTheory`, and
  `dag/lean_names_upstream.json` for `DividedPowers` and the proposed name:
  no existing construction or name collision. Project neighbours concern
  gluing, flat extension, graded structures, or the torsion-free factorial
  criterion. `rg` for this node id throughout `lean/WeilConjectures` has no hit.
  Broad name searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `check_on_generators|exists.*generators|of_generators|checkGenerators`
  likewise found no divided-power generator-check theorem.

Validation: `scompile.py Q41 lem-sfb-pd-check-generators` compiled the delivered
file as both sandbox and library module against the published server build,
without errors or warnings (2.7 s and 2.5 s respectively). All variables and
universes are explicitly bound; `autoImplicit` is disabled. No node faults or
statement disputes were found.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
