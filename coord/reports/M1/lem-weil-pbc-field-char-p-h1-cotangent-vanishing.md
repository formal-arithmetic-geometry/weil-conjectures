## Worker report

The module `Sheaf.RingTheory.SubsingletonH1CotangentOfCharP` states
`Algebra.subsingleton_h1Cotangent_of_charP`, with its sole proof `sorry`.
It introduces no definitions, extra nodes, or dependency modules. The item node
is unchanged except for `lean`.

Hypothesis and clause correspondence:

- “Let K be a field”: `(K : Type u) [Field K]`, with explicit arbitrary universe `u`.
- “of characteristic p > 0”: `(p : ℕ) (hp : 0 < p) [CharP K p]`.
  No separate primality assumption is needed: positive characteristic of a field
  is necessarily prime. This includes every field covered by the node.
- “an F_p-algebra in the unique way”: the conclusion starts with
  `letI := ZMod.algebra K p`. `ZMod p` is F_p because p is prime, and
  `ZMod.instSubsingletonAlgebra` makes all choices of this structure equal.
  No externally supplied algebra structure or compatibility hypothesis is imposed.
- “H_1(L_{K/F_p}) = 0”: `Subsingleton (H1Cotangent (ZMod p) K)`.
  This is precisely zero for this additive group: it has a zero element, so
  having all elements equal is equivalent to every element being zero.
- “the naive cotangent complex of the canonical presentation F_p[K] → K”:
  `Algebra.H1Cotangent R S` abbreviates
  `(Algebra.Generators.self R S).toExtension.H1Cotangent`, not the homology of
  an arbitrary unspecified presentation. `Generators.self` takes one variable
  for each element of S and evaluates it at that element. `Extension.H1Cotangent`
  is the kernel of `cotangentComplex`, on the conormal module I/I².
  Its target `S ⊗[R[S]] Ω[R[S]/R]` is the usual free S-module on the variables;
  `cotangentComplex_mk` sends g modulo I² to `1 ⊗ D g`, whose coordinates are
  the evaluated partial derivatives in the node. Thus no presentation or
  homology comparison hypothesis was added.

Dependency declarations read and used:

The sole statement dependency is `def-weil-pbc-smooth-ring-map`, status `mathlib`.
Its `mathlib_match` records `Algebra.Smooth` in `Mathlib.RingTheory.Smooth.Basic`,
and its `how` explicitly records `Algebra.H1Cotangent` as the canonical
presentation's first homology. The present theorem uses the latter part of that
node, importing `Mathlib.RingTheory.Extension.Cotangent.Basic`. I read
`Algebra.Smooth`, `Algebra.FormallySmooth`, `Algebra.H1Cotangent`,
`Algebra.Extension.H1Cotangent`, `Algebra.Extension.cotangentComplex`, and
`Algebra.Generators.self`, including their signatures and docstrings. Smoothness
is used in the natural-language proof, not as a hypothesis of the statement;
there is consequently no unused import of `Smooth.Basic`. The other import,
`Mathlib.Algebra.Algebra.ZMod`, provides the canonical `ZMod.algebra` and its
uniqueness instance.

Source check: local `literature/stacks-project/algebra.tex` is absent on this
machine. I opened [Stacks 0322](https://stacks.math.columbia.edu/tag/0322),
characteristic-p conditions (1) and (5), and
[Stacks 07E5](https://stacks.math.columbia.edu/tag/07E5), proof of (3) ⇔ (4).
They support exactly the node's assertion; the module docstring follows the
node's full three-step proof: separability via 030R and the prime field,
localization of a smooth algebra for each finitely generated subfield, and
finite support of a representative cycle to pass to arbitrary K.

Edge cases checked before writing:

- p = 0 is excluded exactly by the source's positivity; p = 1 and positive
  composite p cannot occur as a field's characteristic. There is no added
  `Fact p.Prime` binder.
- K = F_p and finite extensions are included.
- Transcendental extensions, arbitrary large transcendence degree, and infinite
  algebraic or perfect closures are included. In particular the perfect closure
  of F_p(t) is not excluded by an essential-finite-type or separably-generated
  assumption. Each cycle still involves only finitely many variables.
- The zero ring is not a field in Mathlib, matching the mathematical convention.
- Zero homology is stated as subsingleton of an existing additive group, not an
  empty type; there is no finite-dimensionality requirement or dimension test.

Searches made (2026-10-11; full tool summaries in sandbox `searches.jsonl`):

- `msearch.py ... leansearch "H1Cotangent of an arbitrary field of positive
  characteristic over ZMod p is zero"`: service unavailable, Internal Server
  Error. No mathematical verdict assigned to this unavailable search.
- `msearch.py ... leanfinder "For any field K of characteristic p > 0, the first
  homology of the naive cotangent complex over F_p vanishes"`: eight hits,
  including `Algebra.H1Cotangent`,
  `Algebra.FormallySmooth.subsingleton_h1Cotangent`, and standard-smooth and
  formally-étale analogues. None states the arbitrary-field assertion without
  additional assumptions.
- `msearch.py ... loogle "Algebra.H1Cotangent, ZMod"`: successful, zero hits.
- `msearch.py ... grep "H1Cotangent|of_perfectField" RingTheory/Smooth`:
  nineteen hits; read `Smooth/Field.lean` in full. `of_perfectField` requires
  `Algebra.EssFiniteType`, and `of_algebraicIndependent_of_isSeparable` requires
  a separating transcendence basis. Neither covers arbitrary K here.
- `rg -n 'H1Cotangent|h1Cotangent|cotangent.*vanish'` on the source's
  `WeilConjectures` and this project's `lean/Sheaf`: no source matches;
  project hits concern Cartier equality and a reference to another étale lemma,
  neither the present assertion. `grep -rn` of this item's id on
  `WeilConjectures`: no matches.
- `rg -n 'subsingleton_h1Cotangent_of_charP|subsingleton_h1Cotangent_zmod'`
  on `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and
  `lean/Sheaf`: no existing declaration with the proposed name.
- Read `Algebra/Algebra/ZMod.lean` to verify `ZMod.algebra` and uniqueness;
  read `Extension/Generators.lean` and `Extension/Cotangent/Basic.lean` to
  verify the canonical presentation, differential, and homology carrier.

No statement fault or disputed assertion was found. The remote single-file
compile passed without errors or warnings on 2026-10-11. The second reader
will supply the independent reading and deliver; this worker only dry-runs.


## Second reading by M1

I independently read the repository node, its sole statement dependency
`def-weil-pbc-smooth-ring-map`, the sandbox node and Lean module, and the
actual Mathlib declarations described below. The node's objects, hypotheses,
and conclusion, listed before matching them, are:

1. An arbitrary field K. Lean: `(K : Type u) [Field K]`, with `universe u`
   explicitly declared. Verdict: exact; no finite generation, cardinality,
   Noetherian, perfectness of K, or separable-generation hypothesis occurs.
2. Its characteristic is an integer p > 0. Lean: `(p : ℕ) (hp : 0 < p)`
   and `[CharP K p]`. Verdict: exact. Primality follows from field
   characteristic and positivity; it is not an additional instance binder.
3. The base is F_p and K has its unique F_p-algebra structure. Lean:
   `letI := ZMod.algebra K p` followed by base ring `ZMod p`.
   Verdict: exact. I read `ZMod.algebra`, which uses `ZMod.castHom` for
   the characteristic-p ring, and the `Subsingleton (Algebra (ZMod p) R)`
   instance in `Mathlib.Algebra.Algebra.ZMod`. Thus no algebra structure
   or compatibility condition is requested from the caller.
4. The homology is that of the canonical polynomial presentation F_p[K] → K,
   not a different cohomology or an unspecified complex. Lean:
   `Algebra.H1Cotangent (ZMod p) K`. Verdict: exact. The abbreviation in
   `Mathlib.RingTheory.Extension.Cotangent.Basic` expands to
   `(Generators.self R S).toExtension.H1Cotangent`. I read `Generators.self`
   in `Extension/Generators.lean`: variables are indexed by all of S,
   `val := id`, and the section sends s to `X s`. `toExtension` uses that
   polynomial ring and its surjective evaluation. I also read
   `Extension.Cotangent` in `Extension/Basic.lean` (the conormal module),
   `Extension.cotangentComplex`, its formula `cotangentComplex_mk`, and
   `Extension.H1Cotangent` (the kernel of this linear map). The map sends
   a relation to `1 ⊗ D g`; for a polynomial algebra its components are
   precisely the evaluated partial derivatives in the dependency node.
5. The sole conclusion is H_1(L_{K/F_p}) = 0. Lean:
   `Subsingleton (H1Cotangent (ZMod p) K)`. Verdict: exact. This carrier
   has an AddCommGroup instance and zero, so subsingleton means every
   homology class equals zero; it cannot merely assert an empty carrier.
   There are no extra conclusions. The binder order introduces p and its
   positivity before K, then its field and characteristic instances; it
   expresses the same universal assertion without a restricted quantifier.

Source reading: the repository does not contain `literature/stacks-project/`
TeX on this machine. I fetched the official Stacks algebra.tex into this
item's scratchpad and read `proposition-characterize-separable-field-extensions`
(Tag 0322), including the surrounding field-extension setting, and
`definition-perfect` / `lemma-perfect` (030Y / 030Z). The positive-characteristic
conditions (1) and (5) give exactly this vanishing over the perfect prime field;
there is no finite-type hypothesis in that proposition. I also read the proof
of (3) ⇔ (4) of https://stacks.math.columbia.edu/tag/07E5, which explicitly uses
this assertion for the residue field K. Its ambient Noetherian local algebra
belongs to that application and is not a hypothesis of 0322 or this node.
The primary source links are https://stacks.math.columbia.edu/tag/0322 and
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex.

Dependency review: the sole dependency has no `lean` record and its
`mathlib_match` names `Algebra.Smooth` in `Smooth/Basic.lean`, explaining its
canonical `Algebra.H1Cotangent` clause. I opened `Smooth`, `FormallySmooth`,
and the underlying homology declarations, rather than relying on that name.
The dependency's conormal-complex notion is usable through these declarations;
this theorem needs its H_1 notion, not a smoothness hypothesis. No dependency
module, private definition, or new node is needed. There is one delivered
module and one node. The sandbox node has no statement correction and matches
the base outside its `lean` record, so there are no corrected-statement citers
to recheck and no new-node/dependency-module review obligations.

Edge cases: p = 0 is excluded exactly as stated. A field cannot have p = 1
or positive composite characteristic. K = F_p, finite extensions, arbitrary
transcendental extensions, and infinite algebraic/perfect closures remain
included. In particular the perfect closure of F_p(t) needs no separating
transcendence basis binder here. The zero ring is excluded by Field, as in
the source. The canonical index set K is never empty for a field and is not
required to be finite. A finite-support cycle involving no variables (the
empty generating list, n = 0) is not excluded. There are no scheme or degree
parameters to restrict. Arbitrarily large `Type u` fields are covered, while
the fixed prime field is small exactly as mathematically appropriate.

Independent searches (2026-10-11, using different phrasing from the worker):

- LeanFinder via msearch: “The conormal differential for the evaluation
  presentation of a positive characteristic field over its prime subfield
  is injective”. Eight hits, including
  `Algebra.SubmersivePresentation.cotangentComplex_injective`,
  `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`, and the
  local residue-field criterion. Their signatures require a submersive
  presentation or formal-smoothness/local conditions, or concern a different
  map. None is this unconditional arbitrary-field assertion.
- Loogle via msearch: `Algebra.H1Cotangent, "field"`. Zero hits.
- LeanSearch via msearch: “The kernel of the naive cotangent differential
  of a field over a finite prime field is zero”. Service unavailable
  (Internal Server Error); this has no mathematical search verdict.
- Direct rg of Mathlib `Smooth/Field.lean` and `Etale/Field.lean` for
  `H1Cotangent|PerfectField|ZMod`, and reading Smooth/Field in full:
  `Algebra.FormallySmooth.of_perfectField` requires `Algebra.EssFiniteType`;
  `of_algebraicIndependent_of_isSeparable` requires a separating family and
  separability over its generated intermediate field. Neither states the
  arbitrary-field node. The existing smoothness-to-H_1 instance is a tool,
  not the assertion being delivered.
- Direct rg on `WeilConjectures/` and repository `lean/Sheaf/` for
  `H1Cotangent|cotangentComplex.*injective|formallySmooth.*[Pp]erfect` and
  its reversed wording: source has no match; project hits are Cartier
  equality and localized cotangent vanishing away from an étale locus,
  neither this assertion. Name/source-description search of those trees
  and `dag/lean_names_upstream.json` also found no existing declaration.

Conventions and repairs: no mathematical or Lean mismatch found; no Lean
or node changes made. Both imports are used. There is no definition or
hollow data. The sole theorem proof remains `by sorry`, as stage 2 requires.
The module and declaration docstrings name the source and blueprint id;
I matched their three numbered proof steps to the node: separability via
030R and the prime field, localization of a smooth algebra, and finite
support reduction of a relation to a finitely generated subfield. All
variables and the universe are bound, the namespace has no Sheaf prefix,
and the longest Lean line is 90 characters. The node's `lean.statement`
is byte-for-byte the theorem signature ending before `:=`.

Validation: independent server single-file compile passed cleanly (1.3 s),
with exit code 0 and no warnings.
