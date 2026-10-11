## Worker report

The module `lean/Sheaf/RingTheory/Etale/LocalDimension.lean` states
`RingHom.Etale.ringKrullDim_localization_eq`, with its proof left as `sorry`.
There are no definitions, additional nodes, dependency modules, or statement changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative rings A and B are `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  The independently bound universes impose no equality of universe sizes.
- The ring map A → B is `(f : A →+* B)`.
- Its being étale is `(hf : f.Etale)`, using Mathlib's `RingHom.Etale`.
- The prime ideal q of B is `(q : Ideal B) [q.IsPrime]`.
- Its inverse image p in A is written directly as `Ideal.comap f q`. Mathlib's
  `Ideal.IsPrime.comap` instance supplies its primality; no assumption on p is added.
- The localizations A_p and B_q are respectively
  `Localization.AtPrime (Ideal.comap f q)` and `Localization.AtPrime q`.
- The conclusion is their equality of `ringKrullDim`, in the node's order, A_p then B_q.
  Mathlib's value type `WithBot ℕ∞` retains infinite dimension and the empty-spectrum value.

Dependency declaration: `def-weil-pbc-krull-dimension-ring` has status `mathlib`;
its `mathlib_match` is `ringKrullDim` in `Mathlib.RingTheory.KrullDimension.Basic`.
I opened its complete definition and docstring: it is the order Krull dimension of
`PrimeSpectrum R`, matching the node's prime-chain definition. No `lean` record is
required on this Mathlib leaf. The file imports that module directly.

Other existing notions were read in Mathlib: `RingHom.Etale` in
`Mathlib.RingTheory.RingHom.Etale` is `Algebra.Etale` for `f.toAlgebra`;
`Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic` is
localization at the prime complement. `Ideal.IsPrime.comap` in
`Mathlib.RingTheory.Ideal.Maps` supplies the contraction instance.

Source verification: the local literature checkout has no Stacks source files, so I opened
https://stacks.math.columbia.edu/tag/07QP directly. Lemma 15.45.2 states exactly the node's
hypotheses and equality, with no Noetherian, domain, injectivity, or finiteness-of-dimension
assumptions. The node's older lemma number 44.2 is harmless; the stable tag agrees.
The declaration docstring records both proof steps and every proof dependency from the node.

Edge cases checked before writing: the identity map gives identical localizations;
field extensions that are étale give dimension zero on both sides; nonmaximal primes are
allowed because `q.IsPrime` is the only ideal hypothesis. Infinite Krull dimension is retained.
A zero target ring has no prime q, so the statement is vacuous there. A map from the zero
ring likewise cannot supply a prime of the target. Neither ring is explicitly assumed
nontrivial; nontriviality of the relevant local rings follows from the chosen prime.
No characteristic restriction is present or required. There is no statement dispute.

Searches (all performed before writing the theorem):

- `msearch.py ... leansearch "etale ring homomorphism dimension localizations at prime ideals"`:
  UNAVAILABLE, Internal Server Error; no search verdict inferred from that failure.
- `msearch.py ... leanfinder "For an etale map of commutative rings the localizations at a prime
  and its contraction have equal Krull dimension"`: eight hits, including
  `Algebra.exists_etale_of_isEtaleAt`, `Algebra.IsEtaleAt`, and étale localization properties;
  none states the dimension equality.
- `msearch.py ... loogle "ringKrullDim, Localization.AtPrime"`: zero hits.
- `msearch.py ... grep "ringKrullDim.*[Ee]tale|[Ee]tale.*ringKrullDim" RingTheory`: zero hits.
- `rg` on `WeilConjectures/` and `lean/Sheaf` for
  `etale.*dimension|dimension.*etale|ringKrullDim|lem-sc-etale-local-dimension`:
  existing dimension and étale results, including localization-height and integral-extension
  dimension results, but no étale local dimension equality.
- Targeted `rg` on Mathlib, `WeilConjectures/`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `ringKrullDim_localization_eq`: no collision.
  A second targeted search for `ringKrullDim.*[Ee]tale|[Ee]tale.*ringKrullDim` and the
  blueprint id in the source/project and upstream name index found no matching declaration.

Validation: the server single-file compile and `deliver2.py --no-push` are run for this
sandbox. The dry run must pass before this item is marked READY. The second reading and
actual delivery are reserved for the independently dispatched second worker.

## Second reading by F1

I independently read the node, the delivered file, and the sole statement dependency
`def-weil-pbc-krull-dimension-ring`, including its recorded Mathlib declaration.
Object/hypothesis/conclusion checklist (all verdicts: exact):

- Arbitrary commutative rings A and B: `{A : Type u} {B : Type v}` with
  `[CommRing A] [CommRing B]`. Independent, explicitly declared universes; no
  nontriviality, Noetherian, domain, field, or dimension bound is assumed.
- Ring map A to B: `(f : A →+* B)`. No independent algebra structure is assumed.
- Etaleness: `(hf : f.Etale)`. I read `RingHom.Etale` in
  `Mathlib.RingTheory.RingHom.Etale`: it uses precisely `f.toAlgebra`.
  `Algebra.Etale` in `Mathlib.RingTheory.Etale.Basic` is formal etaleness plus
  finite presentation, with the documented equivalence to Stacks' etaleness.
- Prime q of B: `(q : Ideal B) [q.IsPrime]`; q need not be maximal.
- Its inverse image p in A: `Ideal.comap f q`. I read the contraction API in
  `Mathlib.RingTheory.Ideal.Maps`, including the `Ideal.IsPrime.comap` instance.
  Substituting the defined p introduces no restriction and requires no extra hypothesis.
- Local rings A_p and B_q: `Localization.AtPrime (Ideal.comap f q)` and
  `Localization.AtPrime q`. I opened `Mathlib.RingTheory.Localization.AtPrime.Basic`:
  the abbreviation is `Localization P.primeCompl`, exactly the prime localization.
- The only conclusion, in the stated order: equality of `ringKrullDim` of those
  two rings. I read `ringKrullDim` in `Mathlib.RingTheory.KrullDimension.Basic`
  and `Order.krullDim` in `Mathlib.Order.KrullDimension`. The value is the supremum
  of strict prime-chain lengths in `WithBot ℕ∞`, exactly the dependency node's
  notion, including both infinities. No clause or quantifier is lost or added.

Source: the repository's literature checkout has no Stacks .tex files. I fetched
the official upstream `more-algebra.tex` into this sandbox and read
`section-permanence-etale`, including its opening conventions, and
`lemma-dimension-etale-extension` (lines 10794–10855). I also checked
https://stacks.math.columbia.edu/tag/07QP, which identifies this as Lemma 15.45.2.
The section assumes only an etale ring map; it recalls etale implies flat and
flat local implies faithfully flat. No standing Noetherian hypothesis is present.
The source and node agree, so no statement correction or citer audit is needed.

Edge cases: either zero ring forces absence of the required prime q (a unital map
from the zero ring forces B to be zero), so those cases are correctly vacuous.
Dimension zero, fields, nonmaximal primes, positive and zero characteristic, and
unbounded dimension are admitted. The identity map gives equal localizations.
There is no index family or scheme object to restrict; an empty spectrum cannot
supply q. Chains of length zero are retained by `Order.krullDim`. Independent
universes u and v cover differently sized rings without any Small or finiteness instance.

Independent searches, using alternative terminology:

- `msearch.py ... leanfinder "The height of a prime ideal is unchanged by an etale
  homomorphism after contracting the prime"`: eight hits. The height results concern
  localization or Noetherian going-down dimension formulae, and the etale results
  concern composition; none is this statement.
- `msearch.py ... loogle '"Etale", "ringKrullDim"'`: no hits.
- `msearch.py ... grep
  '(height|krull|dimension).*(etale|étale)|(etale|étale).*(height|krull|dimension)'
  RingTheory`: 17 hits, on standard smooth relative dimension zero, not local
  Krull dimension invariance.
- I independently ran the same broad pattern and the proposed declaration name
  over `WeilConjectures/`, `lean/Sheaf`, and `dag/lean_names_upstream.json`.
  I followed the plausible `Scheme.Etale.coheight_hom_apply` hit into
  `Sites/DivisorMap.lean` and its dependency `Scheme.Hom.coheight_apply_of_flat`
  in `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean`. These concern
  coheight of points of schemes, not this ring-localization signature. They are
  potential proof tools, not an exact existing declaration for this node.
  No collision for `RingHom.Etale.ringKrullDim_localization_eq` was found.

H5–H9: no definitions or hollow data; the only proof is `by sorry`. The declaration
and module docstrings cite Tag 07QP and the correct blueprint id. The proof docstring
contains both inequalities and all six proof dependencies, followed by antisymmetry.
All imports supply notions used in the signature; the namespace, header, explicit
binders, and line widths conform. No new nodes or dependency modules need review.

Mismatches and repairs: none found. I preserved the Lean module and node record,
including the verbatim `lean.statement`; only this independent review was added.
The explicit server single-file compile passed cleanly (1.6 seconds, no warnings).
