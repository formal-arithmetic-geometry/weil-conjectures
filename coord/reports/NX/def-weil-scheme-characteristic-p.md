## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SchemeCharacteristic.lean` defines
`AlgebraicGeometry.Scheme.IsCharacteristic`.  It takes a scheme `X` and a natural
number `p`, and states `Nat.Prime p ∧ ∀ U : X.Opens, (p : Γ(X, U)) = 0`.
The first conjunct renders the node's hypothesis that `p` is prime.  The universal
quantifier over `U : X.Opens` renders “for every open subset”.  The equality renders
that `p · 1` is zero in the structure-sheaf section ring (natural-number coercion is
multiplication by one).  Since the quantifier is over all opens, this includes the
empty open and therefore the empty scheme, whose section ring is subsingleton.

The statement dependencies are used as follows.  `def-pc-scheme` is Mathlib's
`AlgebraicGeometry.Scheme`, imported from `Mathlib.AlgebraicGeometry.Scheme`.
`def-weil-locally-ringed-space-morphism` is a Mathlib notion of the underlying
locally ringed-space morphisms and contributes no additional term to this predicate;
the structure sheaf sections are the scheme notation `Γ(X, U)` from the same Mathlib
module.

Edge cases checked: `p = 0` and `p = 1` are rejected by `Nat.Prime p`; the empty open
and empty scheme are covered by the universal quantifier and the subsingleton section
ring; no affine, nonempty, reduced, or finite-type hypothesis is introduced.

Searches for an existing declaration:

- `msearch.py ... leanfinder "scheme of characteristic p every open structure sheaf section p times one is zero"`: only ring-level `CharP`/perfection and unrelated scheme predicates; no match.
- `msearch.py ... leansearch "scheme of characteristic p structure sheaf p is zero"`: service unavailable (Internal Server Error); the other search methods were used.
- `msearch.py ... loogle "Scheme IsOfCharacteristic CharP Γ"`: zero hits (Loogle did not recognize `Scheme`).
- `msearch.py ... grep "characteristic.*scheme|CharP.*Γ" AlgebraicGeometry`: zero hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf/`: only ring-level `CharP` uses and Frobenius consumers; no scheme-characteristic predicate.
- `grep`/`rg` over `dag/nodes`: no existing node carrying this notion besides this node.

The module compiles cleanly with `scompile.py`; the expected `sorry` warning does not
arise because this is a definition with real data.

Source verification: the local TeX source is absent, so the first paragraph of
[Stacks Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6) was opened directly.
It fixes a prime number and defines characteristic by vanishing in the structure
sheaf, exactly as the node states. No statement correction or new dependency is needed.

The upstream `Scheme.natCast_eq_zero_of_natCast_top_eq_zero` in
`WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius` transports the global-section
equality to each open, but does not define the requested predicate. Its `iterateFrobenius`
consumes this equality. `CharP Γ(X, ⊤) p` is not used: on the empty scheme the
zero ring has characteristic one in Mathlib, while the node permits every prime.
For the empty scheme all opens are bottom, and Mathlib's subsingleton instance
on `Γ(X, ⊥)` makes the required equality hold for every prime. For a nonempty
scheme, the definition still includes the empty open and imposes no nontriviality
on its section ring.

No theorem is proved, no `sorry` is introduced, and no node fault was found.
The independent second reading is left to the second worker.

## Second reading by NX

I independently read the sandbox node and module, both dependency node records,
and their Mathlib declarations. I also read the opening of the actual Stacks
`varieties.tex`, section `section-frobenius`, lines 6427–6439 in the
[published TeX source](https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex),
and [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6). The paragraph assumes
only a prime number and a scheme. In particular, the chapter title does not impose
a ground field, finite type, or a variety hypothesis here.

The complete object, hypothesis, and defining-clause checklist is:

1. A prime number `p`: `(p : ℕ)` and `Nat.Prime p`, the first conjunct of
   `Scheme.IsCharacteristic`. Verdict: exact. Including primality in the predicate
   records the source's domain of definition without requiring an extra instance.
2. An arbitrary scheme `X` from `def-pc-scheme`: `(X : Scheme.{u})` uses the
   recorded `AlgebraicGeometry.Scheme`, a locally ringed space locally isomorphic
   to affine spectra. Verdict: the same object, with no additional assumptions.
3. The structure sheaf from `def-weil-locally-ringed-space-morphism`:
   `Γ(X, U)` expands in Mathlib's Scheme module to `X.presheaf.obj (op U)`.
   I checked `LocallyRingedSpace` extends `SheafedSpace CommRingCat.{u}` and its
   recorded `LocallyRingedSpace.Hom` extends a continuous map and a map of these
   presheaves, with local stalk homomorphisms. Verdict: these are the actual
   structure-sheaf section rings. No morphism is required by this definition.
   The Scheme import already imports the locally ringed-space module.
4. Every open subset `U` of `X`: `∀ U : X.Opens`, where the Mathlib abbreviation
   is `TopologicalSpace.Opens X`. Verdict: all opens, in the required quantifier
   position, including bottom and top; no affine-open restriction.
5. The section `p · 1` is zero in each section ring:
   `(p : Γ(X, U)) = 0`. Natural-number casting is precisely the sum of `p` copies
   of the ring unit. Verdict: exact vanishing condition, without requiring exact
   ring characteristic or nontriviality.
6. The empty scheme satisfies the condition for every prime in the source's
   scope: its only open is empty, and the sheaf axiom makes its section ring the
   zero ring. The universal equality therefore holds. Verdict: preserved;
   `Nat.Prime p` remains the source's standing qualification on `p`.

Edge cases: bottom opens in any scheme and the empty scheme are included, and
zero section rings are permitted. `p = 0`, `p = 1`, and composite `p` fail the
prime conjunct, as required by the opening hypothesis. Nonreduced and disconnected
schemes are included. There is no index set or degree `n` in this notion, so their
empty and zero cases introduce no further binders. The explicitly declared
universe `u` is arbitrary; the opens and section rings inherit the universe of
the same scheme. There are no unbound variables, independent test universes,
nonemptiness assumptions, or hidden typeclass hypotheses.

I repeated searches with different wording through `msearch.py`, recording them
in this sandbox's `searches.jsonl`:

- LeanFinder: `A locally ringed space whose section rings annihilate a prime
  integer, including the zero ring`. Eight hits describe reduced schemes and
  affine spectra, not this characteristic predicate.
- Loogle: `"natCast", "Scheme"`. No hits.
- LeanSearch: `A prime number vanishes in every ring of regular functions on a
  scheme`. The service returned Internal Server Error; this is recorded as
  unavailable, not as evidence of absence.
- Mathlib grep, AlgebraicGeometry: `IsCharacteristic|HasCharacteristic|natCast.*zero|CharP|ringChar`.
  Fifteen hits concern coefficient rings of elliptic curves; none defines this
  predicate.

I additionally searched `WeilConjectures/`, `lean/Sheaf/`, the upstream name
index, and `dag/nodes/` for `IsCharacteristic`, `HasCharacteristic`, characteristic
of a scheme or ringed space, and vanishing of natural-number casts. I opened the
candidate interfaces in `AbsoluteFrobenius.lean`,
`FourierTransform/ArtinSchreier.lean`, and the project's
`ArtinSchreierSequenceScheme.lean`. The first supplies the theorem
`Scheme.natCast_eq_zero_of_natCast_top_eq_zero` and the Frobenius construction;
the Artin–Schreier interfaces consume either `CharP Γ(X, ⊤) p` or explicit
vanishing and primality. They do not define this notion. I checked Mathlib's
`CharP` field `cast_eq_zero_iff`: it requires vanishing exactly at multiples of
`p`, so imposing it on every section ring would exclude the zero ring for prime
`p`. It is therefore not an exact replacement. The DAG search finds consumers
and this node, with no second definition node for the same notion.

No mathematical mismatch was found, and I changed no Lean declaration or node
statement. There are no new nodes, dependency modules, or statement corrections
to audit. The definition has real propositional data and no `sorry`, auxiliary
theorem, private notion, file-local notation, or local instance. Its module and
declaration docstrings both name the source and blueprint ID. The node has no
proof steps, so no theorem proof docstring is required. I checked the recorded
`lean.statement` is verbatim the declaration signature before `:=` and all Lean
lines fit the 100-character limit. The only delivery change from this reading
is this independent report section. `scompile.py NX
def-weil-scheme-characteristic-p` compiled the sole delivered module cleanly,
without warnings, using the prescribed isolated wrapper.
