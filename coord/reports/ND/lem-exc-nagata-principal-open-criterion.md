## Worker report

The node is already stated by the exact source declaration
`Ideal.exists_notMem_forall_of_isNoetherianRing` in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`; no new module is needed.
Its signature is the node statement rendered in Lean:

```lean
theorem Ideal.exists_notMem_forall_of_isNoetherianRing {S : Type*} [CommRing S]
    [IsNoetherianRing S] (U : Ideal S → Prop)
    (hgen : ∀ P Q : Ideal S, P.IsPrime → Q.IsPrime → Q ≤ P → U P → U Q)
    (hloc : ∀ P : Ideal S, P.IsPrime → U P →
      ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → P ≤ Q → g ∉ Q → U Q)
    (P : Ideal S) [P.IsPrime] (hP : U P) :
    ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → g ∉ Q → U Q
```

The `[CommRing S]` and `[IsNoetherianRing S]` binders render the commutative
Noetherian ring hypothesis. `U : Ideal S → Prop` renders the predicate on
ideals. `hgen` renders clause (i): for prime `Q ≤ P`, `U P` implies `U Q`.
`hloc` renders clause (ii): for every prime `P` with `U P`, some `g ∉ P`
has `U Q` for every prime `Q` with `P ≤ Q` and `g ∉ Q`. The explicit
`[P.IsPrime]` and `hP : U P` render the chosen prime satisfying the property.
The conclusion `∃ g ∉ P, ∀ Q, Q.IsPrime → g ∉ Q → U Q` renders the required
principal open neighborhood.

The statement dependency is `def-weil-pbc-noetherian-ring`, recorded as the
Mathlib declaration `IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`.
The source theorem imports and uses this same Mathlib notion.

Edge cases checked: `U` may be false or true; the theorem is conditional on
`hP`, so the vacuous-failure case has no conclusion obligation. The chosen
prime `P` and all test ideals are arbitrary, including the zero and maximal
ideals; no nonzero or properness assumption is added. The quantifier over
all primes `Q` includes `P` itself and all generalizations.

Searches made: `msearch.py ... leanfinder` for “Nagata principal open criterion
for a property of prime ideals in a Noetherian commutative ring” (returned
related Noetherian-spectrum results but no exact match); `msearch.py ...
loogle` for `Ideal.exists_notMem_forall_of_isNoetherianRing` (unknown identifier);
`msearch.py ... grep` for `exists_notMem_forall_of_isNoetherianRing` (no Mathlib
hit); and `rg` over `WeilConjectures` and project `lean/Sheaf`, locating the
exact declaration in the recorded source module. The source file and theorem
docstring identify it as Nagata’s criterion, citing Stacks Tag 0541.

## Second reading by ND

I opened the node, its dependency record, and the source declaration
`Ideal.exists_notMem_forall_of_isNoetherianRing`. The node's objects,
hypotheses, and conclusion are rendered as follows.

* The commutative Noetherian ring `S` is rendered by `{S : Type*}`,
  `[CommRing S]`, and `[IsNoetherianRing S]`; this is exactly the dependency
  `def-weil-pbc-noetherian-ring` (Mathlib `IsNoetherianRing`).
* The predicate on ideals is `U : Ideal S → Prop`.
* Hypothesis (i), stability under generalization, is
  `hgen : ∀ P Q : Ideal S, P.IsPrime → Q.IsPrime → Q ≤ P → U P → U Q`.
  Thus `Q ≤ P` is the source's `q ⊆ p`.
* Hypothesis (ii), the relative principal neighborhood, is
  `hloc : ∀ P : Ideal S, P.IsPrime → U P →
    ∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → P ≤ Q → g ∉ Q → U Q`.
  The order `P ≤ Q` and `g ∉ Q` match the source's specializations and
  principal-open condition.
* The arbitrary prime where the property holds is `(P : Ideal S)
  [P.IsPrime] (hP : U P)`. The conclusion is
  `∃ g ∉ P, ∀ Q : Ideal S, Q.IsPrime → g ∉ Q → U Q`, exactly the required
  principal open containing `P`.

No mismatch was found and no Lean or node field was changed. The explicit
prime typeclass is the source declaration's way of introducing a prime ideal;
it adds no finiteness, nonzero, properness, or characteristic assumption.
The quantifiers include `Q = P`, the zero and maximal ideals when prime, and
all primes of the zero ring (vacuously when there are none); `U` may be either
truth value, with `hP` correctly making the conclusion conditional. There is
no index set, integer parameter, scheme, or universe restriction beyond the
polymorphic `Type*`, so the empty-spectrum and zero-ring cases remain covered.

For the one-definition-per-notion check I searched the project and Mathlib
with `rg` for `exists_notMem_forall_of_isNoetherianRing` and Nagata/open
criterion variants, and ran the recorded `msearch.py` LeanFinder, Loogle, and
grep searches. The only exact declaration is the source declaration in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`; Mathlib has
related constructible/generalization results but no equivalent theorem. The
dependency is the existing Mathlib `IsNoetherianRing`, so no module or helper
was added.

Source check: the local Stacks literature checkout is absent, so I read
`topology.tex` at `lemma-characterize-open-Noetherian` from the Stacks source
and [Tag 0541](https://stacks.math.columbia.edu/tag/0541). Its only ambient
hypothesis is a Noetherian topological space. For the affine formulation,
`V(p)` is irreducible with generic point `p`: generalization stability makes
any nonempty intersection with the property contain `p`, and `hloc` supplies
its relative open `D(g) ∩ V(p)`. Conversely a nonempty relative open contains
the generic point. Thus the node's affine form has precisely the needed
hypotheses; taking a basic-open neighborhood yields its conclusion. I also
read the upstream theorem's complete proof (intersection of failing primes,
minimal-prime argument, closed failure locus, then a separating element).

Independent searches on this reading: `msearch.py` LeanFinder for
“Noetherian ring prime property downward closed relatively open along every
V(p) principal neighborhood” returned spectrum-Noetherian facts, no exact
criterion; Loogle for `"IsPrime", "IsNoetherianRing"` returned no hits;
LeanSearch for “Nagata openness criterion for prime ideals” returned
constructible/generalization and specialized open-locus facts, no exact
criterion. Direct `rg` by declaration name over all Mathlib, upstream, and
`lean/Sheaf` found the upstream theorem and its use in Flat/Localization.
Concept searches for Nagata, openness criteria, and `exists_notMem_forall`
likewise found no competing definition. I read `IsNoetherian` and
`IsNoetherianRing` in Mathlib Noetherian/Defs, including
`isNoetherianRing_iff_ideal_fg`, to confirm the dependency's meaning.

The only wording repair in this second reading was to call `P ≤ Q`
specialization, not generalization; the Lean and node were already correct.
The delivery dry run compiled its generated existing-declaration check and
passed preflight; no delivered Lean modules require compilation.
