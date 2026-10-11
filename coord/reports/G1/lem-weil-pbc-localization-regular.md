## Worker report

The module `Sheaf.RingTheory.LocalizationRegular` states
`IsLocalization.isRegular_and_fiber`, with its entire proof left as `sorry`.
No new definitions, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The commutative rings S and S′ are `{S : Type u} {T : Type v}` with
  `[CommRing S] [CommRing T]`. Independent explicit universes admit all ring sizes.
- The multiplicative subset W is `(W : Submonoid S)`.
- The map λ is the arbitrary structure map of `[Algebra S T]`, namely `algebraMap S T`.
  Any commutative-ring homomorphism gives this algebra structure via `RingHom.toAlgebra`;
  no injectivity or finite-generation assumption is imposed.
- Localization conditions (a), (b), (c) are `[IsLocalization W T]`. Reading
  `isLocalization_iff` in Mathlib/RingTheory/Localization/Defs.lean shows respectively:
  units on W; each z has z λ(w) = λ(s); equality of images is killed by some denominator.
  The second is the fraction condition because λ(w) is a unit. The third is equivalent
  to the node's zero-kernel condition by applying it to s−t; conversely put t=0.
- Regularity of λ is `RingHom.IsRegular (algebraMap S T)`, the first conjunct.
- Every prime ideal and its primality are `∀ (p : Ideal S) [p.IsPrime]`.
- The residue field is `p.ResidueField`, and the fibre is `p.Fiber T`.
  Mathlib orders its tensor factors as κ(p) ⊗[S] T. The tensor swap identifies it
  as a κ(p)-algebra with the node's T ⊗[S] κ(p); this is the mandated fibre convention.
- Disjointness p ∩ W = ∅ is `∀ w : W, (w : S) ∉ p`. In this case the conclusion
  `Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)` is an algebra isomorphism
  over precisely the residue field, not only a ring isomorphism.
- The otherwise case is `∃ w : W, (w : S) ∈ p`, and `Subsingleton (p.Fiber T)`
  says the fibre is the zero ring. A ring is inhabited, so subsingleton is equivalent
  to having exactly one element (equivalently 0=1). The two conditional clauses
  exhaust the cases without adding any hypothesis.

Dependencies read and used:

- `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `RingHom.IsRegular` and its
  underlying `Algebra.IsGeometricallyRegular`. The full module was read: regularity
  means flatness and geometrically regular fibres, with Noetherianity included in
  geometric regularity. Its definition is imported and used directly.
- `def-weil-pbc-localization-at-prime` is a Mathlib leaf: `Localization.AtPrime`
  in `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and `Ideal.Fiber` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. Their signatures and docstrings
  were read, along with `Ideal.Fiber.algEquivQuotient`. These imports are already
  provided by GRing; there is no private localization or residue-field definition.

Edge cases checked: W={1} gives the identity localization and residue-field fibres;
if 0∈W, T is the zero ring and every fibre is zero; for the zero base ring there
are no primes and the fibre clauses are vacuous. A prime meeting W need not
survive in T, which is exactly why the zero-fibre clause is necessary. No
Noetherian assumption on the original rings is required: the fibres themselves
are fields or zero. Arbitrary characteristics and arbitrary denominator sets
are admitted. No statement dispute was found.

Sources: the local literature checkout contains only citation lists, so the specified
source places were opened at https://stacks.math.columbia.edu/tag/07PT and
https://stacks.math.columbia.edu/tag/07BZ. The former asserts regularity of a
localization in its proof; the latter defines regularity exactly as the dependency.
The declaration docstring records all six DAG proof steps and their dependencies.

Searches performed using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanSearch: `A localization of a commutative ring is a regular ring map with residue
  field or zero fibers`; service unavailable (Internal Server Error), logged as unavailable.
- LeanFinder: `localization regular ring map fibre at prime ideal is residue field or zero`;
  eight hits included `Ideal.Fiber`, localization-at-prime quotient lemmas, regular
  sequences, and unramified maps. None states this theorem.
- Loogle: `IsLocalization, Ideal.Fiber`; no hits.
- Mathlib grep: `IsRegular|geometrically.?regular|subsingleton_iff|atUnits` under
  RingTheory/Localization; 18 hits. Relevant constituents are `IsLocalization.atUnits`
  and `IsLocalization.subsingleton_iff`; none includes regular-map regularity and both fibres.
- `rg` over source `WeilConjectures` and project `lean/Sheaf` for the item id and
  `isRegular.*[Ll]ocaliz|localization.*[Rr]egular`: no declaration stating this item;
  project proofs merely mention its id, and the source hits concern localizations
  of regular rings, a different statement. Additional full-name searches for
  `isRegular_of_isLocalization|isRegular_localization` in the source, project, and
  `dag/lean_names_upstream.json` found no collision with the chosen name.

The theorem is the only declaration and only sorry. The node is copied with only
its `lean` field changed. The independent second reader supplies the second-reading
section and performs the actual delivery.

## Second reading by G1

I independently read the item node, its two statement dependency nodes, the
entire delivered Lean module, and `Sheaf.RingTheory.GRing`. No mathematical
mismatch was found; the Lean and node record were preserved. This reading
adds this report section and independent search records only.

Object, hypothesis, and conclusion inventory, matched against the Lean:

1. A commutative ring S and a commutative target ring S′: `{S : Type u}`,
   `{T : Type v}`, `[CommRing S]`, `[CommRing T]`. Verdict: exact; neither
   ring is required to be a domain, nonzero, Noetherian, or finitely generated.
2. A multiplicative subset W: `(W : Submonoid S)`. Verdict: exact; includes
   1 and is closed under multiplication, without forbidding 0.
3. The ring map λ:S→S′: `[Algebra S T]` and `algebraMap S T`.
   Verdict: exact; any unital commutative-ring homomorphism is represented
   by its `RingHom.toAlgebra`, without an additional mathematical hypothesis.
4. Localization condition (a), λ(W) consists of units: `[IsLocalization W T]`
   renders this through the first conjunct of `isLocalization_iff`.
   Verdict: exact.
5. Condition (b), all elements are fractions λ(s)/λ(w): the second conjunct
   of `isLocalization_iff` gives `z * algebraMap S T w = algebraMap S T s`.
   Verdict: exact because condition (a) makes the denominator invertible.
6. Condition (c), λ(s)=0 implies some w∈W kills s: the third conjunct of
   `isLocalization_iff` gives equality of images iff a denominator kills
   their difference. Verdict: exact; specialize y=0 in one direction,
   apply condition (c) to x−y in the other.
7. Conclusion λ is regular: `RingHom.IsRegular (algebraMap S T)`.
   Verdict: exact. The dependency's definition uses the same ring map's
   induced algebra structure, flatness, and all prime fibres, with fibre
   Noetherianity inside `Algebra.IsGeometricallyRegular`.
8. Every prime p and its residue field κ(p): `∀ (p : Ideal S) [p.IsPrime]`
   and `p.ResidueField`. Verdict: exact; read `Localization.AtPrime` in
   AtPrime/Basic.lean and `Ideal.ResidueField` in ResidueField/Ideal.lean.
   The latter is the residue field of precisely the prime localization.
9. The fibre S′⊗[S]κ(p), as a κ(p)-algebra: `p.Fiber T`.
   Verdict: exact under the project's fibre convention. Read its abbreviation
   in ResidueField/Fiber.lean: κ(p)⊗[S]T, with the left-factor κ(p)-algebra
   structure. Tensor commutation gives the node's tensor order and transports
   this structure to the right-factor structure; no different fibre is used.
10. If p misses W, the fibre is κ(p) as a κ(p)-algebra:
    `(∀ w : W, (w : S) ∉ p) →
    Nonempty (p.Fiber T ≃ₐ[p.ResidueField] p.ResidueField)`.
    Verdict: exact. This is existence of an algebra equivalence, not merely
    equality of cardinalities or an unstructured ring equivalence.
11. Otherwise the fibre is zero:
    `(∃ w : W, (w : S) ∈ p) → Subsingleton (p.Fiber T)`.
    Verdict: exact. In an inhabited ring subsingleton is precisely the zero
    ring condition. The two implications exhaust the alternatives, with
    the same quantifier order and neither an added nor a missing case.

Source reading: the local literature directory has no Stacks checkout.
I read the actual .tex from the Stacks project's official GitHub repository:
[more-algebra.tex](https://github.com/stacks/stacks-project/blob/master/more-algebra.tex),
labels `lemma-check-G-ring-maximal-ideals` (07PT) and `section-regular` /
`definition-regular` (07BZ), and
[algebra.tex](https://github.com/stacks/stacks-project/blob/master/algebra.tex),
label `definition-localization` (00CO). I also opened the official tag pages
[07PT](https://stacks.math.columbia.edu/tag/07PT),
[07BZ](https://stacks.math.columbia.edu/tag/07BZ), and
[00CO](https://stacks.math.columbia.edu/tag/00CO).
The enclosing 07PT lemma assumes R Noetherian for its G-ring criterion;
its localization assertion is the general localization fact isolated by
this node. The regular-map definition 07BZ imposes Noetherianity on the
fibres, not on the original or target ring. The section introduction's
field and Noetherian algebra assumptions concern geometric regularity,
exactly as the imported definition expresses them; they are not extra
hypotheses on S and T.

Edge cases: W={1} gives an isomorphic copy of S with every fibre κ(p).
If 0∈W, T and every fibre are zero and every prime meets W. If S is zero,
there are no prime ideals, so both universal fibre clauses are vacuous;
regularity still includes flatness. Zero divisors in S and arbitrary
characteristics are allowed. The prime set may be empty. A multiplicative
subset cannot be empty because it contains 1; the node has no unrelated
index set, scheme, or integer n, so empty schemes and n=0 introduce no
additional cases. Universes u and v are explicitly independent, and the
imported geometric-regularity definition quantifies over extension fields
in `Type (max u v)`, not a possibly vacuous smaller universe.

Independent searches (different wording from the first worker), all logged
by `/home/ubuntu/weil-launcher/msearch.py` in `searches.jsonl`:

- LeanSearch: `Inverting a multiplicative set gives a flat homomorphism with
  geometrically regular fibers`. Service returned Internal Server Error;
  recorded unavailable, with no negative mathematical verdict.
- LeanFinder: `Tensoring a localization with the residue field of a prime
  yields that field or the trivial ring`. Eight results; the nearest were
  `Ideal.ResidueField.exists_smul_eq_tmul_one`,
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`, and
  `Ideal.Fiber.exists_smul_eq_one_tmul`. Their signatures give fraction
  presentations or nontriviality for general fibres, not this statement.
- Loogle: `IsLocalization, "fiber"`. Zero hits.
- Mathlib grep for `Fiber.*(Subsingleton|IsLocalization)|
  (isRegular|IsRegular).*localization|localization.*(isRegular|IsRegular)|
  atUnits|subsingleton_iff` under RingTheory. Relevant ingredients are
  `IsLocalization.atUnits` and `IsLocalization.subsingleton_iff`; I opened
  both declarations in Localization/Basic.lean and Localization/Defs.lean.
  They only give the units and zero localization cases, not the full theorem.
- Direct `rg` across source `WeilConjectures`, project `lean/Sheaf`, Mathlib
  Localization, and `dag/lean_names_upstream.json` for `isRegular_and_fiber`,
  `geometricallyregular`, and regular/localization/map/hom variants. No
  existing statement matches. Source regular-local-ring localization and
  Mathlib regular-element lemmas are different notions. Project GRing
  criterion and pairs-of-primes docstrings cite this fact but do not state it.

No new definition nodes or dependency modules are present or needed; H12
and H13 therefore require no additional deliveries. Both recorded dependency
notions are usable and directly imported, with no private copies. No
`statement_change` is present and none is needed. The sole theorem has a
`sorry` proof, with no definitions or new axioms. Its docstring names the
source and blueprint and follows all six DAG proof steps: flatness, fibre
localization, residue-map kernel, units/zero split, geometric regularity,
and regularity. The one import supplies the used regular-map definition.
The signature in the node was checked verbatim against the module;
all variables and universes are bound and every Lean line is at most
100 characters. No statement or code repair was needed.

Validation: the second reader ran `scompile.py G1
lem-weil-pbc-localization-regular` on the absolute module path; the server
compiled it in 1.6 seconds with exit code 0 and no warnings. The subsequent
`deliver2.py G1 lem-weil-pbc-localization-regular --no-push` printed
`OK (dry run)`: preflight and compilation passed, with nothing pushed.
