## Worker report

The module `Sheaf.RingTheory.ExistsLiftOfFieldCharP` states
`RingHom.exists_lift_of_field_charP`, with its only proof left as `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

The node's hypotheses and conclusion are rendered as follows:

- A field K: `(K : Type u) [Field K]`.
- Characteristic p > 0: `(p : ℕ) [CharP K p] (hp : 0 < p)`.
  Primality follows from positive characteristic of a field; it is not an extra hypothesis.
- A commutative ring D: `(D : Type v) [CommRing D]`.
- The condition p times its identity is zero: `(hD : (p : D) = 0)`.
  The natural-number cast is exactly p times the identity. This does not impose
  nontriviality or exact characteristic on D.
- An ideal J in D: `(J : Ideal D)`.
- An integer N ≥ 1 and J^N = 0: `(N : ℕ) (hN : 1 ≤ N) (hJ : J ^ N = ⊥)`.
  Positive integers are represented without loss by positive naturals; `⊥` is the zero ideal.
- The quotient map π: `Ideal.Quotient.mk J`. This is the canonical map from D to D/J,
  so no arbitrary map or extra hypothesis is introduced.
- A ring homomorphism g: `(g : K →+* D ⧸ J)`.
- Existence of a ring homomorphism f with π composed with f equal to g:
  `∃ f : K →+* D, (Ideal.Quotient.mk J).comp f = g`.

The item has empty `stmt_deps`; there are no dependency declarations to import.
The statement uses Mathlib's `CharP` from `Mathlib.Algebra.CharP.Defs`, `Field` from
`Mathlib.Algebra.Field.Defs`, ideal powers from `Mathlib.RingTheory.Ideal.Operations`,
and the quotient ring and `Ideal.Quotient.mk` from `Mathlib.RingTheory.Ideal.Quotient.Defs`.
The full definitions of `CharP` and the quotient map were read locally.
The docstring carries all three proof steps and names the three proof-dependency nodes.

Edge cases checked: N = 1 forces J = 0, so the quotient is canonically D; J = 0 is
allowed for every positive N. N = 0 and p = 0 are exactly the excluded cases in the node.
The field K need not be perfect, algebraic, finite, or essentially of finite type over F_p.
The zero ring D is allowed: it and its quotient have the unique unital ring map from K.
For nonzero D, J = ⊤ cannot satisfy J^N = 0. Independent universes u and v allow fields
and target rings of any sizes. No formal-smoothness or algebra-structure hypothesis is added.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder: “A ring homomorphism from a field of positive characteristic lifts along
  a nilpotent ideal of a ring of the same characteristic”. Eight hits on `PerfectRing.lift`
  and its variants; these concern p-radical maps and perfect target rings, not this statement.
- Loogle: `Algebra.FormallySmooth, PerfectField`. One hit:
  `Algebra.FormallySmooth.of_perfectField`, requiring `Algebra.EssFiniteType K L`.
  Its full signature was read in `Mathlib/RingTheory/Smooth/Field.lean`.
- LeanSearch: “field of characteristic p ring homomorphism lifts nilpotent ideal”.
  Service unavailable (Internal Server Error); recorded as unavailable.
- Mathlib grep: `FormallySmooth|exists_lift` in `RingTheory/Smooth` returned related smoothness
  declarations. Direct reading of `Smooth/Basic.lean` shows `Algebra.FormallySmooth.exists_lift`
  requires a formally smooth algebra and an algebra homomorphism, so is not the exact statement.
- `rg` for `nilpotent.*lift|lift.*nilpotent|FormallySmooth|charP.*lift` in the source's
  `WeilConjectures` and this project's `lean/Sheaf` found related formal smoothness declarations
  and the citer `CohenRingModPowFormallySmooth.lean`, but no declaration stating this result.
- `rg` for the exact node id in `WeilConjectures` returned no match.
- `rg` for `exists_lift_of_charP|exists_ringHom_lift_of_charP` in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no matches; the chosen more specific
  name `RingHom.exists_lift_of_field_charP` is also subject to the delivery collision check.

The local literature checkout is absent. Read the sources at
[Stacks 0320](https://stacks.math.columbia.edu/tag/0320), part (3), for formal smoothness
of separable field extensions, and
[Stacks 07K4](https://stacks.math.columbia.edu/tag/07K4) for successive lifting through ideal
powers. These agree with the node's proof route. No statement fault or dispute found.

## Second reading by C1

Read the node copy and `ExistsLiftOfFieldCharP.lean` together, independently of the
worker's report. The complete object/hypothesis/conclusion checklist is:

| Node item | Lean rendering | Verdict |
|---|---|---|
| A field K | `(K : Type u) [Field K]` | Exact; Mathlib's Field is a nontrivial commutative field. |
| Its positive characteristic p | `(p : ℕ) [CharP K p] (hp : 0 < p)` | Exact; CharP states that a natural-number cast vanishes iff p divides it. Primality is a consequence, not an extra binder. |
| A commutative ring D | `(D : Type v) [CommRing D]` | Exact; no Nontrivial, field, local, Artinian, or Noetherian instance on D. |
| p times the identity of D is zero | `(hD : (p : D) = 0)` | Exact natural-number cast; deliberately does not require CharP D p. |
| An ideal J of D | `(J : Ideal D)` | Exact existing Mathlib ideal, not a private predicate. |
| An integer N at least one | `(N : ℕ) (hN : 1 ≤ N)` | Exact: every integer at least one corresponds to a positive natural. Any such witness can be passed before g; no least exponent is assumed. |
| J to the Nth power is zero | `(hJ : J ^ N = ⊥)` | Exact ideal power and zero ideal. The multiplication is span of products and the power is repeated ideal multiplication. |
| The quotient D/J | `D ⧸ J` | Exact canonical Mathlib quotient ring, with its induced commutative ring instance. |
| The quotient map π | `Ideal.Quotient.mk J` | Exact: its underlying function is the quotient-class map; π is determined, not another arbitrary morphism. |
| A ring homomorphism g from K into D/J | `(g : K →+* D ⧸ J)` | Exact unital ring homomorphism, with no injectivity, surjectivity, or additional algebra-linearity assumed. |
| Existence of a ring homomorphism f from K into D | `∃ f : K →+* D, ...` | Exact existence after all the data and g; no uniqueness or chosen functorial lift is asserted. |
| π composed with f equals g | `(Ideal.Quotient.mk J).comp f = g` | Exact equality of bundled ring homomorphisms; comp evaluates as π(f(x)). |

Source reading: the local repository has no Stacks .tex checkout. Retrieved the upstream
[algebra.tex](https://github.com/stacks/stacks-project/blob/master/algebra.tex) and
[smoothing.tex](https://github.com/stacks/stacks-project/blob/master/smoothing.tex)
into this item's scratchpad, and read the actual labelled passages, not just the tag titles.
The algebra conventions explicitly allow the zero ring and require commutative rings with 1.
Read `lemma-formally-smooth-extensions-easy` (0320), including part (3) and its filtered-colimit
proof; `definition-formally-smooth` (00TI); `definition-perfect` and `lemma-perfect`
(030Y/030Z); and the successive lifting paragraph of `lemma-smooth-strong-lift` (07K4).
The base here is F_p: it is perfect, so every extension K/F_p is separable. No finiteness
condition on K is inherited. The Noetherian construction in 07K4 obtains a nilpotent exponent
in that lemma; this node already assumes J^N = 0 and uses only its successive lifting argument.
Read smoothing.tex's `lemma-helper` (07FG), especially the lifts of σ' and τ': the source
explicitly says the section need not be a k-algebra map, agreeing with the RingHom conclusion.
Also checked the tag pages [0320](https://stacks.math.columbia.edu/tag/0320),
[07K4](https://stacks.math.columbia.edu/tag/07K4), and
[07FG](https://stacks.math.columbia.edu/tag/07FG).

Dependency audit: `stmt_deps` is empty. All statement notions are supplied directly by
Mathlib. Opened Field/Defs.lean (Field extends CommRing and DivisionRing), CharP/Defs.lean
(CharP.cast_eq_zero_iff), Ideal/Quotient/Defs.lean (quotient instances and mk),
Algebra/Ring/Hom/Defs.lean (RingHom and comp), Ideal/Operations.lean, and
Algebra/Algebra/Operations.lean (ideal/submodule multiplication and powers).
There are no new definition nodes, dependency modules, or statement_change to audit.

Edge cases: p = 0 is excluded exactly as in the node. Composite positive p and p = 1
cannot be a field characteristic, without adding a separate primality hypothesis.
N = 0 is excluded exactly as in the node. N = 1 means J = 0 and is included; J = 0
is included for every positive N. D may be the zero ring, whose quotient and maps into it
are also allowed. J = ⊤ can be nilpotent only when D is the zero ring; that case remains
included. Arbitrary imperfect K and arbitrarily large transcendence degree are allowed.
Independent explicit universes u and v impose no common-size restriction; all variables
and universes are bound. No index set, scheme, or separate zero object occurs here.

Independent searches (different wording from the worker):

- LeanFinder through msearch.py: “Fields in positive characteristic are projective with
  respect to surjective ring maps with nilpotent kernel”. Eight hits, including
  `Algebra.FormallySmooth.of_perfectField`, Frobenius/perfect-ring declarations, and an
  unrelated projectivity result; none states this arbitrary-field lifting theorem.
- Loogle through msearch.py: `CharP, Ideal.IsNilpotent, RingHom` was rejected because
  Ideal.IsNilpotent is not an indexed identifier. Repeated with `Algebra.FormallySmooth, Field`:
  five hits, including `of_perfectField`, purely transcendental and separably generated
  smoothness, and a local cotangent criterion. Opened the entire Smooth/Field.lean:
  of_perfectField requires EssFiniteType; the other results require an independent
  generating family or a separably generated presentation, which is not given here.
- LeanSearch through msearch.py: “Every homomorphism from a positive characteristic field
  to a quotient by a nilpotent ideal admits a lift”. Unavailable: Internal Server Error;
  no mathematical verdict inferred from that failed service.
- rg on Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `lift_of_field`, `nilpotent_lifting`, `field_char_p_nilpotent`, and the full proposed
  declaration name found no existing statement/name collision. Broader searches for
  formal smoothness, lifting, and nilpotence found related project modules, including
  CohenRingModPowFormallySmooth, and an Artinian root-lifting argument. Read
  Smooth/Basic.lean's class FormallySmooth, comp_surjective, and exists_lift:
  exists_lift needs FormallySmooth and uses AlgHom; it is the induction component,
  not this theorem without extra assumptions.

H5/H6/H8/H9: one theorem, its proof only `sorry`, no definitions or hidden data holes.
Both docstrings give source places and the exact blueprint id. The theorem docstring
carries each of the node's three proof steps: unique F_p-algebra structures and automatic
linearity; cotangent H1 vanishing plus projective differentials and square-zero lifting,
with all three dependency ids; and successive lifting through ideal powers with the
square-zero inequality and final identification at J^N = 0. All imports serve statement
notions. Header, namespace RingHom, topic, and line lengths follow the conventions.
The node's lean.statement is verbatim the signature up to `:=`.

No mathematical, signature, dependency, or documentation mismatch found. Kept the correct
Lean module and node record unchanged; added only this independent second-reading report.
Server compilation with scompile.py on the absolute sandbox module path succeeded,
exit code 0, in 1.1 seconds, with no errors or warnings.
Delivery dry run: deliver2.py --no-push printed OK; preflight and server compilation passed.
