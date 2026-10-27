## Worker report

The module `Sheaf.RingTheory.SplitSquareZeroDividedPowers` states
`DividedPowers.SplitSquareZero.exists_unique`, with one postponed proof and no
postponed definition data. It constructs two named definitions registered as local instance adapters for the
canonical right action; it does not introduce a second divided-power notion.
The original node is unchanged except for `lean`. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED issue is needed.

Source read: `literature/stacks-project/dpa.tex`, definition-divided-powers
(Tag 07GL), and example-adjoining-odd (Tag 09PH), especially its displayed
first-order formula. The node supplies the expanded ordinary split-extension
argument for arbitrary C-modules. Its seven proof steps are reproduced in the
theorem docstring, including the scalar calculation with a general (c,v), the
addition index shifts, Pascal identity, integer iteration coefficient identity,
and uniqueness using the addition formula.

Hypotheses and clauses, matched individually:

| Node | Lean rendering |
| --- | --- |
| Commutative ring C | `(C : Type u) [CommRing C]` |
| Ideal I in C | `(I : Ideal C)` |
| Given ordinary divided powers gamma | `(γ : DividedPowers I)` |
| Arbitrary C-module M | `(M : Type v) [AddCommGroup M] [Module C M]`; u and v independent |
| Ring B = C direct-sum M, multiplication (cd,cv+du) and unit (1,0) | Mathlib `TrivSqZeroExt C M`; its multiplication and unit instances, with the canonical symmetric right action constructed by `rightModule` and `centralScalar` |
| Ideal K = I direct-sum M | `I.comap (TrivSqZeroExt.fstHom C C M).toRingHom`; membership reduces to the first coordinate being in I |
| Existence of an ordinary structure delta on K | `∃ δ : DividedPowers (I.comap ...), ...` |
| delta_n(x,0) = (gamma_n(x),0), x in I | First conjunct: `∀ (n : ℕ) (x : C), x ∈ I → δ.dpow n (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl (γ.dpow n x)` |
| delta_n(0,u) = 0 for n > 1 | Second conjunct quantifies n and u, assumes `1 < n`, and evaluates `δ.dpow n (TrivSqZeroExt.inr u)` |
| Formula for n >= 1, x in I, u in M | Third conjunct assumes `0 < n` and `x ∈ I`; its RHS is `TrivSqZeroExt.inl (γ.dpow n x) + TrivSqZeroExt.inr (γ.dpow (n - 1) x • u)` |
| Uniqueness subject to the two restrictions | Final clause quantifies every `η : DividedPowers (I.comap ...)`, assumes the first two restriction properties only, and concludes `η = δ` |
| Ordinary degree zero equals 1 | `DividedPowers.dpow_zero` on the ideal; the restriction to (x,0) includes n=0, where both sides are the standard unit |
| All positive operations map K to K | `DividedPowers.dpow_mem` |
| Degree one is the identity | `DividedPowers.dpow_one` |
| Homogeneity for every scalar in B | `DividedPowers.dpow_mul`; its scalar belongs to the whole split ring |
| Addition formula | `DividedPowers.dpow_add`, whose antidiagonal sum is the displayed sum indexed from 0 to n |
| Product formula with binomial coefficient | `DividedPowers.mul_dpow` uses `Nat.choose` |
| Iteration formula with integer factorial quotient | `DividedPowers.dpow_comp` uses `Nat.uniformBell`, the integer (nm)!/(n!(m!)^n) |

The total-map convention in the dependency is used verbatim: the operations
are extended by zero off the ideal (`dpow_null`), not newly specified there.
The all-degrees first restriction differs from its positive-degree reading
only by the already required degree-zero identity. Likewise Mathlib's
zero-index axiom cases follow tautologically from gamma_0=1.

Dependency declarations read and used:

- `def-sfb-ordinary-divided-power-structure` is a Mathlib leaf, with no lean
  record required. Its match is `DividedPowers` in
  `Mathlib.RingTheory.DividedPowers.Basic`, lines 78--92. The file documentation
  and full structure signature were read. This is the ordinary structure in
  both hypothesis and conclusion, with exactly the five listed axioms.
- `Mathlib.Algebra.TrivSqZeroExt.Basic`: `TrivSqZeroExt`, `inl`, `inr`,
  `fstHom`, and its ring instances. The full projection signature and
  multiplication definitions were read. `fstHom C C M` is the canonical
  C-algebra projection; its underlying ring map gives the comap ideal.
- `Ideal.comap` from Mathlib's ideal API, reexported by the divided-power
  dependency. No separate ideal notion or split-ring notion is defined.
- `Module.compHom` and `RingHom.fromOpposite` construct the right action from
  the existing left module structure. The scalar equality is definitional,
  giving the real-data instance `centralScalar`.

Edge cases checked before writing:

- n=0: not covered by the positive formula; delta_0 is (1,0), including at
  zero. The first restriction holds also at n=0. No positive-degree map is
  incorrectly forced to be zero in degree zero.
- n=1: gamma_0(x)=1 makes the formula (x,u). The pure-module vanishing clause
  begins strictly above degree one.
- x=0, n>1: gamma_n(0)=gamma_(n-1)(0)=0, giving the pure-module restriction.
- M=0: recovers the original ideal and its prescribed structure.
- I=0: recovers the standard square-zero ideal with higher powers zero.
- I=top: no special case is silently excluded; the theorem remains conditional
  on the existence of its given divided powers.
- Zero ring, zero module, torsion modules, and positive characteristic are
  allowed. No nontriviality, flatness, torsion-free, Q-algebra, or factorial
  invertibility hypothesis is present. Integer coefficient identities require
  no cancellation in C or M.
- The uniqueness clause does not assume the formula for the competitor; it
  applies under precisely the two restrictions in the node.

Searches made with `msearch.py Q12 lem-sfb-split-square-zero-divided-powers`:

- LeanFinder query: `Divided powers on I direct sum M in a trivial square zero
  extension with formula gamma n x and gamma n minus one x times u`. Eight
  hits, including `DividedPowers.OfSquareZero.dividedPowers`, rational-algebra
  and quotient constructions. None states the arbitrary-I extension.
- Loogle query: `"DividedPowers", "TrivSqZeroExt"`. Zero hits.
- Mathlib grep query: `TrivSqZeroExt|square.zero|OfSquareZero`, subdirectory
  `RingTheory/DividedPowers`. Three hits, all in `RatAlgebra.lean`.
- LeanSearch query: `Divided powers on the split square zero extension of a
  divided power ideal by a module`. Eight hits; square-zero, rational,
  subideal, quotient, and abstract divided-power constructions, not this
  extension theorem.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for
  `split.*[Dd]ivided|[Dd]ivided.*split` and for the exact node id: no existing
  statement. The only relevant hit is the proof documentation in
  `Sheaf.RingTheory.DividedPowerVariableAdjunction`, referring to this lemma.
  Searches for `TrivSqZeroExt` also find existing uses of the standard ring.

The closest Mathlib result was read in full: `OfSquareZero.dividedPowers`
in `Mathlib.RingTheory.DividedPowers.RatAlgebra`, lines 194--207, assumes
I^2=0 for the entire ideal. Here I can be arbitrary, and only M is square zero,
so it is not a match. The canonical split-ring and ideal operations already
exist and are reused, requiring no new node.

Validation: prescribed `scompile.py Q12 lem-sfb-split-square-zero-divided-powers`
compiled the single delivered file both as sandbox and library module; exit 0,
no errors or unexpected warnings. No other compilation command was used.

## Second reading by Q12

A second in-session reading reopened the node and the completed file; no other
agent was started, as the dispatch brief forbids it. The reading checked the
ring, ideal, and module binders, both prescribed restrictions, the explicit
positive-degree formula, and the last uniqueness clause separately. In
particular, the competitor eta is assumed to satisfy only the two restrictions,
not the formula, so uniqueness is not weakened to uniqueness under a prescribed
formula. Both divided-power structures use the same canonical comap ideal.
The degree-zero convention and integer coefficient interpretation agree with
the recorded ordinary-divided-power dependency. The local right action is
constructed from the given action and adds no bimodule hypothesis. No mismatch
was found and no statement change was made. Every variable and universe is
explicitly bound, `autoImplicit` is false, all source lines meet the 100-character
limit, the only theorem proof is `sorry`, and neither local instance contains
postponed data or a proof chosen from an existence theorem.

Preflight repair: its declaration inventory did not recognize named `local instance`
commands. Both canonical action adapters are now named `abbrev` declarations with
`attribute [local instance]`; their data, local scope of instance search, and
the theorem signature are unchanged. The second reading also checked these
revised definition headers against the recorded declaration names.

The adapters are reducible abbreviations, avoiding class-definition reducibility
and proposition-definition lint warnings without suppressing any linter.
