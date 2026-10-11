## Worker report

The module `lean/Sheaf/RingTheory/N2CharPPurelyInseparableCriterion.lean` states
`isN2_of_finite_purelyInseparable_integralClosure`. It uses the existing
`Sheaf.RingTheory.JapaneseDomain.IsN2` definition and Mathlib's
`integralClosure`, `Module.Finite`, `IsPurelyInseparable`, `FiniteDimensional`, and
`CharP`.

The theorem renders the statement as follows. `R : Type u` and `K : Type v` are
commutative-domain and field objects (`[CommRing R] [IsDomain R] [Field K]`), with
`[Algebra R K] [IsFractionRing R K]` giving K as the fraction field of R. The
Noetherian hypothesis is `[IsNoetherianRing R]`. Positive characteristic is an
explicit natural number `p`, a proof `hp : 0 < p`, and the instance `[CharP K p]`.
The hypothesis `h` quantifies every `L : Type v` with field/algebra structures,
`[Algebra K L] [Algebra R L] [IsScalarTower R K L]`; finite extension is
`[FiniteDimensional K L]`, and purely inseparable extension is
`[IsPurelyInseparable K L]`. Its conclusion for each such L is
`Module.Finite R (integralClosure R L)`, i.e. the integral closure of R in L is a
finitely generated R-module. The result is `IsN2 R K`, exactly the Japanese-domain
predicate, whose definition quantifies finite field extensions and asks for the
same finite integral closure.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing` (mathlib leaf).
- `Mathlib.FieldTheory.PurelyInseparable.Basic.IsPurelyInseparable` and
  `Module.Finite` (the finite purely inseparable dependency).
- `Mathlib.Algebra.Algebra.Defs.Algebra` (the field-extension convention).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic.integralClosure` and
  `IsIntegral` (integral closure dependency).
- `Mathlib.RingTheory.Finiteness.Defs.Module.Finite` (finite generation).
- `Sheaf.RingTheory.JapaneseDomain.IsN2` from
  `lean/Sheaf/RingTheory/JapaneseDomain.lean` (Japanese/N-2 definition).

Edge cases checked: `hp : 0 < p` excludes characteristic zero; the field
characteristic instance is attached to K (the fraction field), and `L` is allowed
to equal K, so the hypothesis includes the trivial purely inseparable extension.
Finite extensions are represented by `FiniteDimensional K L`; no additional
separability or algebraicity hypothesis is added. The universe of L is the same
`Type v` as K, matching the existing `IsN2` definition.

Searches made before writing: `msearch.py E1 ... leanfinder` for finite purely
inseparable Japanese/N-2 criteria (no matching theorem); `msearch.py ... loogle`
for `IsPurelyInseparable, Module.Finite, integralClosure` (no combined result);
`msearch.py ... grep` for Japanese/N-2 and purely inseparable integral-closure
predicates (no project or Mathlib definition); `rg -n` over
`WeilConjectures/` and `lean/Sheaf` for the theorem/predicate (only the existing
`JapaneseDomain.IsN2` definition). The node's recorded Mathlib searches likewise
report no criterion theorem.

The source is Stacks Project `literature/stacks-project/algebra.tex`, Lemma Tag
032N, direction “if” (line 45382 and proof lines 45389–45407). Its proof is left
as `sorry` for stage 2, as required.

## Earlier second reading (a previous round; superseded)

The source statement and the Lean signature agree clause by clause: the base is a
Noetherian integral domain with fraction field K of positive characteristic p;
`h` covers exactly finite purely inseparable field extensions and gives finite
integral closure; the conclusion is the existing N-2 predicate. No statement
correction or disputed clause was found.

## Second reading by E1

I independently opened the node, its six statement dependency nodes, the complete
JapaneseDomain module, and the Mathlib declarations below. I read Stacks
algebra.tex lines 45380–45410 and verified tags 032N and 032F on the server
(the local repository omits the literature checkout). Tag 032N assumes exactly a
Noetherian domain with fraction field of positive characteristic; no ambient
normality, perfection, or finite-type condition is assumed. The node correctly
selects the “if” direction. There is no statement_change and no new node or
dependency module in this delivery.

Objects, hypotheses, and conclusion, listed before the comparison:

1. A commutative integral domain R: `(R : Type u) [CommRing R] [IsDomain R]`.
   Verdict: exact; nontriviality is part of being a domain.
2. R is Noetherian: `[IsNoetherianRing R]`. I read
   Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing: it is `IsNoetherian R R`,
   meaning every ideal is finitely generated. Verdict: exact.
3. Its fraction field K: `(K : Type v) [Field K] [Algebra R K]
   [IsFractionRing R K]`. Mathlib's fraction-ring predicate is localization at
   non-zero-divisors. For a domain this is precisely its fraction field.
   Verdict: exact, with no chosen special field.
4. K has characteristic p > 0: `(p : ℕ) (hp : 0 < p) [CharP K p]`.
   Verdict: exact; primality follows from positive characteristic of a field,
   so an extra prime instance is unnecessary.
5. Every field extension L/K: `∀ (L : Type v) [Field L] [Algebra K L]` in h.
   I read Mathlib.Algebra.Algebra.Defs.Algebra; its algebraMap is the given
   unital ring homomorphism, injective between fields. Verdict: exact.
6. Finite and purely inseparable: `[FiniteDimensional K L]
   [IsPurelyInseparable K L]`. I read the latter class and
   `isPurelyInseparable_iff_pow_mem` in PurelyInseparable.Basic, identifying it
   with `∀ x, ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap K L).range` in this positive
   characteristic. FiniteDimensional is literally `Module.Finite K L`.
   Verdict: exact, including n = 0; no separability or perfection added.
7. Integral closure uses the composite R → K → L:
   `[Algebra R L] [IsScalarTower R K L]`, followed by `integralClosure R L`.
   Scalar-tower compatibility forces the algebraMap to be the composite;
   these structures can always be supplied for any L/K. I read the subalgebra
   definition with carrier `{x | IsIntegral R x}`. Verdict: exact, not an
   independently chosen R-action or private closure definition.
8. The hypothesis says each such closure is finitely generated over R:
   `Module.Finite R (integralClosure R L)` in h. I read Finiteness.Defs:
   `Module.Finite` asserts that the whole module is finitely generated.
   Verdict: exact; finite means module finite, not finite cardinality.
9. Conclusion: `IsN2 R K`. I read its complete signature and body in
   Sheaf.RingTheory.JapaneseDomain. It quantifies all finite field extensions,
   with the same composite scalar tower, and asks for the same finite integral
   closure, without assuming purely inseparable. Verdict: every conclusion
   clause and quantifier is present, with no added integrally closed condition.

Edge cases: zero rings and empty carriers cannot be domains or fields, so the
node does not cover them. Empty index sets and empty schemes do not occur.
The trivial extension L = K is included and h therefore includes N-1.
A field extension cannot have vector-space dimension zero. The exponent n = 0
is included by Mathlib's natural-number quantifier. Characteristic zero is
excluded exactly by hp; p = 1 is impossible for a field, and composite positive
p is likewise impossible, as in the source. Universes u and v are both bound,
and no inequality between the ring and fraction-field universes is imposed.
The extension universe is v, matching the existing IsN2 definition: this is
nonvacuous (K itself qualifies). Every finite-dimensional extension of K has
cardinality at most max(ℵ₀, |K|) and a representative in K's universe (a finite
coordinate space over K with transported field structure). Thus the universe
choice retains all finite extensions up to K-algebra isomorphism, including
finite base fields, and does not restrict the mathematical criterion.

Independent searches (with vocabulary different from the first worker):

- `msearch.py ... leanfinder "A noetherian domain is Japanese if normalization
  in all finite radicial fraction field extensions is module finite"` returned
  eight hits, principally IsIntegralClosure.finite/isNoetherian and Dedekind
  results. I opened IsIntegralClosure.finite: it assumes the base is integrally
  closed and the extension separable, so it is not this criterion.
- `msearch.py ... loogle "IsPurelyInseparable, integralClosure"`: zero hits.
- `msearch.py ... grep
  "radicial|IsN2|IsJapanese|purelyInseparable.*integralClosure"`: zero hits.
- Direct rg in Mathlib, WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for IsN2, Japanese, and both orders of the
  purely-inseparable/integral-closure words found no criterion. The project's
  JapaneseDomain and its localization/Nagata uses are the existing notion,
  already imported. The node also records a LeanSearch absence search; the
  independent Finder, Loogle and grep checks corroborate it.

Mismatches repaired: H8, the theorem docstring omitted the node's natural-language
proof. I added all six steps and their named dependencies: normal-extension
reduction; purely-inseparable intermediate field; normality, fraction field and
Noetherianity of its closure; separable-extension finiteness and finite-module
transitivity; equality of the two integral closures; the N-2 conclusion. H9,
the conventional copyright/license/author header was missing and is now present.
No statement, signature, dependency record, or mathematical definition changed.
There are no hollow definitions or proved theorems: the only theorem body is
`sorry`. All declaration names/universes are explicitly bound, imports supply
notions used in the signature, and every line is at most 100 characters.

Validation: scompile.py E1 lem-weil-pbc-n2-char-p-purely-inseparable-criterion
compiled the repaired module on the server in 1.4 seconds, exit 0, with no
warnings or errors. The node's lean.statement was checked verbatim against the
file's theorem signature.

## Stage-2 review by R-npi1153 (FIX)

The characteristic hypothesis `(p : ℕ) (hp : 0 < p) [CharP K p]` is replaced by
`(p : ℕ) [Fact p.Prime] [CharP K p]`, the convention of STATE line CHARACTERISTIC p
(C1 fe000df38), which names `(hp : 0 < p)` as not to be used in new statements.
For a field the two are equivalent (positive characteristic of a field is prime), so the
mathematical statement is unchanged; the second reading's item 4 and the worker's
mentions of `hp` above refer to the delivered form. All other clauses were matched
against the node and `IsN2` (J1 def-weil-pbc-japanese-domain) and kept: the hypothesis
`h` is exactly `IsN2`'s quantifier with `[IsPurelyInseparable K L]` added, over the same
universe `v` as `IsN2` (nonvacuous: `L = K` qualifies). Recompiled clean.
