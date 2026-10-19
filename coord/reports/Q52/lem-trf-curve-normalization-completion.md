## Worker report

The module `Sheaf.TraceFormula.CurveNormalizationCompletion` states
`RingTheory.curve_normalization_completion`, with one `sorry` proof and no definitions.
The node copy changes only `lean`. There are no new nodes, dependency repairs, statement
corrections or disputed statements.

I read the node, all six statement dependencies and their recorded Mathlib declarations,
including the `mathlib_match` for essential finite type (that node is a Mathlib leaf and
needs no `lean` record). I read Stacks `varieties.tex`, `lemma-pre-delta-invariant` (0C3S)
and `lemma-normalization-same-after-completion` (0C3V), including the completed-DVR product
argument. The node is the completion specialization for local algebras essentially of
finite type over an arbitrary field. The Lean docstring carries its eleven-step proof
route, including the common denominator calculation.

For readability in this report only, write R = AdicCompletion (IsLocalRing.maximalIdeal A) A,
Q(T) = FractionRing T, and B = integralClosure A (FractionRing A). The Lean signature writes
these expressions in full, without let binders, abbreviations or file-local notation.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| A is a commutative k-algebra | `(A : Type v) [CommRing A] [Algebra k A]` |
| A is local with maximal ideal m | `[IsLocalRing A]`; `IsLocalRing.maximalIdeal A` |
| A is reduced, including the stated nilpotent criterion | `[IsReduced A]`, meaning every nilpotent element is zero |
| A is essentially of finite type over k | `[Algebra.EssFiniteType k A]` |
| A has Krull dimension one | `hdim : ringKrullDim A = (1 : WithBot ℕ∞)` |
| Q(A) inverts every non-zero-divisor | `FractionRing A`, defined as `Localization (nonZeroDivisors A)`, with no domain hypothesis |
| B is the integral closure in Q(A) | `integralClosure A (FractionRing A)`, the subalgebra of integral elements |
| R is the maximal-ideal completion with its canonical A-map | `AdicCompletion (IsLocalRing.maximalIdeal A) A` and its standard `algebraMap A R` |
| Tensor product is scalar extension | `R ⊗[A] B`, using the recorded dependency's left scalar extension convention; its canonical tensor flip identifies this with B tensor R in the node |
| B is finite as an A-module | first conjunct `Module.Finite A (integralClosure A (FractionRing A))` |
| R is reduced | second conjunct `IsReduced R` |
| R has dimension one | third conjunct `ringKrullDim R = (1 : WithBot ℕ∞)` |
| Every old denominator remains a valid completed denominator | the existential proof `hreg : ∀ s : A, s ∈ nonZeroDivisors A → algebraMap A R s ∈ nonZeroDivisors R` |
| The canonical comparison identifies the tensor with the new integral closure | `e : (R ⊗[A] B) ≃ₐ[R] integralClosure R (FractionRing R)`, together with the final pure tensor equation |
| The fraction map extends A to its completion and uses the same denominators | `φ : FractionRing A →+* FractionRing R` and the equation for every a and s: `φ (IsLocalization.mk' (FractionRing A) a s) = IsLocalization.mk' (FractionRing R) (algebraMap A R a) ⟨algebraMap A R s, hreg s s.property⟩` |
| Compatibility of normalization comparison with the fraction map | `∀ b : B, (e (1 ⊗ₜ[A] b) : FractionRing R) = φ b.1` |

The fraction formula at denominator 1 says that φ extends A to R and then into Q(R).
An algebra isomorphism over R is already R-linear and preserves the R-algebra structure.
Consequently the final equation fixes its value on every r tensor b as r times φ(b).
After the canonical tensor flip, this is exactly the node's canonical map on b tensor r.
Neither e nor φ is arbitrary: the displayed formulas characterize both uniquely, since
fractions and pure tensors generate their domains. No assertion about normalizations of
quotients or about henselization has been added.

Dependency declarations used (all read in the supplied source checkout):

| Dependency | Module and declarations |
| --- | --- |
| `def-weil-pbc-essentially-finite-type-algebra` | `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`; its docstring and `essFiniteType_iff_exists_subalgebra` identify localizations of finite type algebras |
| `def-weil-pbc-krull-dimension-ring` | `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` |
| `def-weil-pbc-integral-closure` | `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, with carrier `IsIntegral A` |
| `def-weil-pbc-adic-completion` | `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, with the ring and canonical algebra structures from `.Algebra` |
| `def-weil-finitely-generated-module` | `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` |
| `def-weil-module-base-change` | `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`, pure tensors, scalar extension and `LinearMap.baseChange`; the scalar extension itself, rather than a particular map base change, occurs here |

All available proof dependency modules are imported without `public`, including the
Nagata/Japanese definitions and stability theorems, reduced Noetherian total fractions,
Dedekind normalization, DVR localization and completion, finite-extension completion,
completion dimension, flatness, and the reduced-normal total-fraction characterization.
Statement dependency imports use `public import`. No dependency import cycle was found
and none was omitted.

Edge cases checked:

- A may be reduced and reducible; `FractionRing A` is a total quotient ring for any
  commutative ring. There is no `IsDomain A` or field hypothesis on Q(A).
- k may be imperfect and have any characteristic. No separability, perfection or
  algebraic closedness assumption occurs. k and A have independent universes u and v.
- The zero ring and fields cannot satisfy `ringKrullDim A = 1`; the exclusions are
  precisely the node's dimension assumption. There is no extra nontriviality binder.
- The completion uses the full Mathlib inverse system, including n = 0 (the zero
  quotient). That harmless initial term does not change the inverse limit over n >= 1.
- Denominators are non-zero-divisors, not merely nonzero elements; units and denominator
  1 are covered. The witness hreg makes each displayed completed fraction well typed.
- Already normal local curves are included. The theorem then identifies the completed
  normalization with the completed ring's normalization, as expected.
- Finiteness is `Module.Finite`, never finiteness of the underlying set or finite type
  of an algebra. No flatness, Noetherianity or Nagata assumption is added: those are
  consequences used only by the proof route.

Searches for an existing statement:

- `msearch.py` LeanFinder: "Normalization of a reduced one dimensional local algebra
  essentially of finite type over a field commutes with maximal ideal adic completion".
  Eight hits, including Dedekind height-one valuation completions and
  `Algebra.intNorm_eq_of_isLocalization`; none states normalization under local adic
  completion. The former complete fraction fields for valuations, the latter compares
  integral norms after localization.
- `msearch.py` Loogle: `"integralClosure", "AdicCompletion"`: no hits.
- `msearch.py` grep: `normalization.*completion|completion.*normalization|integralClosure.*[Cc]ompletion`:
  no Mathlib hits.
- `msearch.py` LeanSearch: "The normalization of a reduced local ring essentially of
  finite type over a field is finite and its tensor product with the adic completion is
  the integral closure of the completed ring in its total ring of fractions". Eight
  hits: finite-module completion/tensor equivalences, ring structure on adic completion,
  normal closure results and scheme normalization; no match for the statement here.
- Direct `rg` over the supplied upstream `WeilConjectures` sources, project `lean/Sheaf`
  and `dag/lean_names_upstream.json`, by the item id, prospective declaration name and
  normalization/completion patterns: no existing statement. Unrelated coefficient
  completion normalization and coherent completion files do not state this result.
  The new declaration name `RingTheory.curve_normalization_completion` has no collision.

Validation: the final module, with the complete statement/proof import set, compiled
cleanly through the prescribed `scompile.py Q52 lem-trf-curve-normalization-completion`
wrapper, in both sandbox and library module modes. Exactly one `sorry` occurs, in the
named theorem's proof; there are no proof holes in the signature or data definitions.
Every variable and universe is bound explicitly. Every Lean line is at most 100 columns.
The JSON `lean.statement` is extracted verbatim from the theorem's signature.

## Second reading by Q52

Independent maintainer second reading of immutable delivery
`5a128141698d7b68303b3e00666e67eb90e36917`, on 2026-10-18. I did not write
this delivery. The original section was a placeholder; this replacement records the
actual reading. The Worker report above is preserved.

Read the item, all six statement-dependency records, their exact Mathlib declarations,
the entire delivered module and both docstrings. Read Stacks `varieties.tex` lines
8293–8314 (Tag 0C3S) and 8345–8424 (Tag 0C3V) in the read-only group clone.
The node is precisely the finite normalization and completion specialization of these
results for local algebras essentially of finite type over a field. The source's
Nagata assumption follows from the field, polynomial, quotient and localization argument
in the node; it need not be an additional Lean hypothesis.

For this table only, R denotes the maximal-ideal completion and B denotes
`integralClosure A (FractionRing A)`.

| Node object, hypothesis or clause | Exact Lean rendering and verdict |
| --- | --- |
| Arbitrary field k, local commutative k-algebra A | `(k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]`: matches. |
| Reduced A, essentially finite type, dimension one | `[IsReduced A] [Algebra.EssFiniteType k A]` and `hdim : ringKrullDim A = (1 : WithBot ℕ∞)`: matches. |
| Total fraction ring and normalization | `FractionRing A` is `Localization (nonZeroDivisors A)`; B has carrier `IsIntegral A`. No domain assumption is introduced: matches. |
| Completion | `AdicCompletion (IsLocalRing.maximalIdeal A) A` with standard `algebraMap A R` is the compatible sequence ring of A/m^n: matches. |
| Finite normalization | First conjunct `Module.Finite A B` is finite generation as a module: matches. |
| Reduced completion of dimension one | Next conjuncts `IsReduced R` and `ringKrullDim R = (1 : WithBot ℕ∞)`: matches. |
| Canonical comparison is an isomorphism | `e : (R ⊗[A] B) ≃ₐ[R] integralClosure R (FractionRing R)`: matches after the canonical tensor flip. |
| Old denominators remain valid | `hreg` asserts exactly preservation of `nonZeroDivisors` by `algebraMap A R`: matches the denominator convention. |
| Fraction map extends A → R with unchanged denominators | `φ : FractionRing A →+* FractionRing R` and the formula for every `a : A` and `s : nonZeroDivisors A`: matches. Taking s = 1 gives compatibility on A. |
| Isomorphism is the canonical comparison | Final equation `(e (1 ⊗ₜ[A] b) : FractionRing R) = φ b.1` for every b: matches. R-linearity determines the value on every pure tensor. |

The formulas characterize φ and e, so the existential quantifiers do not introduce
arbitrary maps or a hollow construction. All universes and variables are explicitly
bound, with independent u and v. No stronger Noetherian, Nagata, flatness, domain,
perfection, separability or algebraically closed field assumption appears.

Read the proof-dependency statements and the supporting Nagata/Japanese, total-fractions,
Dedekind normalization, completion-of-DVR, finite-extension completion, completion-dimension
and reduced-normal-total-fractions interfaces. The product decomposition has its required
compatibility with the base and normalization algebra maps. The proof docstring follows
the node's eleven steps, including the flat injection proving reducedness and the explicit
common-denominator embedding and total-fraction identification. No missing helper,
statement correction or dependency repair is needed. The delivered theorem has just one
`by sorry` proof and no definitions. Source-place and blueprint docstrings are present.

Edge cases: reducible reduced curves use total quotient rings, rather than fraction
fields. Units and denominator 1 are included. Fields and the zero ring are excluded by
dimension one; `IsLocalRing`'s nontriviality therefore loses no case. Arbitrary
characteristic and imperfect fields are included. The completion includes n = 0, whose
zero quotient imposes no extra constraint. Normal local curves are included.

Independent `rg` searches of Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
used integral-closure/adic-completion and normalization/completion patterns. No existing
statement matching the item was found. Read `TensorProduct.toIntegralClosure` and its
flatness, localization and smooth-base-change results: their ambient tensor ring and
hypotheses differ, so they do not duplicate this theorem. The six existing Mathlib
notions are reused. The node's `lean.statement` was byte-compared with the signature
from `theorem` to `:=`: equal; no Lean line exceeds 100 characters.

The current route-pivot dropped-node list has no intersection with the item's statement
or proof dependencies; no prohibited machinery occurs in this commutative algebra
module. The item-specific repair-note path is absent at `origin/newtargets-dag`.

Compilation was reproduced with:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q52 lem-trf-curve-normalization-completion snapshot/lean/Sheaf/TraceFormula/CurveNormalizationCompletion.lean`

The installed wrapper now uses the server's persistent side overlay, as its source
explicitly documents. After an initial SSH session refusal and automatic retry it
returned exit code 0, reporting `sandbox Sheaf/Stage2/Sandbox0.lean [8.3 s]` and
`library Sheaf/TraceFormula/CurveNormalizationCompletion.lean [141.3 s]`, with no
error or warning output. These are wrapper-reported timings, not a raised per-file
limit. This independently confirms the worker's clean per-file compile claim. No
lake/global build, live Lean write, project clone edit, claim, merge or delivery was run.

Finding H11: the original second-reading section was not a reading. Fixed by replacing
that section with this independent clause-by-clause audit. The node and Lean module
require no changes. The complete fixed delivery is acceptable at statement stage;
this does not certify the postponed theorem proof.
