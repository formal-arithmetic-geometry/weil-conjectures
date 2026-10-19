## Worker report

The module `lean/Sheaf/FieldTheory/FiniteFieldAbsoluteGalois.lean` states the complete
finite-field absolute-Galois assertion.  It binds fields `K` and `Ks`, a finite-field
instance on `K`, the algebra structure `K → Ks`, and `IsSepClosure K Ks` (the recorded
separable-closure dependency).  The cardinality `Fintype.card K` is the node's `q`.

The first conjunction renders arithmetic Frobenius: it supplies `φ : Gal(Ks / K)` and
requires `φ x = x ^ Fintype.card K` for every `x : Ks`.  For each `n ≥ 1`, the `∃!`
subextension is an `IntermediateField K Ks`; `Module.finrank K Kn = n` renders degree
`n`, and the `Polynomial.eval₂` biconditional says exactly that its elements are the
roots of `X^(q^n) - X` in `Ks`.  `IsGalois K Kn` gives the Galois clause.  The witness
`φn : Kn ≃ₐ[K] Kn` is Frobenius on `Kn`; `orderOf φn = n` gives the cyclic order, and
every `K`-automorphism is a power `φn ^ j.val` for `j : ZMod n`, giving generation.

The final existential supplies a `ContinuousMulEquiv` from `Gal(Ks / K)` to
`ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))`, the
profinite completion of the infinite cyclic group (the multiplicative presentation of
`ℤ`).  The equation with `ProfiniteGrp.ProfiniteCompletion.etaFn ... 1` renders that
arithmetic Frobenius corresponds to `1` in the profinite completion.

Dependencies used are `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`, declaration
`IsSepClosure.exists_intermediateField_mem`; Mathlib's `Algebra`, `Module.finrank`,
`Polynomial.eval₂`, `IntermediateField`, `Gal`, `IsGalois`, `ZMod`,
`ProfiniteGrp.ProfiniteCompletion.completion`, and `etaFn`.  The dependency nodes
`def-weil-finite-field-q-elements`, `def-pc-field-extension`,
`def-weil-vector-space-dimension`, and `def-weil-polynomial-root` are Mathlib leaves,
so no project module is imported for them.

Edge cases checked: `n = 1` is allowed (`1 ≤ n`), with `ZMod 1` and the trivial cyclic
group; `q` is the actual finite cardinality and hence includes every finite field,
including the prime field; the polynomial is evaluated through the given algebra map;
and the formulation permits arbitrary universe `u` for `K` and `Ks`.

Searches made: the retained node's stage-1 LeanSearch, LeanFinder, Loogle, and grep
searches found only component finite-field/Galois declarations, not this complete
statement.  I reran `msearch.py` LeanFinder with “absolute Galois group of a finite
field is the profinite completion of the integers, Frobenius corresponds to one,
unique degree n subfield roots of X^(q^n)-X”; it returned `FiniteField.Extension.frob`,
`Field.absoluteGaloisGroup`, `FiniteField.Extension.exists_frob_pow_eq`,
`FiniteField.frobeniusAlgEquivOfAlgebraic`, and related ingredients, with no exact
match.  The Loogle query `InfiniteGalois.profiniteGalGrp,
ProfiniteGrp.ProfiniteCompletion.completion, FiniteField.Extension.frob` returned no
hits.  Grep for `absoluteGaloisGroup|profiniteGalGrp|frobeniusAlgEquivOfAlgebraic`
in Mathlib `FieldTheory` found the component declarations and no complete theorem.
The project search found no existing declaration for this node.


## Second reading by N5

I independently read the node and its blueprint source
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-base-field-cd/sk-lem-base-field-cd-galois-group.md`,
the six proof steps, the cited source Stacks `fields.tex`, label
`lemma-infinite-galois-limit` (Tag 0BU2), and the dependency records and declarations.
The blueprint source assumes only a finite field and its separable closure; Stacks
0BU2 assumes a Galois field extension, supplied here by `IsSepClosure.isGalois`.
No statement correction to the natural-language node was needed. The following
list is my object/hypothesis/conclusion checklist against the final signature;
it supersedes the inaccurate generator and universe claims in the Worker report.

- Object K, a finite field with q elements: `(K : Type u) [Field K] [Fintype K]`,
  with `q = Fintype.card K`. Verdict: exact, with no chosen characteristic or extra
  finiteness restriction. The dependency `def-weil-finite-field-q-elements` points
  to Mathlib `GaloisField` and its cardinality/isomorphism facts; no fixed model of
  K is needed here, since the node allows every finite field.
- Object Ks, a separable closure with the K embedding: `(Ks : Type v) [Field Ks]
  [Algebra K Ks] [IsSepClosure K Ks]`. Verdict: exact. I opened `Algebra` and
  `IsSepClosure`: the latter gives separably closed and separable algebraic over K.
  I opened the recorded `IsSepClosure.exists_intermediateField_mem` in
  `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: its independent universes,
  finite-dimensional/separable intermediate fields, and membership are the
  dependency's union assertion. The module is now a public import because the
  dependency belongs to the statement interface.
- Object arithmetic Frobenius: `∃ φ : Gal(Ks / K), ∀ x, φ x = x ^ Fintype.card K`.
  Verdict: exact; `Gal` is the existing K-algebra automorphism group, with Mathlib's
  Krull topology (I read `galBasis`, `galGroupBasis` and its instance).
- Positive index: `∀ n : ℕ, 1 ≤ n → ...`. Verdict: exact; zero is intentionally
  excluded, while one is included.
- Existence of the degree-n subextension: `∃ Kn : IntermediateField K Ks,
  Module.finrank K Kn = n ∧ ...`. Verdict: exact; the existing IntermediateField
  structure records the base-field containment. `Module.finrank` is the recorded
  dimension notion. Since n is positive, finrank n cannot accidentally denote an
  infinite-dimensional field (finrank is zero for infinite dimension).
- Uniqueness among all degree-n subextensions: the separate conjunct
  `∀ E : IntermediateField K Ks, Module.finrank K E = n → E = Kn`.
  Verdict: repaired. Originally `∃! Kn, degree ∧ roots ∧ Galois ∧ ...` only
  syntactically asserted uniqueness among fields with all the extra properties;
  it did not directly render the node's uniqueness among all degree-n fields.
- Description as the roots of T^(q^n)-T: the `∀ x : Ks` membership biconditional
  using `Polynomial.eval₂ (algebraMap K Ks) x (Polynomial.X ^
  (Fintype.card K ^ n) - Polynomial.X) = 0`. Verdict: exact. I opened the recorded
  `Polynomial.eval₂` interface; the polynomial has coefficients in K and is
  evaluated through the given embedding into Ks.
- Galois: `IsGalois K Kn`. Verdict: exact, no hypothesis added.
- Cyclic of order n generated by Frobenius: `∃ φn : Kn ≃ₐ[K] Kn`, its pointwise
  q-power formula, `orderOf φn = n`, and `∀ g, ∃ j : ZMod n, g = φn ^ j.val`.
  Verdict: exact. Exact order plus generation gives group order n, and the formula
  identifies φn with the restriction of φ without assuming an arbitrary map.
- Profinite isomorphism to lim Z/n = Z-hat: `∃ e : Gal(Ks / K) ≃ₜ*
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ)), ...`.
  Verdict: exact standard presentation, not a newly defined substitute. I opened
  `finiteGrpDiagram`, `diagram`, `completion`, and `etaFn`: completion is the
  projective limit of finite quotients. Finite-index subgroups of additive Z are
  nZ for positive n, and the induced quotient maps are reduction for divisibility;
  thus this is exactly the node's lim Z/n, with its product-subspace topology.
  `≃ₜ*` includes continuity of both directions, not only a group isomorphism.
- Frobenius goes to 1: `e φ = ProfiniteGrp.ProfiniteCompletion.etaFn ...
  (Multiplicative.ofAdd (1 : ℤ))`. Verdict: repaired. The original `(1 :
  Multiplicative ℤ)` is multiplicative identity, i.e. additive zero. I checked
  `Multiplicative.ofAdd` and `ofAdd_eq_one` in Mathlib's TypeTags.Basic. The final
  expression is additive one and therefore the tuple `(1 mod n)`.

Edge cases: n=1 gives Kn=K, order-one Frobenius and `ZMod 1`, whose only residue
is zero; this also equals one in that quotient, so the completion normalization
is consistent. n=0 is outside the source. All finite characteristics are allowed,
including characteristic two and the prime field; a field is nontrivial and
nonempty, so q=0, q=1, zero fields, and empty fields are not source cases. There
is no arbitrary empty inverse-limit index: the completion's finite-quotient
index contains the trivial quotient, and the cyclic index contains n=1. Empty
schemes/zero objects do not occur. Universes were repaired from `(K Ks : Type u)`
to `(K : Type u) (Ks : Type v)`; the final compilation accepts independent u,v,
with no equality or smallness hypothesis. Every variable/universe is bound.

Independent searches (not just the first worker's searches):

- `msearch.py ... leanfinder` with “Finite field separable closure automorphisms
  topological infinite cyclic profinite integers unique intermediate extension of
  each positive degree”: eight hits, including `FiniteField.Extension.frob`,
  `exists_frob_pow_eq`, `InfiniteGalois.profiniteGalGrp`, and
  `FiniteField.instIsCyclicAlgEquivOfFinite`; all component results only.
- `msearch.py ... loogle '"profinite", "frobenius"'`: zero hits.
- `msearch.py ... leansearch` with “finite field absolute Galois group is
  topologically generated by arithmetic Frobenius and is isomorphic to the
  completion of the infinite cyclic group”: eight component hits, including
  `Field.absoluteGaloisGroup`, `FiniteField.frobeniusAlgEquivOfAlgebraic_apply`,
  and the Krull topology instances, no complete theorem.
- `msearch.py ... grep` for `finiteField_absoluteGaloisGroup|profinite.*[Ii]nteger|
  completion.*Multiplicative|Frobenius.*generator`: only an unrelated Laurent
  series valuation hit. Direct rg searches in Mathlib, upstream WeilConjectures,
  and repository lean/Sheaf for `ZHat|Zhat|profinite.*integer`, completion of
  `Multiplicative`, cyclic completion, and the declaration/module names found
  no existing version of this full statement. Searching absoluteGaloisGroup and
  the general Galois-limit API found only the component interfaces I opened.

Other repairs: expanded the proof docstring to all six DAG steps, including
basis counting, degree uniqueness, both directions of divisibility, the union,
restriction-limit topology and generator normalization. Added non-public
proof-dependency imports `Sheaf.FieldTheory.UniqueSubfieldOfClosure` and
`Mathlib.FieldTheory.Finite.GaloisField`; I opened the former's exact declaration
and the finite Frobenius/closure/limit Mathlib declarations. Existing public
imports supply the remaining proof leaves. There are no new nodes or dependency
modules, no private duplicate notions, no definitions, and only the single
named theorem with proof `by sorry`. No mathematical proof was added.

Validation: the final module compiled cleanly with the prescribed
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N5 det-base-field-cd-galois-group
lean/Sheaf/FieldTheory/FiniteFieldAbsoluteGalois.lean`, both sandbox and library
forms, within the 60-second limit and without warnings. All Lean lines are at
most 100 characters. The node's `lean.statement` is verbatim the final signature.
