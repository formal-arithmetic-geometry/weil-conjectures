## Worker report

The module `Sheaf.RingTheory.FinitePolynomialCoordinateLift` states the node in two
theorems, both with `sorry`. It introduces no new definition or axiom and changes
only the item's `lean` field. No missing dependency, disputed statement, or
statement correction was found.

Source read: Stacks Project algebra.tex, Tag 051P,
`lemma-refined-Noether-normalization`, including its full induction proof and
last extension z_n mapping to y_n. I also read the current blueprint's
`lem-trf-local-term-locality.proof.md` under literature/blueprint/latest; this
node is a generated elementary ingredient along its recorded route, not that
blueprint lemma's own statement.

Hypothesis and clause correspondence:

- Commutative rings R and S: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The universes are independent. The ring map is `β : R →+* S` and its module
  finiteness is `hβ : β.Finite`, which unfolds through `β.toAlgebra` to
  `Module.Finite R S`. The ideal is `p : Ideal S`, with no primality assumption.
- The specified finite list is `s : ℕ` and `b : Fin s → S`. Its generating
  hypothesis is exactly `∀ y : S, ∃ a : Fin s → R, ∑ j, β (a j) * b j = y`.
  The first conclusion quantifies over every such list. For every polynomial
  F it supplies `A : Fin s → Polynomial R` and the identity
  `∑ j, mapRingHom β (A j) * C (b j) = F`. These are precisely polynomial
  linear combinations of the same constants. A scalar action need not be
  installed separately: multiplication by `mapRingHom β (A j)` is that action.
- The coefficientwise extension with Z mapping to T is the existing
  `Polynomial.mapRingHom β`, whose definition is `Polynomial.map β`.
  Separate bound names Z and T are the source and target's respective `X`.
  Its finiteness is the second conjunct `(mapRingHom β).Finite`.
- Ideal extension is `Ideal.map C`; ideal addition is the supremum `⊔`;
  `(T)` and `(Z)` are `Ideal.span {X}` in the appropriate rings. The third
  conjunct is verbatim the required equality of contraction ideals, using
  `Ideal.comap (mapRingHom β)` and `Ideal.comap β p`.
- The fourth conjunct quantifies over every `H : Polynomial R` and says that
  its coefficientwise image belongs to the target ideal if and only if
  `β (H.eval 0) ∈ p`. Evaluation at zero, not an unspecified coefficient map,
  renders the stated equivalent criterion.
- The final specialization is
  `Polynomial.finite_mapAlgHom_and_comap_coordinate_ideal`. The binders are
  `{k : Type u} [Field k] (m r : ℕ) (hr : r ≤ m)`, so m=0 and r=0 are allowed.
  Both polynomial coefficient rings are `MvPolynomial (Fin m) k`; different
  letter names z and y do not require distinct carrier types. The map is a
  finite k-algebra homomorphism `β` with `hβ : β.Finite`.
- Its coordinate-contraction hypothesis is `hp`, an equality with
  `Ideal.span (MvPolynomial.X '' {i : Fin m | r ≤ i.val})`. Zero-based index
  i with value r is the paper's z_(r+1), and indices run through m-1.
- The new k-algebra map is the existing canonical `Polynomial.mapAlgHom β`.
  Its domain and target are the iterated polynomial rings k[z_1,...,z_m][Z]
  and k[y_1,...,y_m][T]. This is the ordinary (m+1)-variable polynomial ring
  presented by grouping monomials in the last variable. In particular no
  arbitrary map or existential choice stands in for the canonical extension.
  The first conjunct states its finiteness. The second contracts
  `Ideal.map C p ⊔ Ideal.span {X}` to the span of `insert X` into the image
  of the old coordinate variables under `fun i ↦ C (MvPolynomial.X i)`.
  Thus the last variable and exactly z_(r+1),...,z_m generate the contraction.

Dependency declarations read and used:

- def-weil-finitely-generated-module: `Module.Finite`,
  Mathlib.RingTheory.Finiteness.Defs (full signature and docstring at line 117).
  The same module defines `RingHom.Finite` (line 170) and `AlgHom.Finite`
  (line 189), the map-specific wrappers used here.
- def-weil-pbc-mv-polynomial-ring: `MvPolynomial`,
  Mathlib.Algebra.MvPolynomial.Basic (line 85), with its monomial-algebra
  definition. The recorded universal-property declarations
  `MvPolynomial.aeval` (Mathlib.Algebra.MvPolynomial.Eval, line 593) and
  `MvPolynomial.algHom_ext` (Basic, line 436) were also inspected. The
  statement uses this ring directly for the m old coordinate variables.
- `Polynomial.mapRingHom` (Mathlib.Algebra.Polynomial.Eval.Defs, line 534)
  and `Polynomial.mapAlgHom` (Mathlib.Algebra.Polynomial.AlgebraMap,
  line 168) supply the canonical extensions. No dependency API repair is needed.

Edge cases checked mathematically before writing:

- s=0: the empty-sum generating hypothesis forces S to be the zero ring;
  its polynomial ring is zero and the empty list still generates.
- R or S zero: no `Nontrivial` instance is assumed. When R is zero and a
  ring map exists, S is zero; the asserted ideals are still well-typed.
- Noninjective finite map Z to Z/4, p=(2): target contraction is (2,Z),
  and the constant-term criterion is reduction of H(0) modulo 2.
- Finite map Z to Z[i], p=(1+i): contraction is again (2,Z).
- p=top gives both full ideals; p=bot gives the constant-term kernel
  condition, without assuming that β is injective.
- m=0, r=0, and r=m: the old coordinate-variable set is empty, and the
  contraction in the conclusion is exactly the ideal generated by the new X.
- A nonprime ideal p is allowed; evaluation at zero detects ideal membership
  for every ideal, so the proof has no hidden primality or field assumption
  in the general result.

Searches actually run (2026-10-24):

- msearch.py grep: `mapRingHom.*[Ff]inite|[Ff]inite.*mapRingHom|comap.*(span|eval)|span.*(comap|eval)` in `RingTheory/Polynomial`. Result: 5 hits: `Mathlib/RingTheory/Polynomial/Ideal.lean`, `Mathlib/RingTheory/Polynomial/Ideal.lean`, `Mathlib/RingTheory/Polynomial/Quotient.lean`, `Mathlib/RingTheory/Polynomial/Quotient.lean`, `Mathlib/RingTheory/Polynomial/Basic.lean`; no exact match for all clauses.
- msearch.py loogle: `Polynomial.mapRingHom, RingHom.Finite`. Result: 0 hits; no exact match for all clauses.
- msearch.py leanfinder: `For a finite ring map R to S the same module generators generate S[T] over R[T] and the contraction of p S[T] plus (T) is the extension of the contraction of p plus (T)`. Result: 8 hits: `Algebra.FinitePresentation.polynomial`, `Algebra.Generators.toExtension_commRing`, `AdjoinRoot.finitePresentation`, `RingHom.FinitePresentation.polynomial_induction`, `Polynomial.map_under_lt_comap_of_quasiFiniteAt`, `Algebra.FinitePresentation.mvPolynomial_of_finitePresentation`, `Algebra.SubmersivePresentation.map_jacobianRelationsOfHasCoeffs`, `MvPolynomial.finite_universalFactorizationMap`; no exact match for all clauses.
- msearch.py leansearch: `The constants of any finite generating family for S over R generate S[X] over R[X], and comap of p S[X] plus (X) is comap p R[X] plus (X)`. Result: 8 hits: `Algebra.FiniteType.iff_exists_generators`, `PowerSeries.fg_iff_of_isPrime`, `Algebra.FiniteType.instPolynomial`, `Polynomial.adjoin_X`, `Polynomial.mem_closure_X_union_C`, `RingHom.EssFiniteType.finset`, `Algebra.Generators.mk`, `instIsIntegralPolynomial`; no exact match for all clauses.
- Direct rg over lean/WeilConjectures and lean/Sheaf for finite polynomial
  extension, coordinate lift, zero section, and the proposed declaration names;
  direct node-id search in lean/WeilConjectures; name search also in
  dag/lean_names_upstream.json and all Mathlib. No existing whole statement or
  collision was found. Mathlib's evaluation, ideal-map, finite-presentation,
  and universal-factorization results cover only pieces or other maps.

Validation: scompile.py compiled the module twice, as a sandbox module and at
its intended library path, with no error or non-sorry warning. The file has
`autoImplicit false`, all type and universe variables explicitly bound, and
no theorem proof other than `sorry`. Both theorem docstrings carry the source,
blueprint id, and the corresponding steps of the node's proof. No new nodes
or dependency modules are needed.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
