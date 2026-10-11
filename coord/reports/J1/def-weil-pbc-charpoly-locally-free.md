## Worker report

Module: `lean/Sheaf/Algebra/LocallyFreeCharpoly.lean`. Main definition:
`Algebra.locallyFreeCharpoly`. This is an actual polynomial obtained by `Classical.choose`
from the landed `Algebra.charpoly_locallyFree_exists_unique`; it contains no `sorry`.
Three named theorems state the remaining clauses with `sorry`, with the node's corresponding
natural-language proof steps in their docstrings. They belong to this definition node's
well-posedness and specification, not to additional mathematical notions.

Hypothesis and clause correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`, including the zero ring.
- An A-module: `{M : Type v} [AddCommGroup M] [Module A M]`, with independent ring/module
  universes. These explicitly bound section variables occur in every declaration.
- Nonnegative integer rank n and finite cover size r: `{n r : ℕ}`. A finite family of ring
  elements is `f : Fin r → A`.
- The elements generate the unit ideal: `hgen : Ideal.span (Set.range f) = ⊤`.
- Each localization is free of rank n: `hfree` asserts existence of a
  `Module.Basis (Fin n) (Localization.Away (f i)) (LocalizedModule.Away (f i) M)`.
  The form `∃ _e : ..., True` is the existential-basis form of the recorded dependency;
  it supplies precisely a basis, not an additional assumption. `_e` avoids a linter warning.
- The given A-linear endomorphism is `φ : M →ₗ[A] M`.
- The polynomial has coefficients in A: the definition's result is `Polynomial A`.
- For every ring map A → A', the predicate P in `locallyFreeCharpoly_spec` binds
  `A' : Type (max u w)`, `[CommRing A']`, and `ρ : A →+* A'`; the local algebra instance is
  `RingHom.toAlgebra ρ`. The arbitrary universe w allows scalar extension to arbitrarily
  large universes. Smaller rings can be lifted into the displayed universe; this is the
  same universe convention as the landed existence theorem.
- The base-changed module is `A' ⊗[A] M`, Mathlib's convention equivalent by
  `TensorProduct.comm` to the node's `M ⊗[A] A'`. Its endomorphism is `φ.baseChange A'`.
- Being free of rank n after base change is expressed by universally quantifying each
  `e : Module.Basis (Fin n) A' (A' ⊗[A] M)`. With no such basis the condition is vacuous;
  with one it imposes equality in every basis. This also states basis independence.
- Coefficientwise polynomial image: `χ.map ρ`.
- Determinant T·1 minus the base-changed endomorphism: the concrete matrix expression
  `(LinearMap.toMatrix e e (φ.baseChange A')).charpoly`. Mathlib's `Matrix.charpoly` is
  the determinant of its characteristic matrix, whose entries are T on the diagonal
  minus the coefficientwise embedded matrix entries. This is exactly the node's
  explicitly permitted concrete formula. It avoids needing auxiliary free-module
  instances on the polynomial scalar extension.
- Existence and unique characterization: `locallyFreeCharpoly_spec` states P for the
  defined polynomial and `∀ χ, P χ → χ = locallyFreeCharpoly f hgen hfree φ`.
- Monic form: `∃ c : Fin n → A`, with equality to `Polynomial.X ^ n +
  ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)`.
- The free case: the final clause of `locallyFreeCharpoly_spec` quantifies every
  `e : Module.Basis (Fin n) A M` and identifies the result with the matrix characteristic
  polynomial of φ in e. This is equivalent to the dependency's conditional Nonempty-basis
  formulation, including when no global basis exists.
- Independence of all choices f and n: `locallyFreeCharpoly_eq` compares two covers f and g
  of sizes r and s with ranks n and m, without requiring n = m or a nonzero ring.
- For a nonzero ring the module determines n: `locallyFree_constantRank_eq` states n = m
  for the two covers under `[Nontrivial A]`, exactly the node's parenthetical restriction.
  There is no such assumption on the definition, specification, or independence theorem.

Dependency declarations read and used:

- `Sheaf.Algebra.CharpolyLocallyFree`, `Algebra.charpoly_locallyFree_exists_unique`: its
  complete signature and proof docstring were read. This is the definition's direct data
  source, instantiated with universe parameters `{u, v, u}`; thus choosing data does not
  leave an unconstrained universe parameter in the definition. The specification then
  quantifies the characterization in arbitrary universes.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule.Away`: module
  localizations in all cover hypotheses; also read `LocalizedModule.mkLinearMap` and
  `IsLocalizedModule.lift`, which underlie the node's further-localization argument.
- `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`, with ring structure
  and algebra instance from `Mathlib.RingTheory.Localization.Away.Basic`: the local rings.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`, `LinearMap.baseChange`: scalar extension
  of φ, with the algebra instance supplied by the ring map.
- `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`; `Polynomial.map`, `Polynomial.C`,
  `Polynomial.X`: polynomials, coefficient images and the monic expansion.
- `Mathlib.LinearAlgebra.Matrix.Defs`, `Matrix`, and `LinearMap.toMatrix`:
  the finite square matrix in each chosen basis.
- `Mathlib.LinearAlgebra.Determinant`, `LinearMap.det` was read, including its basis
  description. The statement uses the node's concrete matrix-determinant presentation
  through `Matrix.charpoly` from `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`, rather
  than applying `LinearMap.det` directly. Both give the node's determinant on a free
  finite module. All needed imports are supplied by the existence module; the new
  module imports only that used module.

Edge cases checked before writing:

- n = 0: `Fin 0` is empty, the sum has no terms, and the monic expansion is 1; the
  0-by-0 characteristic polynomial is 1, including after base change.
- A = 0: allowed everywhere except the rank-uniqueness theorem; `Polynomial A` is
  subsingleton, so every rank/cover gives the same polynomial. The expansion is still
  valid, since 1 = 0. No degree n claim wrongly excludes the zero ring.
- r = 0: the empty span equals ⊤ only over the zero ring. The local-freeness condition is
  then vacuous and the polynomial remains uniquely determined in the zero ring.
- Nilpotent or zero cover elements may give zero localizations; no nonzero-localization
  hypothesis is imposed. The whole family must generate the unit ideal.
- The zero module, arbitrary characteristics, and modules without a global free basis
  are allowed. No finite/free typeclass on M is silently imposed.
- Different cover sizes, different stated ranks, and independent universes u and v
  occur in the choice-independence statement.

Searches for an existing definition:

- `msearch.py ... leanfinder "characteristic polynomial of an endomorphism of a finite
  locally free module of constant rank"`: eight hits, including `LinearMap.charpoly`,
  `LinearMap.polyCharpoly`, and `LinearMap.eval_charpoly`. The charpoly declaration
  requires `[Module.Free R M] [Module.Finite R M]`; no locally free construction.
- `msearch.py ... loogle "LinearMap.charpoly, Module.Projective"`: zero hits.
- `msearch.py ... grep "charpoly|CharPol" RingTheory/Flat`: zero hits.
- `msearch.py ... leansearch "characteristic polynomial finite locally free module"`:
  service unavailable (Internal Server Error). No mathematical verdict drawn from that.
- `rg -n 'charpoly|Charpoly|CharPol'` in project/source RingTheory directories, then
  `rg -n 'charpolyLocallyFree|charpoly_locallyFree|CharPol|charpoly'` in the full source:
  hits are usual free-module characteristic polynomials and representation applications.
- `grep -rn 'def-weil-pbc-charpoly-locally-free'` in the full source: no hits.
- `rg -n 'charpoly|charpoly_locallyFree' lean/Sheaf`: only the landed existence module,
  which states existence but does not define the polynomial.
- New declaration names searched in `dag/lean_names_upstream.json`, Mathlib, and
  `WeilConjectures`: no clashes.

Source verification: the literature checkout is absent on this machine, so the relevant
paragraph was opened at [Stacks Tag 09XI](https://stacks.math.columbia.edu/tag/09XI), proof
of (3)⇒(1). It defines the free case by the matrix polynomial and the locally free case
by gluing. The node gives its explicit universal characterization and well-posedness proof.
No node correction or disputed statement was needed; no new nodes or dependency modules.

Validation: server single-file compile passed without warnings after changing the unused
existential basis name to `_e`. All variables and universes are explicitly bound. Every
new theorem proof is `sorry`, as required at stage 2.

## Second reading by J1

I independently opened the item's node and delivered module, every statement-dependency
node, the full landed `Algebra.charpoly_locallyFree_exists_unique` declaration and docstring,
and the Mathlib declarations identified below. No corrected statement, new definition node,
or dependency module is present in this delivery.

Source check: the local literature checkout is absent. I read the Stacks source `.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
`lemma-characterize-henselian-pair`, proof of (3)⇒(1), characteristic-polynomial paragraph
(current lines 2414–2429), and https://stacks.math.columbia.edu/tag/09XI. The paragraph
constructs the polynomial from matrix characteristic polynomials by standard-cover gluing.
The surrounding ideal/idempotent assumptions concern its application in the henselian-pair
proof; they are not prerequisites for this construction on a locally free module. The
node's constant-rank specialization and universal characterization agree with that
construction. No Noetherian, field, characteristic, or nonzero-ring assumption is required.
The historical line numbers in the node have moved in the current upstream source.

My object/hypothesis/conclusion list, matched independently against the Lean:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative ring A | `{A : Type u} [CommRing A]` in the explicitly bound section | Exact, zero ring included |
| A-module M | `{M : Type v} [AddCommGroup M] [Module A M]` | Exact, no global freeness or finiteness instance |
| Nonnegative integer n | `{n : ℕ}` | Exact |
| Finite cover f₁,…,fᵣ | `{r : ℕ} (f : Fin r → A)` | Exact, enumeration starts at zero only by convention |
| Cover generates unit ideal | `Ideal.span (Set.range f) = ⊤` | Exact |
| Each M_f is free of rank n over A_f | `∀ i, ∃ _e : Module.Basis (Fin n) (Localization.Away (f i)) (LocalizedModule.Away (f i) M), True` | Exact, basis existence is equivalent to the stated isomorphism |
| A-linear endomorphism φ | `φ : M →ₗ[A] M` | Exact |
| Defined polynomial in A[T] | `locallyFreeCharpoly … : Polynomial A` | Exact; `Classical.choose` of the recorded existence theorem |
| Every ring map A→A′ | In the specification's `P`, `∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A')` | Exact up to universe transport, detailed below |
| Base-changed module and endomorphism | `RingHom.toAlgebra ρ`, `A' ⊗[A] M`, `φ.baseChange A'` | Exact, tensor factors commuted as allowed by the recorded dependency |
| Conditional freeness of base change | `∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M)` | Exact: vacuous without a basis, all bases otherwise |
| Coefficientwise image equals determinant | `χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly` | Exact concrete formula explicitly permitted by the node |
| Existence and uniqueness | `P (locallyFreeCharpoly …) ∧ ∀ χ, P χ → χ = locallyFreeCharpoly …` | Exact, same inputs and characterization |
| Monic expansion | `∃ c : Fin n → A, locallyFreeCharpoly … = Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)` | Exact: precisely all exponents below n |
| Independence of cover and stated rank | `locallyFreeCharpoly_eq`, with separate `n m r s`, covers f and g and one φ | Exact, no equality-of-rank assumption |
| Nonzero ring determines rank | `locallyFree_constantRank_eq [Nontrivial A] … : n = m` | Exact, only this clause requires nonzero A |
| Globally free case | Final specification conjunct `∀ e : Module.Basis (Fin n) A M, … = (LinearMap.toMatrix e e φ).charpoly` | Exact conditional case, in every basis |

Dependencies are the same mathematical objects, not private replacements. I checked:
`LocalizedModule.Away` is localization at `Submonoid.powers`, with its canonical
localized-ring module structure; `LocalizedModule.mkLinearMap` and `IsLocalizedModule.lift`
give the localization map and universal property. `Localization.Away` and
`IsLocalization.Away` likewise localize the ring at powers. `LinearMap.baseChange`
(Tower.lean:661) sends `a ⊗ m` to `a ⊗ φ m`, so commuting tensor factors recovers the
node's φ⊗1. `Matrix` (Defs.lean:57) is the expected function of two indices.
`Matrix.charmatrix` (Charpoly/Basic.lean:50) is `T I - C(matrix)` and `Matrix.charpoly`
(line 134) is its determinant. `LinearMap.det_toMatrix` (Determinant.lean:212) identifies
that matrix determinant with the recorded endomorphism determinant. Thus using the
matrix formula directly neither substitutes a different notion nor requires a new node.
`Polynomial`, `Polynomial.map`, `C` and `X` implement the ring and coefficientwise map.
The landed existence theorem has exactly these cover/basis hypotheses and supplies the
chosen polynomial, its uniqueness, expansion and conditional free case; the definition
uses that theorem directly at universes `{u, v, u}`.

Universes: u and v are independent. In `P`, the arbitrary w allows arbitrary larger
coefficient rings, while the floor u ensures that the original localizations can be tested
for uniqueness. For a ring B in any smaller universe, apply `P` to `ULift.{u} B`, compose
its map with the lift ring isomorphism, transport a basis of `B ⊗[A] M` through the scalar
extension equivalence, and map the resulting matrix-polynomial identity back. This yields
the same identity over B. Conversely the node's characterization implies every displayed
instance of `P`. Therefore there is no excluded mathematical base change. For comparing
the chosen polynomial with the existence theorem in a larger universe, lift the original
localizations as well; both restrict to the same local matrix polynomials and coefficient
injectivity identifies them. I clarified these transport steps in the specification's
proof docstring. Simply deleting the floor from the uniqueness predicate would be wrong:
a universe too small to contain the test localizations need not provide enough ring maps
to detect coefficients. The signature was correctly retained.

Edge cases: `r = 0` forces A to be the zero ring since the empty span is bottom; hfree is
then vacuous and `Polynomial A` is subsingleton. `n = 0` gives the empty sum and polynomial
1, matching the empty matrix determinant. The zero module over a nonzero ring has rank
zero; over the zero ring any stated rank is allowed, and polynomial independence still
holds. Zero or nilpotent cover elements can yield zero localizations and are allowed.
No nontriviality instance occurs in the definition, specification or independence theorem.
All characteristics are covered. There is no scheme parameter; the algebraic counterpart
of the empty affine scheme is precisely the admitted zero ring.

Independent searches, with different conceptual queries from the first worker:

- LeanFinder, `determinant polynomial for a finite projective module without a global
  basis`: eight hits, chiefly `LinearMap.det_def`, `detAux`, and free-module charpoly
  coefficient lemmas. Opened determinant definitions: on a module without a finite basis
  that determinant defaults to 1; it is not this locally free characteristic polynomial.
- Loogle, `charpoly, Module.Finite`: unqualified identifier was rejected, no conclusion.
  Follow-up `LinearMap.charpoly` returned twelve hits. Opened Charpoly/Basic.lean: the
  definition requires both `Module.Free` and `Module.Finite`, so it excludes nonfree
  locally free modules; no exact existing construction.
- LeanSearch, `characteristic polynomial projective module scalar extension`: Internal
  Server Error, recorded unavailable; no mathematical verdict based on this service.
- `msearch.py … grep "characteristic polynomial|charpoly" RingTheory/Flat`: zero hits.
  Direct `rg` of the entire `WeilConjectures/` and project's `lean/Sheaf/` for
  `charpoly|CharPol|characteristic polynomial` found free-module/representation results
  and the landed existence theorem, but no definition of the glued polynomial.
- `rg` for `locallyFreeCharpoly|locallyFree_constantRank_eq` in Mathlib, the source and
  `dag/lean_names_upstream.json`: no name clashes. The existing existence theorem is
  a data source, not a duplicate of this definition.

Mismatches and repairs: no mathematical hypothesis or conclusion mismatch found, no node
correction needed. The specification's universe-comparison proof description omitted the
explicit lifting of the test localizations; I added the `ULift` and transport explanation,
including descent to smaller target universes. All declaration signatures are unchanged.
Every new theorem remains `by sorry`; the sole definition contains no `sorry` and its data
comes from the named dependency theorem. Module and declaration docstrings have the source
and blueprint id, and the three proof steps are covered by the specification and the two
independence/rank statements. The import is used, names have no `Sheaf` namespace prefix,
and variables/universes are explicitly bound. The node's recorded main signature matches
the definition verbatim. Server compilation and delivery preflight are checked below.

Validation completed: `scompile.py J1 def-weil-pbc-charpoly-locally-free` compiled the
113-line module on the server in 1.4 seconds, exit 0, without warnings.
`deliver2.py J1 def-weil-pbc-charpoly-locally-free --no-push` printed OK: the delivery
compiles and passes the stage-2 preflight.
