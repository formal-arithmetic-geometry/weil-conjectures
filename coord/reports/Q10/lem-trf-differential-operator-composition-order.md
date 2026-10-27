## Worker report

The module `Sheaf.RingTheory.DifferentialOperatorCompositionOrder` states
`LinearMap.IsDifferentialOperatorOfOrderLE.comp`, the composition bound of
Stacks algebra.tex, Tag 09CJ (`lemma-composition-differential-operators`).
Its only proof is `sorry`. The new definition module
`Sheaf.RingTheory.DifferentialOperatorOrder` supplies the actual recursive
predicate of Tag 09CI (`definition-differential-operators`) and its scalar
commutator, both with real data and no postponed proofs.

Read the item, its entire proof and its sole original statement dependency,
`def-weil-pbc-algebra-hom-quotient`. That dependency is a Mathlib leaf with
`mathlib_match`, so no `lean` record repair is needed. Read the `Algebra`
class in `Mathlib.Algebra.Algebra.Defs` and `AlgHom` in
`Mathlib.Algebra.Algebra.Hom`: the dependency's structure map is precisely
`algebraMap R C`. The quotient and ideal clauses of that dependency are not
used by this item. The new definition imports `Mathlib.Algebra.Algebra.Tower`,
which publicly imports the algebra homomorphism API through
`Mathlib.Algebra.Algebra.Equiv`, and uses its `Algebra.lsmul` declaration.
The composition module publicly imports the new predicate module; its only
original statement dependency is already available transitively. There are
no proof-dependency modules (`proof_deps` is empty).

Hypothesis and clause correspondence:

- The commutative ring `R` is `{R : Type u} [CommRing R]`; the commutative
  `R`-algebra `C` is `{C : Type v} [CommRing C] [Algebra R C]`. These are the
  structures supplied by the original Mathlib dependency, with no substituted
  notion of algebra or structure map.
- The three `C`-modules are `{L : Type w₁} {M : Type w₂} {N : Type w₃}`,
  their `AddCommGroup` instances, and `[Module C L] [Module C M] [Module C N]`.
  All five universes are explicitly declared and independent; no size or
  finiteness restriction is imposed.
- Restriction of scalars is expressed by `[Module R L] [Module R M]
  [Module R N]` with `[IsScalarTower R C L] [IsScalarTower R C M]
  [IsScalarTower R C N]`. The tower law and the algebra structure force the
  `R`-action to be `r • x = algebraMap R C r • x`, so these instances encode
  the stated restriction, rather than an additional mathematical assumption.
  Every `C`-module admits this action; no faithfulness is required.
- The natural order parameters are `{k l : ℕ}`. The bundled maps
  `{D : L →ₗ[R] M}` and `{E : M →ₗ[R] N}` express exactly `R`-linearity.
- The zero clause of `IsDifferentialOperatorOfOrderLE R C n T` is
  `∀ (c : C) (x : M), T (c • x) = c • T x`. Since `T` is already additive,
  this is exactly `C`-linearity, without a stronger condition on `T`.
- The successor clause is `∀ c : C,
  IsDifferentialOperatorOfOrderLE R C n (scalarCommutator T c)`.
  The helper is the actual difference
  `T.comp (Algebra.lsmul R R M c) - (Algebra.lsmul R R N c).comp T`.
  By the read definition of `Algebra.lsmul`, it evaluates to
  `T (c • x) - c • T x`, with the sign and module types of the node.
  The bundled operations construct its `R`-linearity without any `sorry`.
- `hD : IsDifferentialOperatorOfOrderLE R C k D` and
  `hE : IsDifferentialOperatorOfOrderLE R C l E` are the two order bounds.
- The conclusion is exactly
  `IsDifferentialOperatorOfOrderLE R C (k + l) (E.comp D)`; `E.comp D`
  evaluates to `x ↦ E (D x)`. No exact-order assertion or auxiliary conjunct
  is introduced.

Edge cases checked against the definition and source before writing:
`k = l = 0` says the composite of two `C`-linear maps is `C`-linear.
For `(k,l) = (0,1)` and `(1,0)`, the appropriate commutator summand is zero;
there is no negative-order predicate or subtraction on naturals in the
statement. At `(1,1)` the stated bound is two, as for two ordinary
polynomial derivations. A zero map has every bound; zero source, middle or
target modules are admitted. Zero rings are admitted (no `Nontrivial`), and
there is no characteristic restriction. The definition's natural recursion
never interprets order as minimal order. No statement dispute or correction
is needed.

Searches, all run before adding the declarations:

- `msearch.py leanfinder`, query "Composition of algebraic differential
  operators between modules has order at most the sum of their orders":
  eight hits, chiefly `LinearMap.compDer`, `Derivation.llcomp` and
  `Derivation.compAlgebraMap`. These concern derivations, not the recursive
  order predicate or its arbitrary-order composition bound.
- `msearch.py leansearch`, query "An R-linear map between modules over an
  R-algebra is a differential operator of order n if every commutator with
  multiplication has order n minus one": eight hits, including `Derivation`,
  `Derivation.hasCoeToLinearMap` and `KaehlerDifferential.DLinearMap`;
  none defines the general finite-order predicate.
- `msearch.py loogle`, query `DifferentialOperator, LinearMap.comp`: no hits;
  Loogle reports unknown identifier `DifferentialOperator`.
- `msearch.py grep`, query
  `DifferentialOperator|IsDiffOp|differentialOperator|differential.order`:
  no Mathlib hits.
- `rg` with the corresponding names and plain words in the live read-only
  `lean/WeilConjectures` and `lean/Sheaf`: no finite algebraic differential
  order predicate or composition theorem. Sheaf hits concern analytic
  differential operators and an SL2 representation. The prescribed
  `grep -rn` for this item's id in `lean/WeilConjectures` returns no match.
- `rg -l` on `dag/nodes` for `differential.?operator|differential order|09CI`:
  the algebraic hits include this item and its localization consumer, which
  describe the predicate inline; no existing definition node supplies it.
  Other nodes concern analytic operators, Jacobians or differentials.
- `tools/blueprint_refs.py search 'differential operator'`: zero blueprint
  nodes. `ancestor` identifies `lem-trf-local-term-locality`.
  Names `scalarCommutator` and `IsDifferentialOperatorOfOrderLE` have no match
  in Mathlib, upstream, Sheaf or `dag/lean_names_upstream.json`.

Both final modules compiled together through the prescribed `scompile.py`,
each separately in dependency order against the server's published build.
There were no errors or warnings. The theorem docstring contains all four
steps of the node's natural-language proof, including the zero-bound cases.
The original node is changed only in `lean` and the addition of the definition
node to `stmt_deps`; its statement, proof, source and other fields are intact.

## New nodes

`def-trf-differential-operator-order` defines scalar commutators and the
recursive bound on differential order between arbitrary algebra modules,
exactly Stacks 09CI. Its module is
`Sheaf.RingTheory.DifferentialOperatorOrder`; its main declaration is
`LinearMap.IsDifferentialOperatorOfOrderLE`, and its helper
`LinearMap.scalarCommutator` is listed in `lean.declarations`. The base ring,
algebra, module structures, restriction of scalars, zero-order linearity,
successor recursion and commutator sign match the clauses detailed above,
with two independent module universes. Its sole statement dependency is the
existing Mathlib algebra node. All searches are recorded in the new node,
including the exact `msearch.py` result records. No prior definition node,
Mathlib definition, upstream definition or project declaration was found.
Its blueprint provenance follows the item's existing historical route and
the ancestor returned by the blueprint tool. The item cites the new node;
no existing dependency record is changed. Independent delivery review is
performed by the maintainer, as specified by the dispatcher brief.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
