## Worker report

The module `Sheaf.Algebra.Lie.SemisimpleSurjectiveImage` states
`LieAlgebra.hasTrivialRadical_of_surjective` with one `sorry` and no new definitions.
Only the item's `lean` field changes. No missing notions, dependency repairs,
statement corrections, or disputed statements were found.

Source checked: Milne, Algebraic Groups (2017), §22c, printed p.475
(PDF p.487), including the standing assumptions at the start of §22c and
the final paragraph under The Casimir operator. That paragraph decomposes
a semisimple Lie algebra into the kernel ideal and a complementary semisimple
ideal. The complete four-step node proof is carried in the declaration docstring.
Also read the current blueprint's `def-wf-lie-algebra` and
`def-wf-semisimple-lie-algebra` under `literature/blueprint/latest/`.

Hypotheses and clauses, in order:

- The characteristic-zero field F is `(F : Type u) [Field F] [CharZero F]`.
- The Lie algebra L is `(L : Type v) [LieRing L] [LieAlgebra F L]`;
  its finite dimension is `[Module.Finite F L]`.
- The Lie algebra H is `(H : Type w) [LieRing H] [LieAlgebra F H]`;
  its finite dimension is `[Module.Finite F H]`. Mathlib's `FiniteDimensional`
  is an abbreviation for `Module.Finite`, so this retains exactly the given condition.
- The linear map preserving brackets is `(q : L →ₗ⁅F⁆ H)`. The declaration
  `LieHom` extends `L →ₗ[F] H` with precisely the field
  `map_lie' : ∀ {x y : L}, q ⁅x,y⁆ = ⁅q x,q y⁆`.
  Thus bundling adds no requirement to the specified linear map and identity.
- Surjectivity is `(hq : Function.Surjective q)`.
- The hypothesis that L has no nonzero solvable Lie ideal is
  `[HasTrivialRadical F L]`.
- The conclusion that H has no nonzero solvable Lie ideal, and hence is
  semisimple in the specified sense, is `HasTrivialRadical F H`.
  Both uses have exactly that interpretation by
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` and the recorded
  upstream `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot`.
  No use is made of the different direct-sum predicate `IsSemisimple`.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-wf-lie-algebra`: `LieRing`, `LieAlgebra`, and `LieHom` in
  Mathlib.Algebra.Lie.Basic; `LieIdeal` in Mathlib.Algebra.Lie.Ideal;
  `LieAlgebra.IsSolvable` and `LieAlgebra.isSolvable_iff` in
  Mathlib.Algebra.Lie.Solvable. The closed upstream declaration
  `LieAlgebra.isSolvable_iff_exists_derivedSeries_eq_bot` is in
  WeilConjectures.Mathlib.Algebra.Lie.Radical, which is publicly imported.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` in
  Mathlib.Algebra.Lie.Semisimple.Defs and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` in
  Mathlib.Algebra.Lie.Semisimple.Basic; also the closed upstream declaration
  `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot` in the same
  publicly imported Radical module.
- Proof dependency `lem-sfb-semisimple-lie-ideal-complement`:
  `LieIdeal.isCompl_killingCompl` in Mathlib.Algebra.Lie.Killing,
  imported as a proof import. Mathlib.Algebra.Lie.CartanCriterion is also
  a proof import, providing `LieAlgebra.HasTrivialRadical.instIsKilling`
  under the given characteristic-zero and finite-dimensional assumptions.

Edge cases checked before writing: H = 0 permits any surjective zero map;
L = 0 with surjective q forces H = 0; both cases have trivial radical and
are included. The identity map and projections from a direct sum of
semisimple Lie algebras satisfy the statement. No nonzero or nonabelian
assumption is imposed. A nonzero abelian L fails the radical hypothesis,
as it should. A characteristic-zero field need not be algebraically closed,
and no such condition was imposed. The independent explicit universes u, v, w
allow the field and the two Lie algebras to have different sizes.

Searches (2026-10-24), using the required msearch.py wrapper:

- LeanFinder: "A surjective homomorphism of finite dimensional Lie algebras over
  a characteristic zero field preserves having no nonzero solvable ideal".
  Eight hits, including `Function.Surjective.lieAlgebra_isSolvable`,
  `Function.Surjective.isEngelian`, and `LieHom.isSolvable_range`;
  none states trivial radical descends.
- Loogle: "LieAlgebra.HasTrivialRadical, Function.Surjective". Zero hits.
- LeanSearch: "A quotient of a finite dimensional characteristic zero Lie algebra
  with no nonzero solvable ideal has no nonzero solvable ideal". Eight hits:
  quotient Lie structures and the trivial-radical characterization, no match.
- Mathlib grep: "HasTrivialRadical|hasTrivialRadical|isSemisimple" in Algebra/Lie.
  Twenty-five returned hits; inspected Semisimple/Defs, Semisimple/Basic,
  Killing and CartanCriterion. Additional direct rg of Semisimple for
  surject/quotient/range/map found no matching theorem.
- Project rg: "HasTrivialRadical|hasTrivialRadical|surjective.*[Ss]emisimple|
  [Ss]emisimple.*surjective" across lean/WeilConjectures and lean/Sheaf.
  Results include Radical, Solvable, Semisimple/Lemmas, and statements about
  semisimple group Lie algebras and Chevalley theory; none matches the item.
  In particular `map_radical_le` only gives the opposite useful inclusion,
  and `hasTrivialRadical_quotient_center` has a different hypothesis and quotient.
- Exact node-id search in lean/WeilConjectures returned no hits.
  Exact candidate-name search `hasTrivialRadical_of_surjective` in Mathlib,
  lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json returned
  no existing declaration.

Compilation: the prescribed scompile.py compiled the sandbox module and
its actual library module name cleanly (1.2 seconds each). Auto-bound implicits
are disabled with `set_option autoImplicit false`; all universes are explicit.

## Second reading by Q14

Re-read the node and completed module in a separate checking pass. The field
and characteristic binders reproduce the source's standing assumptions. Both
Lie algebras retain finite dimension; `Module.Finite` is definitionally the
usual finite-dimensional predicate over a field. The bundled `LieHom` is
exactly the node's linear map plus bracket identity, and `hq` supplies precisely
surjectivity. The radical hypothesis and conclusion use the dependency node's
recorded predicate, with its no-solvable-ideals equivalence read in full.
The zero source and zero target cases remain included, and the universes
remain independent. The four proof-docstring steps reproduce the kernel
complement, bijectivity on the complement and commuting ideals, inverse-image
ideal, and derived-series vanishing arguments. No mismatches were found and
no statement or dependency changes were needed. This is the dispatcher's
single-worker delivery; independent maintainer review follows delivery.
