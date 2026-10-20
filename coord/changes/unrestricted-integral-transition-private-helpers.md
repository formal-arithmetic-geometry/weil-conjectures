# unrestrictedIntegralTransition_existsUnique private proof helpers

## Reason

The proof adds private helper declarations and module-local elaboration commands in
`Sheaf.Paper.IntegralReductionTowerUnrestricted`. The preflight conservatively classifies
new namespace, universe, variable, option and local-attribute commands as an interface
change and requests this record. No existing statement, signature, visibility, import,
or public definition changes. The theorem's `sorry` is replaced by a complete proof.

## Old

The existing module-level declarations surrounding the insertion were:

```lean
set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
```

There were no declarations in `SheafOfModules.UnrestrictedTowerProof` and no private
coefficient-step/module-step helpers in this file. The public existence-uniqueness
theorem had its existing, unchanged signature and body `by sorry`.

## New

The original commands above remain. The added elaboration option is:

```lean
set_option backward.isDefEq.respectTransparency false
```

The generic proof helpers are private and enclosed in the namespace
`SheafOfModules.UnrestrictedTowerProof`, with explicitly bound universes `a b r` and
site/sheaf parameters. They construct the sectionwise tensor map, its sheafification,
restriction of scalars, transport across the existing object equalities, naturality,
and extensionality. The specialized private helpers construct the coefficient step and
use `limit.w` for its compatibility with the completed projections. Two typed private
lemmas expose just the object and map identifications of the existing reduction
witness; these avoid repeatedly expanding its full derived-functor contract. The
extensionality helper cancels the explicit transport directly, avoiding an `Epi`
typeclass search. Their full Lean
signatures and proofs are in the delivered module; no public signatures are added.

The performance attributes, all local, are exactly:

```lean
attribute [local irreducible] sectionMap presheafMap sheafMap restrictedMap
attribute [local irreducible] identifiedMap
attribute [local irreducible] unrestrictedIntegralReductionExistence
attribute [local irreducible] unrestrictedModuleStep
```

These prevent unnecessary unfolding within this proof. They do not change reducibility
for importers. Every existing public definition retains its original body. No consumer
can mention the private helpers, and options and section variables do not alter the
imported public API or the mathematical meaning of any target.

## Users

The source-only downstream scan finds 1588 transitive importers. All retain the exact
same public constants, signatures and definitions. The theorem has three downstream
textual users; none requires editing. This packet adapts no other module and therefore
has no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralReductionTowerUnrestricted | S5 | One hole closed; private helpers only. |
| Sheaf.Paper.IntegralReductionTowerCanonical | unclaimed | Same theorem signature; no adaptation. |
| Sheaf.Paper.IntegralReductionTowerWellDefined | unclaimed | Same theorem signature; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | P6 | Same theorem signature; no adaptation. |

No holder is acquired or changed for any consumer. The helper-only command changes
have no affected public declaration and require no consumer repair.

## Status

landed 20261020T132039-L-1406426 2026-10-20 (merge of deliver/S5/Sheaf.Paper.IntegralReductionTowerUnrestricted)
