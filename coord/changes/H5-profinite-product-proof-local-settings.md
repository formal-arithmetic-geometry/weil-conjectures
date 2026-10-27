# AlgebraicGeometry.Scheme.UniversalCover.profinite_scheme_product_components

## Reason

The proof constructs the actual quotient diagrams and test-product pullbacks. Elaboration
needs the two backward definitional-equality transparency options when relating bundled
profinite morphisms and the actual scheme constructions. Two auxiliary class witnesses
are registered locally to elaborate the quotient diagrams. The stage-3 command scanner
requires this record for these file-local commands. Existing declarations, public imports,
attributes and signatures stay identical; there is no mathematical interface change.

## Old

The declaration commands before the namespace were:

```lean
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
```

No `quotientIndicesNonempty` or `quotientPowersFinite` helper existed. The theorem was:

```lean
theorem profinite_scheme_product_components : Nonempty ProfiniteSchemeProductComparisons.{u} := by
  sorry
```

## New

The declaration commands are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
```

The two new, proved private witnesses are registered locally in the existing namespace:

```lean
private theorem quotientIndicesNonempty (G : ProfiniteGrp.{u}) :
    Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩

attribute [local instance] quotientIndicesNonempty

private theorem quotientPowersFinite (G : ProfiniteGrp.{u}) (q : ℕ)
    (N : OpenNormalSubgroup G) : Finite ((quotientPowers G q).obj N) :=
  inferInstanceAs (Finite (Fin q → G ⧸ N.toSubgroup))

attribute [local instance] quotientPowersFinite
```

The theorem's signature is identical; its proof constructs all fields from proved
private helpers. Options affect elaboration of this file only. The local instance
registrations end at the namespace's `end` and are not exported to consumers.
No new global instance is introduced.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents --uses
AlgebraicGeometry.Scheme.UniversalCover.profinite_scheme_product_components` reports
zero downstream modules and only the theorem's own module mentioning its name.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents | H5 | Complete the proof; use local elaboration options and instances. Existing public interface unchanged. |

The DAG still requires the result from unfinished parents, so no module is withdrawn.
No target statement or definition used by a target changes; no consumer adaptation or
renewed statement review is needed.

## Status

landed 20261023T231333-L-3578284 2026-10-23 (merge of deliver/H5/Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents)
