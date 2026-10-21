# SupportQuotientProduct local elaboration commands

## Reason

The proof adds declaration-scoped elaboration options, local instance priorities and
local reducibility attributes. These expose existing categorical APIs to Lean without
repeatedly unfolding the site and derived tensor constructions. In particular the generic
K-flat proof and the supported localization definitions must use the same braiding and
cochain tensor instances. All eight existing public definitions and both public imports
are verbatim. All new helpers and instances are private and proved. No public attribute
is added or removed.

The existing public theorem keeps its source text byte for byte. It is elaborated outside
the namespace block that carries the module-local `SymmetricCategory.toBraidedCategory`
priority, so its elaborated type is the published one. This is a reviewer correction of
2026-10-21, re-applied on the repair head 13dc6b7: under that priority the delivered
statement elaborated with the symmetric-category braiding and the `ULift.ring` ring path,
not the published `ModuleCat.MonoidalCategory.instBraidedCategory` and `CommRing.toRing`
path. The proof is the private theorem `supportQuotient_product_aux`, stated with explicit
`IsIso` categories under the local priority. The public theorem is that term, which the
kernel accepts up to definitional unfolding. No target statement or definition is changed.

## Old

The original module options were:

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
```

The original theorem signature was:

```lean
theorem supportQuotient_product
    (A : Type u) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (∃! e :
      etaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        etaleSupportQuotientPullback A j (pullback.snd f g) ≅
          etaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      etaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (etaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (etaleSupportQuotientPullback A i (pullback.fst f g))
        (etaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      etaleSupportQuotientProductNatural A (pullback f g)
        (etaleSupportQuotientProductGenerator A f g i j)
        (etaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom) ∧
    (∃! e :
      proEtaleSupportQuotientPullback A i (pullback.fst f g) ⊗
        proEtaleSupportQuotientPullback A j (pullback.snd f g) ≅
          proEtaleSupportQuotient A (Etale.supportedProductImmersion f g i j),
      proEtaleSupportQuotientProductGenerator A f g i j ≫ e.hom =
        proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j) ∧
      IsIso (proEtaleSupportQuotientDerivedComparison (ULift.{u + 1, u} A) (pullback f g)
        (proEtaleSupportQuotientPullback A i (pullback.fst f g))
        (proEtaleSupportQuotientPullback A j (pullback.snd f g))) ∧
      proEtaleSupportQuotientProductNatural A (pullback f g)
        (proEtaleSupportQuotientProductGenerator A f g i j)
        (proEtaleSupportQuotientMap A (Etale.supportedProductImmersion f g i j)) e.hom)
```

## New

The module-local commands before the definitions are:

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance 20000] AlgebraicGeometry.Etale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.ProEtale.upperStar

namespace AlgebraicGeometry.Scheme

attribute [local implicit_reducible] etaleSupportQuotient etaleSupportQuotientMap
  proEtaleSupportQuotient proEtaleSupportQuotientMap
```

After the definitions, the coefficient braiding is selected through the symmetric
structure, exactly as in the existing generic-coefficient localization APIs. The specialized
ModuleCat braiding and this inherited braiding are definitionally equal, but reconstructing
their equality inside a derived tensor object makes kernel checking exceed the file limit.
This is a module-local instance priority, not a new public instance:

```lean
attribute [local instance 2000] SymmetricCategory.toBraidedCategory
```

After the definitions, the following attributes are local to this module:

```lean
attribute [local irreducible] etaleSupportQuotientDerivedComparison
  proEtaleSupportQuotientDerivedComparison etaleSupportQuotientProductNatural
  proEtaleSupportQuotientProductNatural

attribute [local implicit_reducible] etaleSupportQuotientPullback
  proEtaleSupportQuotientPullback
```

After the generic derived helpers, these additional local attributes suppress automatic
expansion of the derived monoidal construction:

```lean
attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.laxMonoidalQ DerivedCategory.laxMonoidalQh
```

Three proved private equality lemmas identify the existing cochain and localization
instance aliases. Two private lemmas first establish the supported comparison for generic
coefficients; their specialization to ModuleCat uses the existing named comparison, avoiding
reduction of concrete derived tensor objects. A private meta elaboration helper, declared
before the noncomputable section, passes the dictionaries already present in that map's
type verbatim to the proved generic localization theorem. It checks the expected shape and
requires the flatness hypothesis. Lean's kernel checks the resulting ordinary proof term;
the helper adds no axiom, public declaration, data construction or unchecked proof rule.

The private helper declarations and the final theorem use declaration-scoped
`set_option backward.isDefEq.respectTransparency.types true in` and
`set_option backward.isDefEq.respectTransparency true in`. Small proof steps that need
an explicit semireducible alias expanded use the corresponding `false` settings locally.
No heartbeat, recursion, or wall-time limit is raised. The repair after return
C-daa39 replaces the final instance search in each product-generator epicness proof
with explicit `epi_comp'` applications to the already established epimorphisms,
using `IsIso.epi_of_iso` for the two known isomorphisms. This proof-only change avoids repeated unfolding during instance search. Four private instances obtain
preservation of epimorphisms and small colimits directly from the recorded inverse-image
adjunctions; they add no mathematical assumption.

The public theorem signature is unchanged (the text under `## Old`). It is restated after
`end AlgebraicGeometry.Scheme` in a reopened `namespace AlgebraicGeometry.Scheme` and
proved by `supportQuotient_product_aux A k f g i j`.

The repair also keeps the existing constant-sheaf construction folded after the eight
public definitions:

```lean
attribute [local irreducible] constantSheaf
```

Only `etale_constantExteriorTensor_isIso` and
`proEtale_constantExteriorTensor_isIso` receive the declaration-scoped prefix
`attribute [local semireducible] constantSheaf in`. Their original proofs unfold the
constant tensor construction; other arguments use the named constant-sheaf API.
All these attributes are local, and no public definition body or attribute changes.
This removes repeated expansion of sheafification during the proof and axiom check.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SupportQuotientProduct --uses
AlgebraicGeometry.Scheme.supportQuotient_product
AlgebraicGeometry.Scheme.etaleSupportQuotientDerivedComparison` lists no downstream
Lean modules and only this module as a textual user. DAG parents are retained; this is
not a withdrawal. Their propositions are unchanged because the existing public definitions
and elaborated theorem statement are unchanged. No consumer adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | X2 | Prove the existing theorem; retain its public interface. |

## Status

landed 20261021T140949-L-2782083 2026-10-21 (merge of deliver/X2/Sheaf.AlgebraicGeometry.SupportQuotientProduct)
