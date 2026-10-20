# AlgebraicGeometry.Etale.SupportedDerivedScalarUnit

## Reason

The original universal property expands concrete derived single and restriction functors
inside every test Hom type. The item repeatedly exceeds the 60-second compile limit when
using this expanded predicate. Kernel profiling of an equivalent private wrapper also
exhausted 15,000 heartbeats. Keep those functors abstract in the predicate and give the
definition a proved adjunction/transport API instead of expanding them in each proof.
This is a repair of the existing definition's implementation and API; the original item
remains one module and its scalar maps, normalizations and unit-square proof remain there.

`OrdinarySupportedKummerScalar` is unclaimed. All original signatures, attributes and
public imports stay unchanged. Unfold `CategoryTheory.IsScalarExtensionUnit` in the new
body below and reassociate by `Category.assoc`: the result is the old formula. Hence the definition
is neither stronger nor weaker and no coefficient flatness or boundedness is introduced.
The generic definition and its proved transport API live alongside the existing predicate. There are no new holes. Target semantic review is reopened by this definition
body change; the reviewer can check its meaning by the indicated unfolding and associativity.

## Old

```lean
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  ∀ K : DerivedCategoryModule S T,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0).inv.app
          G ≫
          (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map f)
```

## New

```lean
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  IsScalarExtensionUnit
    (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) 0)
    (DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S)) 0)
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor 0) η
```

The abstract predicate is:

```lean
@[irreducible] def IsScalarExtensionUnit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {U : D ⥤ C} {V : D' ⥤ C'} (L : C ⥤ C') (M : D ⥤ D')
    (e : M ⋙ V ≅ U ⋙ L) {F : C} {G : D} (η : F ⟶ U.obj G) : Prop :=
  ∀ K : D', Function.Bijective
    (fun f : M.obj G ⟶ K ↦ (L.map η ≫ e.inv.app G) ≫ V.map f)
```

The coefficient-unit composite is grouped before composing with the test map.
Associativity proves equivalence with the original right-associated formula. The new
proved transport API is
`CategoryTheory.isScalarExtensionUnit_transport`
(node `lem-asd-scalar-unit-transport-api`). The existing definition node's Lean attachment
lists the generic predicate; its construction step records this
specialization. The invertible-adjunct argument itself stays private in the item module,
using exactly the named derived source and target of the existing comparison.

## Users

`tools/downstream.py --uses SupportedDerivedScalarUnit` lists the first two rows.
The same command with `SupportedKummerScalar` lists the remaining named consumers and
this definition module. All five were read: three downstream uses are in signatures or
unchanged definitions, while the item uses the new proved API. No statement changes
meaning, because the predicate is equivalent after unfolding its generic helper and applying `Category.assoc`. No other group's source is edited. The three unchanged downstream consumers were
compiled against the repaired definition and proved item: all passed without adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Generic predicate and proved API added; original scalar-unit body becomes their specialization. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | D3 | Proof uses the API instead of expanding derived test-Hom types. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Unchanged signature; scalar relation retains exactly its prior meaning. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | B3 | Unchanged signature and source; scalar relation retains exactly its prior meaning. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Unchanged compatibility definition; scalar relation retains exactly its prior meaning. |

## Status

landed 20261020T221115-L-4145063 2026-10-20 (merge of deliver/D3/Sheaf.AlgebraicGeometry.SupportedKummerScalarSource)
