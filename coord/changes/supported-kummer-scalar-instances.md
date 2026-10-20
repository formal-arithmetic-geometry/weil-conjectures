# AlgebraicGeometry.Etale.SupportedKummerScalar

## Reason

The interface's Ext arguments stored global sheafification/Grothendieck instance expressions,
while the recorded unbounded derived category stores opaque instance proofs. Comparing them
unfolds the sheafification construction in the kernel. In isolated original-target clauses,
the boundary specification cost about ten seconds, its uniqueness clause eight seconds,
and the scalar clause exceeded twelve thousand kernel heartbeats. The full target statement
alone required twenty-six seconds, and the final complete proof exceeded the file limit.

Select the existing derived-category instance proofs locally when elaborating this definition.
The written signature and body are identical. Their implicit instance arguments now coincide
with the derived interfaces. All differing instance arguments are proofs of the same properties;
proof irrelevance gives the original construction and predicate. No mathematical statement or
normalization changes. This is a repair of the stored instance expressions, not a new predicate.
The local selections export no instances. The auxiliary names have no stable source API;
source refactors may require updating these selections. The auxLemma linter is disabled only
on the attribute command that deliberately names these existing source declarations.

## Old

```lean
@[irreducible]
def SupportedKummerScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (cR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T N R hR) 2)
    (cS : Ext ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      (Scheme.finiteEtaleTateLine T N S hS) 2) : Prop :=
  ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N S hS)),
    (∀ (U : D.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) ∧
    (∀ (U : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj U),
      θ.hom.app U (Scheme.finiteEtaleTateOneGenerator R N T hR U r z) =
        Scheme.finiteEtaleTateOneGenerator S N T hS U (φ r) z) ∧
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N R hR)
      (Scheme.finiteEtaleTateLine T N S hS) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      cR.comp (Ext.mk₀ θ) (add_zero 2)
```

## New

```lean
section

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

@[irreducible]
def SupportedKummerScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (cR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T N R hR) 2)
    (cS : Ext ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      (Scheme.finiteEtaleTateLine T N S hS) 2) : Prop :=
  ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N S hS)),
    (∀ (U : D.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) ∧
    (∀ (U : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj U),
      θ.hom.app U (Scheme.finiteEtaleTateOneGenerator R N T hR U r z) =
        Scheme.finiteEtaleTateOneGenerator S N T hS U (φ r) z) ∧
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N R hR)
      (Scheme.finiteEtaleTateLine T N S hS) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      cR.comp (Ext.mk₀ θ) (add_zero 2)

end
```

## Users

The definition module is unclaimed. Direct declaration users were enumerated with
`tools/downstream.py --uses SupportedKummerScalar`. The table includes the new consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | B3 | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Same predicate; original consumer checked against the repair. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | B3, new | Uses the normalized scalar interface. |

The existing definitions and targets using them require independent definition review.
Original consumer checks and any necessary forced adaptations are recorded in report.md.

## Status

landed 20261020T211631-L-3481036 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer)
