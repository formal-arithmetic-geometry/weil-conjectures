# finiteModel_constantScalarExtension_liftComparison

## Reason

STATEMENT-DISPUTED: the lift comparison and its core assert that ordinary termwise
scalar extension of every complex computes derived scalar extension. Take q : Z → Z/2
and P = (Z/2)[0]. Derived tensor has Tor_1^Z(Z/2,Z/2) = Z/2 in degree -1, whereas
ordinary tensor has no degree -1 cohomology. On a nonempty geometric pro-etale point,
constant realization retains this difference. The stated generic comparison theorem
compares two DERIVED extensions; its K-flat representative computation does not
justify the ordinary tensor intermediate on arbitrary P.

Withdraw both false intermediate declarations. Their only parent is replaced by a
complete proof of its unchanged, correct derived statement. No source-library module
or target statement changes. This is a route correction below the blueprint unit.

## Old

```lean
theorem finiteModel_constantScalarExtension_liftComparison
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P))) ≅
        DerivedCategory.Q.obj
          (finiteModelConstantComplex X C
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

```lean
theorem finiteModel_constantScalarExtension_core (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C] (q : B →+* C) [(koszulConstantFunctor X B).PreservesZeroMorphisms] [(koszulConstantFunctor X C).PreservesZeroMorphisms] (P : CochainComplex (ModuleCat.{t} B) ℤ) : Nonempty ((completedAdicDerivedChange X (adicConstantMap X q)).obj (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅ DerivedCategory.Q.obj (finiteModelConstantComplex X C (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P)))
```

The parent finiteModel_derivedScalarComparison imported
Sheaf.Paper.FiniteModelConstantScalarExtensionCore and
Sheaf.Paper.FiniteModelCoefficientTransport and composed their isomorphisms.

## New

Both declarations above are withdrawn (empty modules via deleted.txt); their DAG
nodes are retained, with lean set to null and a disputed-statement explanation in
proof. The parent theorem's signature and public imports stay verbatim.

The parent now uses a flat-term K-flat resolution in the small module universe.
The new proved CochainComplex.exists_coefficientLift_kFlat_resolution ensures that
its coefficient lift is also K-flat. Pure tensors identify lifted ordinary extension
with ordinary extension of the lift ON THIS RESOLUTION. The specified small universal
counit is invertible there. Exact restriction along rho inverse, the resolution
augmentation, and localization factors give the algebraic representative comparison.
The canonical sheaf scalar adjunctions agree by left-adjoint uniqueness; the proved
generic ConstantScalarRealization.comparisonIso then supplies the sheaf comparison.

The two removed imports are replaced by private proof imports of
Sheaf.Paper.BoundedConstructibleTower,
Sheaf.Paper.ConstantRealizationDerivedScalarExtension (import all, for its proved
private representative API), the new coefficient-lift resolution module,
WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit and
Mathlib.LinearAlgebra.TensorProduct.Tower.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison | J3 | Withdraw false assigned intermediate. |
| Sheaf.Paper.FiniteModelConstantScalarExtensionCore | unclaimed | Withdraw its false conclusion and adapt its only importer. |
| Sheaf.Paper.FiniteModelDerivedScalarComparison | unclaimed | Replace proof; same signature, hypotheses, universes, conclusion and public imports. |
| Sheaf.Paper.FiniteQuotientModelResidueComparison | unchanged | Only direct importer of the parent; compiled unchanged against the replacement (29.8 s). |
| Sheaf.Paper.FiniteModelConstantScalarExtensionDerivedChangeBridge | J1 | Unchanged; parent now constructs this comparison directly, so this route no longer depends on it. |
| Sheaf.Paper.FiniteModelCoefficientTransport | K1 | Unchanged; its disputed ordinary-tensor comparison is no longer used by this route. |

The direct-import and declaration-use searches find only Core importing the assigned
item and only DerivedScalarComparison importing Core. DAG citers agree: the assigned
node is used only by Core, and Core only by the adapted parent. Neither withdrawn
node realizes a unit statement or unit step. Quarantined sources add no importer.
The new module contains one proved theorem and adds no sorry.

## Status

landed 20261027T234015-L-4161097 2026-10-27 (merge of deliver/J3/Sheaf.Paper.FiniteModelConstantScalarExtensionLiftComparison)
