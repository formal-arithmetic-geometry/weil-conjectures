# AlgebraicGeometry.Scheme.exists_finiteGalois_germ_representative

## Reason

Retire the local copy in favor of the adopted source module, as requested by
coord/retire-items.tsv. The local copy is already proved (zero holes). The upstream
statement is restricted to coefficients in Type (max (u+1) v), whereas the local
consumer uses Type (max u v). A direct import rewrite does not supply that instance
of the theorem. Preserve the consumer's statement by applying the upstream theorem
to its ULift sheaf, and transfer the resulting section and germ equality back using
Mathlib's presheafFiberCompIso compatibility. ULift preserves the limits needed for
the sheaf condition and the filtered colimits defining the stalk.

## Old

The retired Sheaf module declared:

```lean
theorem exists_finiteGalois_germ_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max u v)))
    (L : IntermediateField K Ks) [FiniteDimensional K L]
    (m : (pointSmallEtale s).sheafFiber.obj F) :
    ∃ E : FiniteGaloisIntermediateField K Ks,
      L ≤ E.toIntermediateField ∧
      ∃ y : (pointSmallEtale s).fiber.obj (etaleSpec K E),
        y.left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)) ∧
        ∃ z : F.obj.obj (op (etaleSpec K E)),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z = m
```

Its sole consumer imported
Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative and applied this theorem
directly to F and m.

## New

The upstream module, unchanged by this delivery, declares:

```lean
theorem exists_finiteGalois_germ_representative
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (L : IntermediateField K Ks) [FiniteDimensional K L]
    (m : (pointSmallEtale s).sheafFiber.obj F) :
    ∃ E : FiniteGaloisIntermediateField K Ks,
      L ≤ E.toIntermediateField ∧
      ∃ y : (pointSmallEtale s).fiber.obj (etaleSpec K E),
        y.left = Spec.map
          (CommRingCat.ofHom ((algebraMap Ks Ω).comp E.toIntermediateField.subtype)) ∧
        ∃ z : F.obj.obj (op (etaleSpec K E)),
          (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z = m
```

The local copy is withdrawn, and its DAG attachment points to that upstream module.
The consumer privately imports the upstream module and
Mathlib.CategoryTheory.Limits.Preserves.Ulift. Its theorem signature is byte-identical.
In its proof, lift F and m, apply the upstream theorem, and lower the representative;
the germ equality follows from Mathlib's comparison of stalks and ULift. No target
statement or definition changes. No new declarations or axioms are introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative | T2 | Withdraw the duplicate local module; zero holes before and after. |
| Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative | unclaimed | Replace the private import and adapt the theorem application by ULift; every signature and public import stays identical. |

The user table follows tools/downstream.py with
--uses exists_finiteGalois_germ_representative. There are 41 transitive downstream
modules, but this is the only consumer that mentions the retired declaration and
the only direct importer. Other modules retain the consumer's unchanged interface.

## Status

landed 20261020T135427-L-1822367 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative)
