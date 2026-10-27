# Canonical tensor instances used by the residue statement

## Reason

The original public theorem statement needs the canonical closed tensor structure,
symmetry and flat-resolution proof for module objects over a pulled condensed ring.
With transparency checks enabled, inference does not identify all presentations of
the pulled commutativity proof automatically. Private local wrappers solve the
private proof statements, but cannot be used while elaborating the public signature.

## Old

These three helper declarations did not exist. The existing module-object tensor,
symmetry and flat-resolution instances remain unchanged.

## New

The following are proved public declarations, registered only as local instances:

```lean
/-- The canonical closed tensor structure, with the pulled commutativity proof explicit.
Source: the module-object tensor structure (blueprint: lem-sfb-integral-residue-proper-formulas). -/
noncomputable local instance integralResidueModulesClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    MonoidalClosed (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ h

/-- The canonical symmetry, using the same pulled commutative ring object.
Source: the module-object tensor structure (blueprint: lem-sfb-integral-residue-proper-formulas). -/
noncomputable local instance integralResidueModulesSymmetric
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    SymmetricCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ h

/-- The standard functorial flat-resolution instance for these module objects.
Source: the module-object flat resolution (blueprint: lem-sfb-integral-residue-proper-formulas). -/
local instance integralResidueModulesFlat
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)) := by
  have h : IsCommMonObj (condensedRingObj Λ T) := isCommMonObj_condensedRingObj Λ T
  exact @Mod.hasFunctorialFlatResolution _ _ _ _ _ _ _ _ _ h inferInstance
```

Their data is definitionally the existing canonical data: no new choice, hypothesis
or replacement tensor structure is introduced. Expanded module-object types in
these signatures avoid exposing the private scalar-interface alias. The existing
theorem statement and all existing definitions stay unchanged. The original residue
DAG node records these helper declarations.

## Users

The names are new and have no earlier users in the shared source. Their local
instance registrations are not exported to importers. No consumer requires an
adaptation; the original public theorem keeps its statement and canonical maps.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueProperFormulas | P6 | Use the canonical instances in the statement and proof. |

## Status

landed 20261026T023730-L-597739 2026-10-26 (merge of deliver/P6/Sheaf.Paper.IntegralResidueProperFormulas)
