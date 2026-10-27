# AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso

## Reason

The rework item is already restored by D3 in the current source and has zero holes.
Its coefficient comparison nevertheless imports SmoothProperPrimeSpecialization only
for the name strictLocalSpecialization. That unnecessarily brings the smooth-proper
local-acyclicity argument into a comparison valid for all module sheaves.
Use the existing canonical etaleStalkSpecialization definition instead. These maps
are definitionally equal: a separate Lean consumer verifies their equality by rfl.
This is dependency pruning, not another restoration or a claim to close a hole.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization
```

```lean
theorem Etale.bijective_moduleSpecialization_of_abelianIso
    {S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (Etale.moduleAbelianForget R S).obj M ≅ A)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme s)
    (h : IsIso (Etale.strictLocalSpecialization s t A)) :
    Function.Bijective (Scheme.etaleModuleStalkSpecialization s t M)
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
```

```lean
theorem Etale.bijective_moduleSpecialization_of_abelianIso
    {S : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R))
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (Etale.moduleAbelianForget R S).obj M ≅ A)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme s)
    (h : IsIso (Etale.etaleStalkSpecialization s t A)) :
    Function.Bijective (Scheme.etaleModuleStalkSpecialization s t M)
```

The private germ lemma and its proof use the canonical name throughout. The
inverse-image germ facts previously reached through the broad public import are
now imported privately. The germ construction, universes, binders, conclusion and
hypothesis are unchanged up to definitional equality. Neither specialization
construction nor any target declaration or source-library declaration changes.
The node replaces the smooth-proper proof dependency by the canonical definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | A2 | Canonical map name; smaller import dependency. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed, quarantined | Existing application receives a definitionally identical hypothesis; no adaptation. |

The source downstream scan finds no live importer; the declaration-use scan lists
only the item itself. Searching quarantine finds the direct parent above. Its
application at lines 212-214 passes an IsIso strictLocalSpecialization proof,
which the consumer probe accepts directly with no rewriting. That parent imports
SmoothProperPrimeSpecialization itself, so the removed re-export does not deprive
it of the smooth-proper theorem. No consumer source or node is withdrawn, and the
unit route still uses the smooth-proper theorem in the parent where it is needed.
No target meaning is affected and no forced consumer adaptation is needed.

## Status

landed 20261022T043922-L-1093744 2026-10-22 (merge of deliver/A2/Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso)
