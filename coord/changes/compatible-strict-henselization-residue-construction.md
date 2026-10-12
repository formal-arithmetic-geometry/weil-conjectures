# AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_square

## Reason

Repair returned delivery X-dfe97: its strengthened CoreData was a duplicate of
three full-model existence statements. Remove that override and use the existing
CoreData unchanged. Repair the original false arbitrary-map residue claim with
existence of a compatible map between fixed models. The new lifting obligation
is strictly the map-construction step, and does not repeat existence of rings,
affine models or universal homeomorphisms. The item retains its original core
signature and proof. No CoreData interface change is delivered.

## Old

```lean
theorem Etale.compatibleStrictHenselization_residue_square {S T : Scheme.{u}} {g : T ⟶ S} {k k' Ω A B : Type u} [Field k] [Field k'] [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T} (ι : Spec (.of k') ⟶ Spec (.of k)) (φ : A →+* B) (hφ : IsLocalHom φ) (eA : Spec (.of A) ≅ strictHenselizationScheme s) (eB : Spec (.of B) ≅ strictHenselizationScheme t) (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA
```

## New

```lean
theorem Etale.compatibleStrictHenselization_residue_square {S T : Scheme.{u}} {g : T ⟶ S} {k k' Ω A B : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Field Ω] [IsAlgClosed Ω] [CommRing A] [CommRing B] [HenselianLocalRing A] [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField A)] [IsSepClosed (IsLocalRing.ResidueField B)] (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k)) (hι : ι ≫ σ = τ ≫ g) (ν : Spec (.of Ω) ⟶ Spec (.of k')) (eA : Spec (.of A) ≅ strictHenselizationScheme (ν ≫ ι ≫ σ)) (eB : Spec (.of B) ≅ strictHenselizationScheme (ν ≫ τ)) (ρA : Spec (.of k) ⟶ Spec (.of (IsLocalRing.ResidueField A))) (ρB : Spec (.of k') ⟶ Spec (.of (IsLocalRing.ResidueField B))) (hρA : ρA ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = σ) (hρB : ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) = τ) : ∃ (φ : A →+* B) (hφ : IsLocalHom φ), letI := hφ Spec.map (CommRingCat.ofHom φ) ≫ eA.hom ≫ strictHenselizationStructuralMap (ν ≫ ι ≫ σ) = eB.hom ≫ strictHenselizationStructuralMap (ν ≫ τ) ≫ g ∧ ρB ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map φ)) = ι ≫ ρA
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | G3 | Owned residue-square statement now chooses a compatible local map for fixed models. The core declaration stays identical. |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues | unclaimed | Forced proof-only adaptation: install the obtained ring instances, choose a compatible local map with its structural and residue squares, and repack. All signatures, imports and visibility stay identical. |

These are the only textual declaration users found by downstream.py --uses.
The adapted caller changes only the block following its existing obtain.
All further users import the unchanged caller interface. No target or definition
is changed. CoreData is neither changed nor adapted.

## Repair of X-1f91b

The new helper now takes the residue embedding r and its spectral square hres as
inputs. The main item constructs them independently using residue-image containment,
field-map injectivity and full faithfulness of Spec. The helper returns only a ring
lift with its ring reduction and structural equalities. Its proof dependencies now
cite and import EtaleLocalRingTriples, StrictHenselizationTriples and
MapIntoHenselianColimit. No existing additional module interface is changed by this
repair, and no additional caller adaptation is needed.

## Status

landed 20261012T154243-L-2434686 2026-10-12 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore)
