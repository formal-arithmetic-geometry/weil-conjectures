# AlgebraicGeometry.affinePushforwardComparison_factorization

## Reason

The assigned wrapper already re-exports the complete adopted upstream theorem.
That canonical theorem and the complete upstream identity theorem using it remain
verbatim. Record the canonical upstream identity proof as the identity node's
provider; that complete proof imports the canonical factorization directly. The Sheaf
factorization wrapper is then unused by the parent's realized proof. Withdraw only this compatibility path and retain
its node and every mathematical dependency.

The separately claimed Sheaf identity source module and its quarantine
archive are not edited or withdrawn. Only the parent node's Lean attachment and
proof-origin note change, to record the existing complete replacement argument.
Its proof steps and all dependency edges stay intact. The canonical signature is
identical to the archived intended statement, with explicit sheaf universes.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization

/-! # Naturality of the ordinary affine comparison on cohomology

The factorization theorem is provided by the adopted upstream module. This import
preserves the existing module path while using its proved declaration with explicit
sheaf universes.

Source: Stacks Project, Tag 0AVW; Mathlib homology comparison naturality.
(blueprint: lem-pc-affine-pushforward-comparison-factorization). -/

@[expose] public section
```

The parent node's previous Lean attachment pointed to
`Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity`, whose source is
preserved in quarantine. Its archived signature (unchanged there) is:

```lean
theorem exists_affinePushforwardCohomologyEdge_identity
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩
```

Its archived ambient instance left the sheaf universe implicit. The node now
points to the canonical proof whose explicit instance and signature are below;
no source module signature is edited by this delivery.

## New

Withdraw the compatibility module through deleted.txt. The delivery tool writes:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The node remains attached to the existing theorem
AlgebraicGeometry.affinePushforwardComparison_factorization in
WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization.
Its signature, proof, imports and axioms are unchanged. The canonical identity
proof uses this theorem directly, including the same final theorem application.
The identity node's new canonical signature is:

```lean
theorem exists_affinePushforwardCohomologyEdge_identity
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat A) ℤ)
      (hK : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C))),
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map
            (𝟙 _)) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C _ (Iso.refl _) i).hom) ≫
          α.app ⟨_, hK⟩
```

Its ambient derived-category instance fixes SheafOfModules.{u}, as does the
canonical comparison-coordinate definition. Comparing the entire archived and
upstream identity files shows only a copyright change, the canonical factorization
import and six explicit sheaf-universe annotations; their three mathematical proof
steps agree exactly. Both canonical proofs use only the three allowed axioms.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization | G4 | Withdraw the unused re-export; no mathematical declaration is removed. |
| Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | P1 | Source module and quarantine archive untouched. Its node records the existing canonical upstream proof; all mathematical dependencies remain. |
| WeilConjectures.Algebra.Homology.AffinePushforwardComparisonFactorization | unclaimed | Existing canonical provider remains verbatim. |
| WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity | unclaimed | Existing canonical consumer remains verbatim and imports canonical factorization directly. |

The direct DAG parent of the factorization node is the identity node. Its
mathematical factorization dependency is retained and its Lean attachment now names
the existing complete upstream proof. No DAG node depends on the identity node.
Searches of the active library find no importer of the withdrawn wrapper. The only
archived importer is the separately claimed identity source, which is preserved
verbatim; the node is realized by the complete canonical upstream argument instead.
This is an actual parent replacement proof and corresponding provider update in
the same packet, rather than an inference from zero current importers alone. The unit's realized lists
contain neither of these nodes, and no unit route is changed.

## Status

landed 20261020T160107-L-3325645 2026-10-20 (merge of deliver/G4/Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization)
