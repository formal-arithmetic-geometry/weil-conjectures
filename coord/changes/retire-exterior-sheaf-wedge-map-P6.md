# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_wedgeMap_exists

## Reason

Retirement item in coord/retire-items.tsv under the human's 2026-10-20 hand-off.
The Sheaf module duplicates the upstream wedge theorem, but its exteriorSheaf construction
is not definitionally equal to the upstream exteriorPower. Preserve the two direct consumer
signatures by explicit comparison isomorphisms, then withdraw the duplicate module.
No source-library file, target statement or existing definition is changed.

## Old

Duplicate module: Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists.

```lean
theorem exteriorSheaf_wedgeMap_exists {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorSheaf A r ⊗ exteriorSheaf B s ⟶ exteriorSheaf B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (exteriorSheafSection A r U a) (exteriorSheafSection B s U c)) =
          exteriorSheafSection B t U
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i))
```

## New

Use the existing, unchanged theorem in
WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists:

```lean
theorem exteriorSheaf_wedgeMap_exists {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r s t : ℕ) (ht : t = r + s) :
    ∃ ψ : exteriorPower A r ⊗ exteriorPower B s ⟶ exteriorPower B t,
      ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
        (c : Fin s → B.val.obj (op U)),
        ψ.val.app (op U)
          (tmulSection (wedge (M := A) (r := r) (U := U) a) (wedge (M := B) (r := s) (U := U) c)) =
          wedge (M := B) (r := t) (U := U)
            (fun i ↦ Fin.append (fun j ↦ f.val.app (op U) (a j)) c (Fin.cast ht i))
```

The two consumers import this upstream module privately. Each constructs a private
presheaf isomorphism with identity components: the exterior restrictions agree by
exteriorSheafRestriction_existsUnique and the upstream map_ιMulti formula. Applying the
sheafification functor gives the sheaf isomorphism. Unit naturality proves preservation
of pure wedges; the inverse formula follows from hom_inv_id. Conjugating the upstream
morphism by these isomorphisms proves the legacy formula without changing either
consumer's public declaration. All helpers are fully proved and private, with no global
instances or attributes. The item module is withdrawn through deleted.txt; the delivery
tool represents withdrawal as an empty module until the queue prunes it.

## Users

The downstream.py scan found the following nine transitive consumers. The only two direct
users of exteriorSheaf_wedgeMap_exists are adapted in this packet; both were unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel | unclaimed | Proof import switched; private wedge-preserving comparisons; public signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt | unclaimed | Proof import switched; private wedge-preserving comparisons; public signature unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | No edit: imports the unchanged public interface of the adapted consumers. |

The retired module itself is held by P6. Its node now points at the upstream declaration.
No target uses a changed definition, since no definition changes in this packet.

## Status

landed 20261020T164814-L-3967578 2026-10-20 (merge of deliver/P6/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists)
