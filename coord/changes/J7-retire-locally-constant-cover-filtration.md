# AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf

## Reason

Retire the redundant `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration`, as assigned
in `coord/retire-items.tsv`. The nominal twin lacks the `_sheaf` theorem, but the exact
same declaration already exists in
`WeilConjectures.ConstructibleSheaf.LocallyConstantCoverFiltrationExtension`.
The two signatures are byte-for-byte identical, and their proofs follow the same route.

## Old

Declared in `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration`:

```lean
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf
    {U : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      (∃ (n : ℕ)
        (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
        Nonempty (W n ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
        ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
          (constantSheaf V.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))
```

## New

Use the existing declaration from
`WeilConjectures.ConstructibleSheaf.LocallyConstantCoverFiltrationExtension`:

```lean
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf
    {U : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      (∃ (n : ℕ)
        (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
        Nonempty (W n ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
        ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
          (constantSheaf V.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))
```

The redundant Sheaf module is withdrawn through `deleted.txt`; the landing tool leaves
an empty module. Redirect the existing node's Lean attachment to the source module.
Its statement, proof, proof dependencies and declaration name are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | J7 | Redundant declaration withdrawn. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged; not adapted | Sole DAG parent already imports the source Extension and uses its exact theorem; compiles unchanged. |

`tools/downstream.py ... --uses ...` finds no downstream Lean modules of the Sheaf copy;
only the copy itself mentions the declaration in that import closure. There are no
imports to migrate. The sole dependency parent is
`lemma-weil-pbc-curve-locally-constant-reduction`; its unchanged node id reference now
resolves to the source declaration via the updated attachment. No target meaning changes.
All source-library files, declarations and imports are preserved.

## Status

landed 20261020T221226-L-4160913 2026-10-20 (merge of deliver/J7/Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration)
