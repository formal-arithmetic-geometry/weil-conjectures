# exists_finite_adjoin_with_jacobson_power

## Reason

Retire the unused Sheaf copy in favour of the proved upstream declaration, as requested
by the human's 2026-10-20 retirement instruction in
`coord/changes/retire-sheaf-twins-20261020.md` and row
`retire:Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux` of
`coord/retire-items.tsv`. No current Lean module imports the Sheaf copy. The upstream
theorem drops only the unused dimension-one hypothesis; its conclusion is identical.
This also implements step 8d of the worker brief: withdraw an item no parent uses.

## Old

The retired Sheaf module declares:

```lean
theorem exists_finite_adjoin_with_jacobson_power
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]
    [Finite (MaximalSpectrum (integralClosure B K))]
    (x y : integralClosure B K)
    (hx : x ∈ Ideal.jacobson (⊥ : Ideal (integralClosure B K))) :
    ∃ A : Subalgebra B K, Module.Finite B A ∧ IsFractionRing A K ∧
      (x : K) ∈ A ∧ (y : K) ∈ A ∧
      ∃ m : ℕ, 0 < m ∧ ∃ a : A,
        (a : K) = (x : K) ^ m ∧
        a ∈ Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))
```

## New

The Sheaf module is withdrawn using `deleted.txt`; the delivery tool leaves an empty
module with no declarations. The DAG node points to the existing, unchanged declaration
in `WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPowerAux`:

```lean
theorem exists_finite_adjoin_with_jacobson_power
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)]
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]
    [Finite (MaximalSpectrum (integralClosure B K))]
    (x y : integralClosure B K)
    (hx : x ∈ Ideal.jacobson (⊥ : Ideal (integralClosure B K))) :
    ∃ A : Subalgebra B K, Module.Finite B A ∧ IsFractionRing A K ∧
      (x : K) ∈ A ∧ (y : K) ∈ A ∧
      ∃ m : ℕ, 0 < m ∧ ∃ a : A,
        (a : K) = (x : K) ^ m ∧
        a ∈ Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))
```

No upstream source, signature, attribute, import, definition, or target is changed.
The node's mathematical statement and proof dependencies are unchanged. Correct the
proof-step wording from a surjective ring map to a surjective prime-spectrum comap.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux
--uses exists_finite_adjoin_with_jacobson_power` reports zero downstream modules;
its sole named use is the declaration in the retired module itself. A repository-wide
`rg` confirms no imports of the Sheaf copy. The historical consumer named in the
retirement table, `Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPower`, is already
absent from the live source tree.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux | G2 | Withdrawn unused duplicate. |

The unchanged upstream consumer
`WeilConjectures.AlgebraicGeometry.SemilocalDimOneConductorPower` already imports and
calls the upstream theorem without the dropped dimension argument. No forced adaptation
or target review is needed.

Validation: compile an exact copy of the upstream module through `lcompile.py`, then
compile the complete old signature as a private scratch theorem with proof
`exact exists_finite_adjoin_with_jacobson_power B K x y hx`. Both the upstream theorem
and its old-signature specialization have axioms exactly `propext`, `Classical.choice`,
and `Quot.sound`. The two files compile in 2.5 and 1.6 seconds respectively.

## Status

landed 20261020T132002-L-1399262 2026-10-20 (merge of deliver/G2/Sheaf.AlgebraicGeometry.SemilocalDimOneConductorPowerAux)
