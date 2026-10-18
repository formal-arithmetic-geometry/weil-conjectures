# IsLocalRing.depth_eq_projectiveDimension_add_depth

## Reason

The intermediate theorem used an arbitrary module universe `v`, but its finite
free resolution theorem and the comparison with ordinary projective dimension
require the module universe to contain the ring universe `u`. Mathlib likewise
requires `Small.{v} R` when identifying categorical and ordinary projectivity.
Use `Type (max u v)` for the module, matching the existing resolution APIs.
This is a size-interface repair, with unchanged mathematical assumptions and
conclusion. It changes no target signature or definition used by a target.

## Old

```lean
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    depth (R := R) R =
      (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M
```

## New

```lean
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    depth (R := R) R =
      (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.AuslanderBuchsbaum | Q2 | Proof and module universe repaired. |
| Sheaf.RingTheory.UniformPerfectQuotientBound | unclaimed | Only downstream importer; its modules and rings are all in universe u, so no adaptation is necessary. Its current proved theorem applies this declaration to a module N in Type u over R in Type u; the same-universe application is separately compiled unchanged. The full current consumer compile awaits the unrelated missing BoundedFiniteProjectiveResolution.olean in the published build. |

The downstream script found one downstream module. Source search found one
application, in UniformPerfectQuotientBound at its local-ring depth bound. The DAG citer
lem-weil-pbc-uniform-perfect-quotient-bound also uses a common universe.

## Status

landed 20261018T091410-L-3257941 2026-10-18 (merge of deliver/Q2/Sheaf.RingTheory.AuslanderBuchsbaum)
