# CategoryTheory.tor_kernel_boundary_naturality_of

## Reason

Repair of reviewer X-75668 (E2 / point 4; G1). An arbitrary exact boundary
family need not be natural. Over Z with M=Z/3, q=mod 3, q′=-q, a=c=-id,
b=id, identical nonzero exact boundary isomorphisms would require 1=-1.
The old hypothesis supplies no comparison with canonical connecting maps.
Replace it with naturality of the explicitly constructed torKernelBoundary.
The construction uses Mathlib's projective resolution and a projectivity lift,
a kernel restriction, tensoring, and a cokernel descent. No data are chosen
from a theorem left unproved. Its naturality is proved completely. Its
exactness alone is isolated as a smaller new theorem left sorry.

## Old

```lean
theorem tor_kernel_boundary_naturality_of
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
      Function.Surjective q →
        (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
          (LinearMap.ker q ⊗[R] M)) :
    (∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q),
      Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom (δ F N q hq) ∧
      Function.Exact (δ F N q hq) ((LinearMap.ker q).subtype.rTensor M)) →
    ∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
        (hq : Function.Surjective q) (hq' : Function.Surjective q')
        (a : F →ₗ[R] F') (b : N →ₗ[R] N')
        (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
      q'.comp a = b.comp q →
      (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
      ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
        δ F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom b)).app M).hom t) =
        c.rTensor M (δ F N q hq t)
```

## New

```lean
theorem tor_kernel_boundary_naturality_of
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
        (hq : Function.Surjective q) (hq' : Function.Surjective q')
        (a : F →ₗ[R] F') (b : N →ₗ[R] N')
        (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
      q'.comp a = b.comp q →
      (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
      ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
        torKernelBoundary M F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom b)).app M).hom t) =
        c.rTensor M (torKernelBoundary M F N q hq t)
```

The new signature refers to `CategoryTheory.torKernelBoundary`, defined in
`Sheaf.RingTheory.TorKernelBoundaryConstruction`. No existing definition changes.
The new exactness obligation is
`CategoryTheory.tor_kernel_boundary_construction_exact` in
`Sheaf.RingTheory.TorKernelBoundaryConstructionExact`.

## Users

The full-library textual search (`tools/downstream.py` with `--uses`) found
exactly these two modules mentioning the changed declaration:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.TorKernelBoundaryNaturalityOf | F3 | Replace false signature and prove naturality of constructed maps. |
| Sheaf.RingTheory.TorKernelBoundaryNaturality | unclaimed | Forced proof adaptation: use torKernelBoundary as witness, its fixed-map exactness theorem, and its proved naturality. Signature and visibility identical. |

The original caller fails against the changed interface at its final application:
it supplies δ and hδ where the new theorem expects the presentation modules.
The change replaces only its proof-dependency imports and final proof lines.
The original final application is `tor_kernel_boundary_naturality_of R M δ hδ`;
the replacement uses `tor_kernel_boundary_naturality_of R M` with the constructed
family. The preceding choice of arbitrary exact maps is necessarily replaced too.
All transitive users use the caller's unchanged existential API, including
`Sheaf.RingTheory.MinimalPresentationTor`; they need no adaptations.
All five target statements and their definitions remain unchanged. No target's
meaning changes; this repairs a false auxiliary proof interface.

## Status

landed 20261012T212721-L-1130977 2026-10-12 (merge of deliver/F3/Sheaf.RingTheory.TorKernelBoundaryNaturalityOf)
