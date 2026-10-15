# Proper direct image of bounded constructible complexes

## Reason

The remaining projective-space adic input needs finite-coefficient proper finiteness.
All three modules below are unclaimed in the supplied repository. The launcher's unclaimed
module rule permits their proof-only changes; no held module is adapted.

## Old

The two bounded-complex declarations had proof `sorry`, with signatures:

```lean
theorem boundedConstructible_rightDerivedLowerStar_of_isProper {Y S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K)
```

```lean
theorem isBoundedConstructible_rightDerivedLowerStar_of_proper
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (N : ℕ)
    {k : Type u} [Field k] {Y S : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (b : Y ⟶ S) [IsProper b] (hb : b ≫ aS = aY)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ Y) (hK : DerivedCategory.isBoundedConstructible Λ Y K) :
    DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) b).obj K)
```

## New

The same signatures are proved:

```lean
theorem boundedConstructible_rightDerivedLowerStar_of_isProper {Y S : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS] (b : Y ⟶ S) [IsProper b]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y K) :
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) S
      ((R((b)_*[ModuleCat.{u + 1} Λ])).obj K)
```

```lean
theorem isBoundedConstructible_rightDerivedLowerStar_of_proper
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (N : ℕ)
    {k : Type u} [Field k] {Y S : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (b : Y ⟶ S) [IsProper b] (hb : b ≫ aS = aY)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ Y) (hK : DerivedCategory.isBoundedConstructible Λ Y K) :
    DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) b).obj K)
```

The source theorem combines finite torsion cohomological dimension, proper
constructibility and the existing finite-truncation devissage. The exact DAG theorem
converts constructibility and boundedness predicates, descends the invertible exponent
to the field on a nonempty target, and treats an empty target directly. All added imports
are private. The source module's proper constructibility/vanishing and geometric comparison holes
are now proved too, by torsion proper base change, geometric-point detection and
the 2d bound. Their signatures are unchanged. The exact DAG
module drops the now-unused spectral-sequence proof imports, listed fully in report.md.
The node's statement, Lean attachment and the unit's realizations are unchanged.

The exact project `properCase_constructible_and_vanishing` is also proved in
`Sheaf.AlgebraicGeometry.ProperCaseConstructibility`, with its existing signature and
public imports unchanged. Its proof treats empty targets, converts constructibility,
then uses the source proper constructibility, proper torsion base change and geometric
2d vanishing. The node keeps its original Lean attachment and statement; its proof
requirements drop the unneeded finite-fibre comparison route. This module's replaced
private proof imports are listed completely in report.md.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | three proofs closed; interfaces unchanged |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | one proof closed; proof imports replaced |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | constructibility and uniform vanishing proved; original signature unchanged |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | new C3 module | planned finite-level finiteness inputs proved |

No caller requires adaptation: every existing signature and public import is identical.
No statement or definition used by a target changes. This record concerns proofs only.

## Status

landed 20261015T195758-L-1299658 2026-10-15 (merge of deliver/C3/WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar)
