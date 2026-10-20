# AlgebraicGeometry.Scheme.Modules.locallyRankedExteriorComplex

## Reason

The human's retirement instruction in `coord/changes/retire-sheaf-twins-20261020.md`
requires replacing Sheaf copies by their canonical upstream twins. This item has no
sorry: it is the listed definition repair, not a theorem proof task.

The old rank term uses `exteriorSheaf`; the upstream rank term uses `exteriorPower`.
Both construct the sheafification of sectionwise exterior powers. The rank opens,
nonnegative degree convention, negative zero terms and zero differentials agree.
Retire the old construction and its only remaining consumer,
`Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`, whose proved upstream
replacement uses the canonical exterior power throughout. The consumer is unclaimed
and no Lean module imports it. No upstream file is edited.

## Old

`lean/Sheaf/AlgebraicGeometry/LocallyRankedExteriorComplex.lean`:

```lean
/-- The open and closed rank-n stratum. Source: Stacks, Tag 0BR0
(blueprint: def-sc-locally-ranked-exterior-complex). -/
def exteriorRankOpen {X : Scheme.{uE}} (r : LocallyConstant X ℕ) (n : ℕ) : X.Opens :=
  ⟨{x | r x = n}, r.isLocallyConstant.isOpen_fiber n⟩

/-- Degree n is the extension from the rank-n stratum of its top exterior power;
negative degrees are zero. Direct image along this clopen inclusion is extension by zero.
Source: Stacks, Tag 0BR0 (blueprint: def-sc-locally-ranked-exterior-complex). -/
noncomputable def locallyRankedExteriorTerm {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) (n : ℤ) : X.Modules :=
  if 0 ≤ n then
    (pushforward (exteriorRankOpen r n.toNat).ι).obj
      (exteriorSheaf
        ((restrictFunctor (exteriorRankOpen r n.toNat).ι).obj M) n.toNat)
  else 0

/-- The complex wedge^r M[-r]: degree n is supported on the rank-n stratum and every
 differential is zero. On a rank-n component it is precisely wedge^n M in degree n,
 hence the cohomological shift [-n]. Source: Stacks, Tag 0BR0
(blueprint: def-sc-locally-ranked-exterior-complex). -/
noncomputable def locallyRankedExteriorComplex {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) : CochainComplex X.Modules ℤ :=
  CochainComplex.of (locallyRankedExteriorTerm M r) (fun _ => 0)
    (fun _ => zero_comp)

```

The retired consumer's public signature:

```lean
theorem constantRankExterior_derived_iso {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M N : X.Modules) (d : ℕ) (e : M ≅ N) :
    Nonempty (((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj
        (locallyRankedExteriorComplex M (LocallyConstant.const X d))) ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (exteriorSheaf N d))⟦-(d : ℤ)⟧)
```

## New

The two Sheaf modules are withdrawn via `deleted.txt`. Their DAG attachments point to
`WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex` and
`WeilConjectures.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`, respectively.
The canonical construction is already present, unchanged:

```lean
/-- The open and closed rank-n stratum. Source: Stacks, Tag 0BR0
(blueprint: def-sc-locally-ranked-exterior-complex). -/
def exteriorRankOpen {X : Scheme.{uE}} (r : LocallyConstant X ℕ) (n : ℕ) : X.Opens :=
  ⟨{x | r x = n}, r.isLocallyConstant.isOpen_fiber n⟩

/-- Degree n is the extension from the rank-n stratum of its top exterior power;
negative degrees are zero. Direct image along this clopen inclusion is extension by zero.
Source: Stacks, Tag 0BR0 (blueprint: def-sc-locally-ranked-exterior-complex). -/
noncomputable def locallyRankedExteriorTerm {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) (n : ℤ) : X.Modules :=
  if 0 ≤ n then
    (pushforward (exteriorRankOpen r n.toNat).ι).obj
      (exteriorPower
        ((restrictFunctor (exteriorRankOpen r n.toNat).ι).obj M) n.toNat)
  else 0

/-- The complex wedge^r M[-r]: degree n is supported on the rank-n stratum and every
 differential is zero. On a rank-n component it is precisely wedge^n M in degree n,
 hence the cohomological shift [-n]. Source: Stacks, Tag 0BR0
(blueprint: def-sc-locally-ranked-exterior-complex). -/
noncomputable def locallyRankedExteriorComplex {X : Scheme.{uE}} (M : X.Modules)
    (r : LocallyConstant X ℕ) : CochainComplex X.Modules ℤ :=
  CochainComplex.of (locallyRankedExteriorTerm M r) (fun _ => 0)
    (fun _ => zero_comp)

```

The canonical comparison theorem has the same binders and conclusion with
`exteriorPower N d` in place of `exteriorSheaf N d`; its proof is already complete.
No new alias or duplicate declaration is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex | T4 | Retired definition module; its self-use is removed with the module. |
| Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison | unclaimed | Only direct importer of the old complex; retire its unused copy and attach its node to its proved upstream twin. |

A scan of every current Lean import found no remaining importer of the comparison
copy and no other importer of the complex copy. The older retirement inventory's
other consumers have already disappeared. Both upstream modules remain available;
all current users of the declaration names already import their upstream variants.
The upstream comparison's 144-module import closure contains no Sheaf modules and
therefore no pair of Sheaf/upstream twins. The unit's mathematical route and statements
are unchanged. No target signature or upstream declaration is edited. This substitutes
canonical exterior-power data for an independently constructed sheafification; target
semantic review should record the canonical construction if a target depends on it.

The remote audit compiled in 1.6 seconds, including both sign branches of the
canonical term definition. Axiom inspection of all three canonical definitions and
`constantRankExterior_derived_iso` found only `propext`, `Classical.choice` and
`Quot.sound`. `tools/downstream.py --uses` independently confirms the sole importer
and the absence of downstream users of the comparison.

## Status

landed 20261020T144305-L-2262278 2026-10-20 (merge of deliver/T4/Sheaf.AlgebraicGeometry.LocallyRankedExteriorComplex)
