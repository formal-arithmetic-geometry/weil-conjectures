# WeilConjectures.sfCompactSupportTerm and the specified quotient tower

## Reason

Extract the existing tower definitions from the constructibility theorem module into
`Sheaf.Paper.SfIntegralCompactSupportTower`. A separate slice/intrinsic presentation
lemma needs these definitions, while the main constructibility proof imports that lemma.
The extraction avoids an import cycle. It is not a performance split: no proof or
changed definition was divided to meet a compiler limit.

No signature, binder, universe, attribute, instance priority or definition body changes.
The old module publicly imports the new module and retains the theorem with its exact
original signature. Every old public import remains available transitively through the
new module. The only moved proof is the already proved projection-transition equation;
its proof is unchanged. No adopted source-library declaration is changed.

## Old

The following declarations were in `Sheaf.Paper.SfIntegralCompactSupportConstructible`:

```lean
/-- Positive coefficient levels are finite. Source: blueprint coefficient extension;
Bhatt--Scholze, Section 6.7 (blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportCoefficientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Restriction from exponent n+2 to exponent n+1 along the specified quotient map.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable abbrev sfCompactSupportFiniteRestriction (T : Scheme.{u}) (n : ℕ) :
    scalarReductionTarget.{u, u} l E T n ⥤ scalarReductionTarget.{u, u} l E T (n + 1) :=
  proEtaleCoefficientRestrictScalars T (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is left exact. Source: Stacks Tag 03DA
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportFiniteRestrictionLimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- Finite quotient restriction is right exact. Source: Stacks Tag 03DA
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable instance sfCompactSupportFiniteRestrictionColimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (sfCompactSupportFiniteRestriction l E T n) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits T
    (Padic.coefficientExtensionTransition l E (n + 1))

/-- The completion projections commute with the specified finite quotient transition.
Source: Stacks Tag 03CO; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-integral-compact-support-constructible).
Proof: the completed sheaf is the inverse limit of the finite quotient tower.
Its cone condition identifies the higher projection followed by the quotient map
with the lower projection. Forgetting commutativity gives exactly this condition
for ring sheaves; faithfulness lifts it back to commutative ring sheaves. -/
theorem sfCompactSupportProjection_transition (T : Scheme.{u}) (n : ℕ) :
    completedIntegralCommRingProjectionUnrestricted l E T (n + 1) ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) =
      completedIntegralCommRingProjectionUnrestricted l E T n := by
  apply (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
  change limit.π (integralCoefficientSheafSystem l E T) (Opposite.op (n + 1)) ≫
      integralCoefficientSheafTransition l E T n =
    limit.π (integralCoefficientSheafSystem l E T) (Opposite.op n)
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using limit.w (integralCoefficientSheafSystem l E T)
      (homOfLE (Nat.le_succ n)).op

/-- The sectionwise identity composite restriction comparison, supplied by the shared
commutative ring-sheaf restriction interface. Source: Stacks Tags 03DA and 03CO
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    sfCompactSupportFiniteRestriction l E T n ⋙
        scalarReductionRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionRestriction.{u, u} l E T n :=
  pbcRestrictComp (completedIntegralCommRingProjectionUnrestricted l E T (n + 1))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift))
    (completedIntegralCommRingProjectionUnrestricted l E T n)
    (sfCompactSupportProjection_transition l E T n)

/-- Exact restriction composition on derived categories. Source: Stacks Tag 015F
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportDerivedRestrictionComp (T : Scheme.{u}) (n : ℕ) :
    (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction.{u, u} l E T (n + 1) ≅
      scalarReductionDerivedRestriction.{u, u} l E T n :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCompactSupportRestrictionComp l E T n)

/-- The canonical reduction map at the finite coefficient level. It is the adjunct
of the lower reduction unit under the higher reduction/restriction adjunction.
On a K-flat representative it is precisely x tensor a ↦ x tensor rho(a), since that
adjunction's unit is x ↦ x tensor 1 and the restriction comparison is identity on
sections. Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tags 03EK and 07A6
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportReductionTransition (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E T (n + 1)).obj K ⟶
      (sfCompactSupportFiniteRestriction l E T n).mapDerivedCategory.obj
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E T (n + 1)).choose.homEquiv
    K _).symm
    ((sfDerivedReductionUnit l E T n).app K ≫
      (sfCompactSupportDerivedRestrictionComp l E T n).inv.app
        ((scalarReductionDerivedExtension.{u, u} l E T n).obj K))


variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The actual term Res_n R(c.g)_* c.i_! (K tensor^L A_n), where the natural index
n denotes exponent n+1. Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportTerm
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    DerivedCategory (scalarReductionSource.{u, u} l E Y) :=
  (scalarReductionDerivedRestriction.{u, u} l E Y n).obj
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))

/-- The specified quotient transition: apply compact support at the higher level to
the reduction map, apply the compact-support restriction comparison, and restrict to
completed coefficients. The final identity-on-sections comparison identifies the two
composite restrictions. Source: Bhatt--Scholze, Sections 6.5 and 6.7
(blueprint: lem-sf-integral-compact-support-constructible). -/
noncomputable def sfCompactSupportTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    sfCompactSupportTerm l E c K (n + 1) ⟶ sfCompactSupportTerm l E c K n :=
  (scalarReductionDerivedRestriction.{u, u} l E Y (n + 1)).map
    ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
        (sfCompactSupportReductionTransition l E X K n) ≫
      (sfCompactSupportRestriction c
        (Padic.coefficientExtensionTransition l E (n + 1))).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
    (sfCompactSupportDerivedRestrictionComp l E Y n).hom.app
      ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))
```

## New

The declarations above, with exactly the same signatures and bodies, are in
`Sheaf.Paper.SfIntegralCompactSupportTower`. Only their docstring blueprint labels
change to the new definition-ownership node. The original module now begins with:

```lean
public import Sheaf.Paper.SfIntegralCompactSupportTower
```

The public theorem `WeilConjectures.sfIntegralCompactSupport_constructible` remains
in the original module with the exact original signature. Its completed assembly proof
uses the slice proper-image theorem and the separate presentation comparison.

## Users

`tools/downstream.py --uses` was run for all ten moved declarations. The table includes
their users and consumers of the unchanged constructibility theorem. Textual uses were
read; no declaration can become stronger or weaker because both signatures and bodies
are unchanged. The source module public-reexports all the moved declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | W9 | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.CompactSupportTotalLimitRealization | C7 | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same declarations through the public reexport; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | E3 | Publicly imports the extracted definitions; theorem proof completed. |

## Status

landed 20261025T011011-L-3633664 2026-10-25 (merge of deliver/E3/Sheaf.Paper.SfIntegralCompactSupportConstructible)
