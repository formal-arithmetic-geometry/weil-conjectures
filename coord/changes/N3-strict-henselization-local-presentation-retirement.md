# AlgebraicGeometry.Scheme.smallStrictHenselizationRing_local_presentation

## Reason

Complete the assigned retirement in `coord/retire-items.tsv` (the human's hand-off,
2026-10-20). The Sheaf copy has zero holes but remains a retirement item because a
small-colimit compatibility theorem was reintroduced in B4's landing. The upstream
local-presentation theorem is already complete. The small and full affine-neighbourhood
colimits are canonically isomorphic; they are not definitionally the same ring.

The one live call of the small-colimit theorem is in the unclaimed divisor-quotient
module. Preserve that consumer's full statement and transport the upstream local-base
algebra structure through `smallStrictHenselizationColimitIso` inside its proof. Construct
the quotient-localization action by a quotient lift followed by a localization lift, so
the proof can use the upstream localized-divisor theorem's explicit-action API. This
also avoids loading the two incompatible declarations of `localized_divisor_quotient`.
The private structural-map comparison is proved by the canonical coprojection equation.
No data is chosen from an unproved theorem.

The other direct importer has a planned use of the mathematical node and keeps that
use through an import of the upstream twin. All DAG parent edges and the unit route
remain. No source-library file, target statement, or ring definition changes.

## Old

The retired Sheaf module publicly provided the following small-colimit theorem:

```lean
theorem smallStrictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY)
```

The divisor-quotient consumer imported:

```lean
public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation
import Sheaf.RingTheory.StrictHenselizationLocalizedDivisorQuotient
```

Its proof applied `smallStrictHenselizationRing_local_presentation R barY b hb`, then
used the existential Sheaf `localized_divisor_quotient` API.
The trace-formula consumer privately imported the Sheaf local-presentation module.

## New

The item is withdrawn through `deleted.txt`; the delivery tool writes the standard
empty module. No new public declaration replaces its compatibility theorem. Its
mathematical node attaches to the retained upstream declaration:

```lean
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselization barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselization barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselization barY)
```

The divisor-quotient consumer imports:

```lean
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationLocalizedDivisorQuotient
```

Its theorem signature and visibility are verbatim unchanged. The proof identifies the
structural maps under the canonical comparison, pulls the local-base algebra structure
back along the inverse ring isomorphism, and transports its pointed-etale cocone
isomorphism. It then constructs the prime of `R/(f)`, its canonical residue-field
separable closure, and the localization lift defining the quotient action. The last
step applies the upstream localized-divisor theorem with this explicit compatibility.

The trace-formula import is switched to the upstream twin, preserving its mathematical
dependency. The existing local-presentation node is reattached to the upstream theorem,
its proof steps now describe that retained proof, and the divisor-quotient node records
the canonical transport and explicit quotient action. Natural-language statements and
all mathematical dependency lists are unchanged.

Validation: the two changed Lean consumers compile together without warnings. The
immediate regularity consumer also compiles unchanged against the sandbox artifacts.
The retained upstream local-presentation theorem and the adapted divisor theorem both
have exactly the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoordinateBlowupBranchDrop | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation | unclaimed | Adapt imports and proof; keep the exact statement and visibility. Canonical transport and quotient-localization action replace both Sheaf proof dependencies. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | Only direct importer of the adapted divisor theorem. Compiles unchanged against the new proof and public imports. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.NormalCrossingsStrictification | unclaimed | Indirect importer only. Public theorem signatures and all ring definitions used here are unchanged; no source edit. |
| Sheaf.TraceFormula.CoordinateMaximalBranchStratum | unclaimed | Switch the private dependency import to the upstream twin; statement and unfinished proof unchanged. |

`tools/downstream.py --uses smallStrictHenselizationRing_local_presentation` finds
only the retired declaration and the adapted divisor-quotient application. There are
no additional Lean consumers in quarantine. Other DAG parents (including unfinished
parents) keep the same node, now realized by the upstream theorem. The canonical
isomorphism gives the required small-colimit interpretation, as demonstrated by the
complete divisor-quotient proof in this packet. No target's definitions change, so no
target statement review is reopened.

## Status

landed 20261021T003514-L-1645355 2026-10-21 (merge of deliver/N3/Sheaf.AlgebraicGeometry.StrictHenselizationLocalPresentation)
