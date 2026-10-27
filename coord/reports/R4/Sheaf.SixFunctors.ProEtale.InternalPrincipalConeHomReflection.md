## What changed

Proved `AlgebraicGeometry.ProEtale.AdicCompletion.internal_principal_cone_hom_reflection`
with its existing signature. All supporting declarations are proved private helpers in the
item module. The proof constructs the section determined by the pulled-back endomorphism
of the tensor unit and verifies its action by the existing pure-tensor and unitor formulas.
It then transports to the canonical small site, applies the existing singleton Koszul
reflector through its two unit-compatible comparisons, and transfers the Hom bijection
back through the fully faithful derived equivalence. The node copy records this route.
No definition or statement was changed; no other module was adapted. Private proof
context is recorded in
`coord/changes/R4-internal-principal-cone-private-proof-context.md`.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.AdicCompletion.internal_principal_cone_hom_reflection`
(node `lem-pe-internal-principal-cone-hom-reflection`).

Zero holes remain in the item module; zero holes were added. No new split statements.
The proof uses existing declared dependencies, including
`CategoryTheory.principalKoszulRoos_presentation_comparison`, whose independent proof
remains an existing project obligation. This delivery does not claim that the whole
transitive closure is free of `sorry`.

## No longer needed

The public statement imports are preserved. No existing direct import was removed.
The trial proof import `Mathlib.Algebra.Homology.GrothendieckAbelian` was removed
because the proof uses neither its declarations nor its instances.

The original proof plan's `lem-sf-open-roos-unit-adjunction`
(`Sheaf.SixFunctors.OpenRoosUnitAdjunction`) is unnecessary: it concerns a more specialized
open-immersion setting, whereas the singleton ringed Koszul reflector supplies the needed
Hom bijection directly on the small model.

`lem-pur-principal-cone-small-site-criterion`
(`Sheaf.Paper.PrincipalConeSmallSiteCriterion`) is not used: its conclusion records only
output completeness and unit invertibility. The proof instead uses the same underlying
unit-compatible cone/Koszul comparison and Koszul presentation comparison to obtain the
Hom bijection. Neither module is withdrawn; other consumers may still need them.

Identification of the scalar section with the constant uniformizer, and the regularity
consequences of `hd`, are unnecessary for this reflection assertion. The proof works for
any endomorphism of the regular coefficient module. The given hypothesis and theorem
signature are retained.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies contain the needed mathematics, but the original plan cites the
small-site criterion without its Hom reflection assertion. Its proof contains the relevant
normalized comparisons. The present proof applies those existing comparison declarations
and the reflector directly, retaining the actual unit equality throughout.

The general singleton reflector applies to the image ideal of an arbitrary scalar;
regularity and pointwise identification with the uniformizer are not required. This also
covers the zero scalar, a unit scalar, and zero complexes, without adding hypotheses.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
