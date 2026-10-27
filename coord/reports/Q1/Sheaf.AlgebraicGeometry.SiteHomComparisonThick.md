## What changed

Completed the Lean assembly of `AlgebraicGeometry.ProEtale.siteHomComparison_exact_thick`
from two strictly smaller intermediate statements: signed exactness of the native closed
derived Hom, and shift compatibility of the canonical evaluation comparison. The assembly
constructs the actual natural transformation, transports the prescribed monoidal structure,
checks both all-degree shift formulas, and uses the induced triangle morphism with its
specified components. Its thick-locus argument is proved directly in the new module
`Sheaf.CategoryTheory.ContravariantIsoLocus`, using the existing triangle and retract API.

The already proved `siteHomComparison_restriction` is preserved. Its private square
helper now supplies the four categories explicitly, and the ordinary monoidal equality
helper unfolds the two equal constructions directly. Their statements are unchanged.
The original single hole concerns exactness, shifts, triangle compatibility and thickness;
restriction had already been proved by the earlier M2 delivery.

Relocated `siteHomTensorParameterShift`, `siteHomSourceShift`, and
`siteHomOppositeSourceShift` with unchanged signatures and bodies to
`Sheaf.CategoryTheory.NativeDerivedHomSignedExact` to avoid an import cycle. Their old
module publicly imports the new module. Their declaration names, signatures, visibility,
docstrings and construction bodies are unchanged. The three shifts and the two assertion
definitions are marked irreducible to bound kernel reduction; proofs unfold the assertions
explicitly once. The relocation and consumer search are
recorded in `coord/changes/site-hom-native-shifts.md`. No source-library file is changed.

## Proved and sorry left

Original item: one hole. Closed its body in
`AlgebraicGeometry.ProEtale.siteHomComparison_exact_thick` by decomposition. Zero holes
remain in the item module. This is a decomposition, not a claim that the comparison is
now independent of sorry.

The following new declaration is completely proved:

- `CategoryTheory.contravariantComparison_isoLocus`
  (`lem-sf-contravariant-comparison-iso-locus`).

Exactly two new holes are split off, each a public theorem with `:= by sorry`:

- `AlgebraicGeometry.ProEtale.nativeDerivedHom_signed_exact`
  (`lem-sf-native-derived-hom-signed-exact`), in
  `Sheaf.CategoryTheory.NativeDerivedHomSignedExact`.
- `CategoryTheory.Functor.exactDerivedHomComparison_shift`
  (`lem-sf-exact-derived-hom-comparison-shift`), in
  `Sheaf.CategoryTheory.ExactDerivedHomComparisonShift`.

The first proves properties of one native Hom functor without mentioning a comparison.
The second asserts only a shift square for a given canonical comparison, assuming the
normalized shift structures; it asserts neither exactness nor thick closure. Thus neither
is the original conclusion under another name. Each has its source and a complete
representative-level proof in its docstring and node. There are no holes in definitions
or private helpers. Final validation: `lcompile.py --all` compiled all four delivered Lean modules and the
unchanged downstream consumer `Sheaf.Paper.LisseFlatHomSiteComparison` against them.
The consumer was copied only for validation and is not delivered. Hole accounting: one closed, two added, net minus one.

Edge-case checks: degree zero has correction +1; degrees 1 and -1 have corrections -1
and +1. In the ordinary complexes of modules these give the signed cone boundary and
its inverse normalization. At M=0 and K=0 the comparison is between zero objects.
For the identity functor the comparison is the identity and the shift square is the
normalization equality. The categorical thick-locus proof handles the zero object,
all positive and negative shifts, and arbitrary retracts explicitly in Lean. Neither
new statement assumes preservation of K-injectives by comparison pullback: its proof
in words resolves FI to a separate K-injective J.

## No longer needed

Removed six unused original imports: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`,
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Sheaf.Paper.ComparisonPullbackExact`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`. Their declared proof-plan
interfaces do not supply the native normalized structures used here.
The only new private proof imports are `ExactDerivedHomComparisonShift` and
`ContravariantIsoLocus`; `NativeDerivedHomSignedExact` is public because it owns the
three existing definitions used in public assertion types.

The following dependencies are removed from the parent's direct proof route:

- `lem-sf-comparison-pullback-exact`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-coef-signed-derived-internal-hom-exact`.
- `lem-sf-ringed-hom-complex-pullback-shift`.
- `prop-pur-kinjective-resolutions-exist`.
- `def-pur-hom-complex`.
- `def-pur-derived-internal-hom`.
- `lem-pur-rhom-well-defined`.
- `def-weil-abstract-derived-category`.
- `lem-pc-kflat-resolution`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-sf-ringed-derived-closed-symmetric-monoidal`.
- `lem-sf-triangle-morphism-iso`.

These are dependency factoring, not whole-module withdrawals. The representative and
ringed-Hom dependencies remain needed through the two new intermediate proofs or
existing statement imports. In particular `lem-coef-signed-derived-internal-hom-exact`
is the source calculation for native exactness, and
`lem-sf-ringed-hom-complex-pullback-shift` plus `lem-pc-kflat-resolution` remain in the
comparison-shift node. The triangle two-of-three dependency is used in the proved
categorical helper through the existing upstream theorem, not a new imported Sheaf
proof. No claim is made that these modules leave the targets' transitive import closure.
No module is withdrawn, and no unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan uses the ringed `SheafOfModules` signed exactness theorem, but the item
uses the native `MonoidalClosed.internalHom` on derived categories of coefficient-valued
sheaves. The former's signature does not directly supply the latter's normalized
contravariant structure. Likewise, the ordinary Hom pullback shift theorem does not by
itself identify its localized map with the native derived evaluation transpose. These
two interface gaps are now separate, precisely stated items rather than hidden glue.
The existing upstream `exists_distinguished_ihom_pre` supplies an unspecified third
arrow and therefore cannot replace the all-degree normalization and fixed boundary.

Compilation uses the existing canonical derived monoidal and Grothendieck instances.
The signed-to-thick assembly is a proved private generic helper, avoiding expansion of
concrete sheaf structures at every conjunction constructor. The sandbox's original budget
and session metadata are retained.

## New nodes

`lem-sf-native-derived-hom-signed-exact`: coherent all-degree signed opposite shifts and
exactness of one native derived Hom functor. Its module also owns the three existing
shift constructions with unchanged bodies and explicit reduction controls. This is the
native counterpart of the existing ringed calculation.

`lem-sf-exact-derived-hom-comparison-shift`: only the shift equation for the exact derived
evaluation transpose. Its proof uses K-injective target replacement, K-flat source
comparison and signed ordinary reindexing, without requiring FI to be K-injective.

`lem-sf-contravariant-comparison-iso-locus`: completely proved categorical thick-locus
lemma using zero objects, shift squares, distinguished-triangle two-of-three and retracts
in the arrow category. The original node's proof and proof dependencies now follow
this assembly and preserve its prior restriction proof.

Change record: `coord/changes/site-hom-native-shifts.md`.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
