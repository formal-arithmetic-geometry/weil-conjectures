## What changed

The sole hole of `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` is replaced by a
compiling compactification argument. Embed the affine source in relative projective
space, factor its immersion through its scheme-theoretic image, push through the dense
open and closed immersions, then apply projective-space finiteness and the existing
bounded-complex truncation devissage. Actual derived-composition isomorphisms identify
this composite with the original derived direct image. No definition, original public
import, existing signature or visibility changes.

Three new modules state the geometric inputs. The closed-immersion input is fully
proved using exactness, the closed counit and an open-closed stratification. The
dense-open and projective-space inputs are the two remaining named obligations.
They use the concrete modules over locally finite continuous Qbar_l-valued functions.

I continued down the proof dependencies and proved the needed generic closed-immersion
counit in unclaimed `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`.
The affine closed-site adjunction makes precomposition fully faithful; scheme
isomorphisms give arbitrary affine targets, then weakly etale base change, double mates
and open-cover conservativity give the global counit. A proved abstract private helper
keeps the double-mate calculation from expanding scheme adjunctions: this reduced
compilation from about 53 seconds to about four, without changing definitions or limits.

For the finite levels of the projective input I proved all three existing holes of
unclaimed `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper`. Proper
constructibility, finite torsion cohomological dimension and truncation devissage give
bounded constructibility. Proper base change and the geometric-fibre 2d bound give
uniform vanishing. Exact pullback and bounded-below/total-derived compatibility give
the comparison statement in every integer degree, including negative degrees.

I also proved the exact project predicates in unclaimed
`Sheaf.AlgebraicGeometry.ProperBoundedConstructible` and
`Sheaf.AlgebraicGeometry.ProperCaseConstructibility`. They use the existing proved
comparison between finite-constant-value and finite-stalk constructibility, and handle
empty targets explicitly before descending an invertible exponent to the ground field.
No module held by another group is changed.

All eight modules compile together through `lcompile.py --all`. The five modified
existing modules have no interface changes according to `leanindex.interface_changes`.
The original item and generic closed-counit imports remain; added imports are private.

## Proved and sorry left

Closed the original item hole:

- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine`
  (`lem-sf-adic-affine-direct-image-finiteness`). This is a decomposition into two
  strictly more specialized geometric inputs, with a proved closed step and a real
  compactification/composition argument. It is not an axiom-free proof of all finiteness.

Closed six existing dependency holes:

- `AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`
  (`lem-exc-proetale-closed-fully-faithful`).
- `AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_of_isProper`
  (source realization of `thm-fin-proper-case`).
- `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMapPlus_of_isProper`
  (source realization of `obl-fin-comparison`).
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isProper`
  (source realization of `lem-fin-proper-bounded-constructible`).
- `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_proper`
  (`lem-fin-proper-bounded-constructible`, its exact attached Lean declaration).
- `AlgebraicGeometry.Etale.properCase_constructible_and_vanishing`
  (`thm-fin-proper-case`, its exact attached Lean declaration).

New proved theorem:

- `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_of_isClosedImmersion`
  (`lem-sf-adic-closed-direct-image-finiteness`). Every private helper is proved too.

Exactly two new holes remain, each as the whole proof `:= by sorry` in its own module:

- `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_of_denseOpenImmersion`
  (`lem-sf-adic-dense-open-direct-image-finiteness`). It needs finite-extension descent,
  a constructible integral lattice complex, complete direct-image/reduction comparisons,
  and rationalization/coefficient-extension comparisons for the concrete AdicSheaf model.
  The existing torsion open-finiteness and integral DAG statements do not yet expose
  these coefficient bridges in Lean. Its finite torsion cohomological-dimension bound
  must be independent of the coefficient quotient; it is not twice the fibre dimension
  of the open immersion.
- `AlgebraicGeometry.ProEtale.bounded_constructible_rightDerivedFunctor_adicLowerStar_projectiveSpace`
  (`lem-sf-adic-projective-space-direct-image-finiteness`). The same concrete coefficient
  comparisons remain. Its finite-coefficient proper bounded-constructibility and uniform
  fibre vanishing inputs are now proved in this sandbox. It concerns only projective
  projections and degree-zero sheaves; the parent's proved devissage handles complexes.

No other hole remains in any delivered Lean module. This closes seven existing holes
and adds two (raw net five across delivered declarations); actual target-import-closure
figures belong to the sorry ledger. Existing dependency holes are not claimed closed.
The closed-site adjunction uses
`AlgebraicGeometry.Scheme.AffineProEt.affine_closed_site_functor_properties`, in a module
this delivery does not change. This upstream declaration is now proved in the available
library: independent `#print axioms` checks show only `propext`, `Classical.choice` and
`Quot.sound` for the generic closed counit and the new adic closed-image theorem. The
affine theorem, both new open/projective inputs and all five finite-coefficient proofs
still report `sorryAx`, as well as those three axioms. Their named imported obligations
are not claimed discharged by this delivery.

## No longer needed

No original import of the item or generic closed-counit module is removed. The item's
four added imports are the three geometric input modules and
`WeilConjectures.Compactification.Affine`. The closed-counit proof adds three private
imports: `ClosedSiteAdjunction`, `BaseChange.WeaklyEtale`, and
`OpenImmersion.Conservative`. The proper source adds private imports for finite
cohomological dimension, bounded-complex devissage and proper base change.

The two exact finite-coefficient project modules replace their former proof imports
with the proper source module and the constructibility comparison. Removed imports:

From `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`:

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.ProperCaseConstructibility`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `Sheaf.Topology.DimensionSupremumLocalDimensions`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

From `Sheaf.AlgebraicGeometry.ProperCaseConstructibility`:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages`
- `Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`

`lem-exc-closed-inverse-image-formula` is removed from the closed-counit node's proof
dependencies. This was its only citing node in the supplied DAG. Full faithfulness of
precomposition proves the counit without a separately sheafified inverse-image formula.
The associated inverse-image-evaluation/left-adjoint development is not required by
this proof. I do not withdraw its modules, which may have other Lean importers.
The direct counit dependency on `lem-exc-closed-lift-reduction` is removed too, but it
remains needed through the closed-site adjunction and is not claimed pruned.

The proper bounded-complex proof no longer needs its separate fibre-dimension and
local-dimension/base-change construction, a chosen injective representative, the
truncation spectral sequence or `thm-fin-proper-case`. Finite cohomological dimension
and finite truncation triangles replace that calculation. The proper-case proof no
longer needs the finite geometric-fibre comparison theorem or a separate constructible
pullback/fibre-finiteness calculation: proper torsion base change and the generic
torsion 2d bound suffice. These nodes may still be needed elsewhere and are not claimed
globally pruned. The realized statement/step lists of `sk-prop-sf-cbc` are empty; no
mandated unit realization is bypassed. The item's compactification and Cech unit route
is retained. No torsion open-finiteness or proper-finiteness theorem is pruned.

For completeness, these are all old `proof_deps` absent from the revised node records
(removal of a direct proof edge does not imply global pruning):

- `lem-exc-proetale-closed-fully-faithful`: `lem-exc-closed-inverse-image-formula`,
  `lem-exc-closed-lift-reduction`.
- `lem-fin-proper-bounded-constructible`: `def-weil-pbc-constructible-complexes`,
  `def-weil-pbc-direct-image`, `def-weil-pbc-scheme-conventions`,
  `lem-fin-finite-type-fibre-dimension-bound`, `lem-sc-fibre-dimension-after-base-change`,
  `lem-weil-pbc-dimension-supremum-local-dimensions`,
  `lem-weil-pbc-dplus-injective-representative`,
  `lem-weil-pbc-module-direct-image-left-exact`,
  `lem-weil-pbc-module-sheaves-enough-injectives`,
  `lem-weil-pbc-ring-sheaves-grothendieck`, `thm-fin-proper-case`, `thm-sp-truncation-e2`.
- `thm-fin-proper-case`: `cor-weil-pbc-geometric-fiber-finite`, `def-constructible-finite`,
  `def-finrepair-property-c`, `def-weil-finite-type-morphism`,
  `def-weil-pbc-constructible-complexes`, `def-weil-proper-morphism`,
  `lem-pur-scheme-constructible-preimage`, `lem-weil-pbc-fibre-product-affine-spectra`,
  `prop-constructible-pullback`.

The definition nodes on these lists remain statement dependencies or are supplied by
the existing interfaces; no definition is withdrawn. The categorical prerequisites and
Serre/pullback infrastructure still used transitively are not claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original introductory comment claimed an upper bound twice the supremum of fibre
dimensions for ordinary direct image. This is false: G_m -> A^1 has zero-dimensional
fibres but a nonzero degree-one boundary direct image for the constant l-adic sheaf.
Only that comment is corrected to a finite upper bound. No statement is weakened.

The affine adic declaration's docstring pointed to `sk-prop-sf-finiteness`, but the
supplied DAG had no direct Lean attachment for it. Occurrences of the module name were
nested source audits. A new node records the exact existing theorem and its proof;
three new nodes record its geometric inputs. No torsion statement is changed to adic.

The available finite-coefficient and integral statements use different coefficient
categories. Their Lean declarations cannot simply be applied to the concrete AdicSheaf
model. The remaining obligations explicitly include these bridges. The integral source
argument chooses a constructible lattice complex; a globally lisse lattice need not
exist. Empty schemes, zero sheaves and projective zero-space cause no exception; local
probes checked these cases without applying the two new holed finiteness assertions.

The existing integral-direct-image dependency closure contains the pre-existing cycle
`lemma-weil-pbc-derived-exchange-replacement` ->
`lem-weil-pbc-derived-exchange-termwise` ->
`lem-weil-pbc-derived-exchange-bounded-comparison` ->
`lemma-weil-pbc-derived-exchange-replacement`. This delivery introduces no such cycle;
those upstream files are unchanged and need maintainer attention.

LeanSearch was unavailable and recorded as such. LeanFinder, Loogle and direct searches
of Mathlib and both project roots were used. The Bhatt--Scholze paper was read locally,
especially Lemmas 6.7.2/6.8.13, Propositions 6.8.11/6.8.14 and Remark 6.8.15.
No literature binary or probe module is delivered.

## New nodes

`lem-sf-adic-affine-direct-image-finiteness` records the original affine theorem and its
actual compactification proof, bounded-complex devissage and derived-composition maps.

`lem-sf-adic-closed-direct-image-finiteness` records the proved closed-image step for
bounded constructible complexes over a noetherian target. It introduces no hole.

`lem-sf-adic-dense-open-direct-image-finiteness` records the affine-source, quasi-compact
dense-open step. Its remaining work is the concrete integral/rational coefficient passage.

`lem-sf-adic-projective-space-direct-image-finiteness` records only projective projections
on sheaves in degree zero. Its finite-level proper inputs are now proved; the concrete
coefficient comparisons remain. Neither hole is the original affine theorem renamed.

The existing closed-counit, proper bounded-constructible and proper-case nodes change
only proof-owned fields. Their statements and original attached Lean declarations stay
unchanged. The source proper comparison follows the existing fibre/base-change route;
no node statement is modified for the stronger source coefficient conventions.

Change records: `coord/changes/adic-affine-finiteness-closed-counit.md` and
`coord/changes/proper-bounded-constructible-proof.md`. All dependency modules changed
were unclaimed; no forced adaptation or existing interface change is involved.

## Second reading by C3

1. **Interfaces — pass.** Read every delivered module and compared all five existing
   modules with the read-only repository using `diff`. Parsed raw declaration slices
   confirm that all existing signatures are byte for byte identical after restoring one
   extra space before `:=` in the proper comparison theorem. No definition, instance,
   notation, existing visibility or original public import changes. The only new public
   declarations are the three geometric inputs; proof imports are private. The added
   closed-counit helpers are private proved lemmas. The four dependency modules are
   unclaimed in the supplied claim table, so no forced adaptation is asserted.

2. **Proofs — pass, with the reported dependencies still open.** All eight files compile
   in import order through `lcompile.py --all`, without diagnostics. The only two textual
   holes are the whole proofs of the new dense-open and projective-space theorems; no
   data definition or private helper has a hole, and no forbidden declaration occurs.
   Independent scratch `#print axioms` checks on all ten relevant declarations show only
   `propext`, `Classical.choice`, `Quot.sound`, and where appropriate `sorryAx`. In
   particular the generic closed counit and adic closed-image theorem have no `sorryAx`.
   The affine reduction and the five finite-coefficient proofs still do. The closed-site
   adjunction is chosen only locally in proofs for fixed functors, and no arbitrary
   existence witness is installed as data. Seven existing declaration holes close and
   two new holes are added; the affine argument remains a decomposition.

3. **Split statements — pass.** Read both statements, their complete docstrings and their
   nodes against Bhatt--Scholze Lemmas 6.5.9, 6.5.11, 6.7.2, 6.8.13, Propositions 6.8.11,
   6.8.14 and Remark 6.8.15 in the local paper. Finite type over the field supplies
   noetherianity and quasi-excellence; the characteristic hypothesis supplies invertible
   coefficients. A quasi-compact open immersion is finitely presented here. Integral
   constructible complexes, rather than globally lisse lattices, suffice. The coefficient
   reduction comparisons and rationalization must concern the actual locally finite
   continuous coefficient sheaves. Each input is only one geometric part of the affine
   proof. Independently compiled probes cover zero sheaves, empty targets, the identity
   dense open and projective zero-space, without invoking the two new holed inputs.
   Independent LeanFinder searches for open pushforward of local systems and projective
   cohomology, a Loogle search for constructible derived statements, and direct searches
   of Mathlib, both library roots and the upstream adic module found no usable shorter
   theorem. The upstream affine theorem still has its original hole. Existing torsion
   and integral declarations use different coefficient categories and cannot directly
   discharge these adic statements.

4. **Route and pruning — pass after report repair.** The actual affine proof embeds the
   source into a projective chart, takes the scheme-theoretic image, applies dense-open
   and exact closed direct image, then projective finiteness and finite truncation
   devissage. The two derived-composition isomorphisms have the correct direction and
   transport the actual composite to the original morphism. The original finite-cover
   Mayer--Vietoris argument and unit route remain intact. The existing adic exactness
   wrapper in `Adic.ClosedSupport` cannot shorten this proof's imports: through
   `ClosedImmersionStages` it already imports the item and would create an import cycle.
   The closed proof therefore uses the underlying exactness theorem and forgetful
   functor directly. Checked the `realized` records of `sk-prop-sf-finiteness` and
   `sk-prop-sf-cbc`; neither mandates an omitted node. Added the complete list of old
   proof dependencies removed from each revised node. Direct edges removed and private
   imports dropped are distinguished from modules globally pruned; none is claimed
   globally pruned without the ledger's verification.

5. **DAG — pass.** The existing nodes change only their proof-owned fields (and the
   closed-counit Lean attachment). All seven node records have `proof_deps` equal to
   the union of their proof-step `uses`, and every dependency ID exists. New nodes name
   the concrete coefficient model, geometric hypotheses, full Lean signatures, source,
   provenance, searches, chapter, unit and creation record. The affine, closed, dense-open
   and projective statements agree with their Lean declarations. Traversing the overlaid
   proof graph finds no cycle through any delivered node. Confirmed the independently
   reported exchange-replacement cycle in unchanged upstream nodes; this delivery does
   not create it. The finite-coefficient nodes describe the source-library proofs and
   the conversions to their original exact attached declarations.

Changes made by this reading: restored byte-identical signature whitespace in the
proper comparison theorem; completed the removed-dependency inventory; corrected the
stale claim that the available closed-site input remains a hole; recorded the actual
axiom results, independent searches, edge probes and route checks. No mathematical
statement or proof argument was changed.
