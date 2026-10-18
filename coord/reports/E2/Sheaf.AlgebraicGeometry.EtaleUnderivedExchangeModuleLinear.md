## What changed

Replaced the hole in `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
with a construction of the module pushforward square followed by its inverse mate.
The constant-section hypotheses imply the ring-map compatibility by sheafification
hom-extensionality. Mathlib's `pushforwardComp` and `pushforwardCongr₂` then construct
an actual natural module square. Its inverse mate under the given g' and g module
adjunctions is the required natural transformation. The existing abelian unit formula
`Etale.unit_map_baseChangeMap_app` proves the specified comparison after forgetting.

A private, fully proved reflexive API lemma identifies the underlying abelian map
of a module pushforward. The comparison uses this lemma and explicit congruences
instead of repeatedly unfolding restriction of scalars over the constant sheaves.

Updated the declaration docstring and the existing node's proof, proof dependencies,
and proof origin to describe this route. Existing declaration signatures, universe parameters, visibility, and public imports
are unchanged. The new universe names serve only the private helper. No new modules
or nodes were introduced. Change record:
`coord/changes/E2-etale-underived-exchange-private-api.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.etaleUnderivedExchange_moduleLinear`
(node `lem-weil-pbc-underived-exchange-module-linear`), the module's one original hole.
Added holes: none. Remaining holes in this delivery: none. This is a proof, not a decomposition.

Validation: the complete proof passed remote single-file compilation (53.4 seconds), with no warnings.
The delivery dry run passed compilation, axiom checks and preflight (CODEX review
class). The included change record documents the module-level universe command
and verifies that no downstream consumer needs adaptation.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`:
  the module composition-linearity theorem is unnecessary. The pushforward square
  follows directly from Mathlib's module pushforward API; taking its inverse mate
  supplies the exchange and its naturality. Node
  `lem-weil-pbc-inverse-image-composition-module-linear` and
  `lem-weil-pbc-inverse-image-composition-module-linear-core`
  (`Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore`) are no longer
  needed by this proof.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: its declarations are already
  provided by the existing public import of `WeilConjectures.SixFunctors.BaseChange.Square`.
  The composition node remains needed for its pushforward comparison.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: no use of the chosen-square structure;
  the existing `IsPullback` hypothesis and its `toCommSq` provide the needed square.
- `Sheaf.CategoryTheory.RingedSiteModules`: no use of the `ringedSiteModules` abbreviation;
  all module categories and morphisms use the existing Mathlib definitions directly.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: redundant with the
  existing public shim import. The compatible adjunctions are already universally
  quantified in the theorem, so no inverse-image witnesses need to be selected.

The separate node `lemma-weil-pbc-underived-exchange-naturality` is not a proof dependency:
Mathlib's mate equivalence constructs a natural transformation directly. The original
public import of its module remains because it also defines the exchange and square.
No unit statement or unit proof step is bypassed: this node is below the unit level.
These are dependencies pruned from this item, not a claim that no other parent uses them.

## Where the brief, the DAG or earlier work was wrong

The original four-step route is mathematically valid, but unnecessarily passes through
linearity of inverse-image composition. The existing abelian library already proves
that the exchange is the inverse mate of the pushforward square. Using that
characterization gives a shorter route wholly from the stated compatible adjunctions
and Mathlib. It also avoids conversion between the `CommRingCat` constant-sheaf
encoding of the composition theorem and this module's `RingCat` encoding.

The proof uses neither nonzero coefficients nor a nonempty scheme, and only uses the
commutativity part of the Cartesian-square hypothesis. The stronger existing statement
is retained verbatim. Sources read: Stacks `sites-modules.tex`, Lemmas 03D3, 03D7,
03D8, and `etale-cohomology.tex`, Lemma 03S6, proof. No source error or statement dispute.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
