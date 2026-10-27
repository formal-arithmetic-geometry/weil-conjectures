## What changed

The original theorem now has a complete combining proof from two separate statements:
existence of the normalized pullback comparisons for one line, and scalar-square
compatibility for already given normalized families. Its signature is unchanged.

The uniqueness part is proved here. Adjunction injectivity and pure-tensor
extensionality prove equality in nonnegative degrees. For each negative degree,
compose both maps with precomposition by the same positive isomorphism. The published
unique pairing transfer identifies these composites; cancellation proves equality.
No local-basis existence hypothesis is needed for this uniqueness argument.

SignedLinePullbackNormalization contains the two original Prop definitions verbatim,
publicly re-exported by the original module. This permits the separate lemmas without
an import cycle. The relocation record is
coord/changes/signed-line-pullback-normalization-location.md. The predicate bodies,
all existing signatures, the unit route and every target statement are preserved.

Validation: all four delivery modules compile together through lcompile.py. The
original module compiles in 23.9 seconds after removal of unused proof imports.
The downstream user scan found SignedLineDerivedBaseChange and
IntegralTwistSchemeCompatibility; both keep the same public predicate names and bodies.

## Proved and sorry left

Closed the original body hole in
SheafOfModules.existsUnique_signedLineScalarPullbackSquare by a decomposition.
Added two holes, not counted as two completed proofs:

- SheafOfModules.exists_signedLinePullbackNormalized in
  Sheaf.Paper.SignedLinePullbackExistence;
  node lem-pur-normalized-signed-line-pullback-exists.
- SheafOfModules.signedLineScalarPullbackSquare_of_normalized in
  Sheaf.Paper.SignedLineScalarPullbackNaturality;
  node lem-pur-signed-line-scalar-pullback-naturality.

The original module has zero sorry. The delivery has two sorry in total.
Its three private helpers are completely proved: pullback_section_ext,
pullback_tensor_section_ext and signedLinePullbackNormalized_unique.
No data definition chooses an arbitrary witness of an unproved existence theorem.
The main theorem eliminates the existence hypotheses only in a proof of Prop.

The existence lemma has one coefficient map and no scalar square or uniqueness.
The naturality lemma assumes the families and proves only the scalar square.
Neither restates the original existence-and-uniqueness result.

## No longer needed

Removed the direct proof imports Sheaf.CategoryTheory.SiteInverseImageTensor,
Sheaf.CategoryTheory.ModulePullbackTensorIso,
Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction, and
Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackLocalizationOfUniverses from the item.
The complete uniqueness proof uses the published PullbackPairingTransfer instead.

The generic tensor, inverse-image and localization nodes remain needed in the
construction/naturality split nodes, as recorded there. Thus no global node or module
is claimed pruned, and no upstream declaration is deleted or weakened.
The original node now depends directly on the two split nodes and the pairing-transfer,
sheaf-Hom and signed-tensor APIs used in its actual combining/uniqueness proof.

## Where the brief, the DAG or earlier work was wrong

The generic module_pullback_tensor_iso API is written with equal site/coefficient
universes and existential intermediate rings, whereas this statement uses the actual
chosen left adjoints at max u v w. It cannot simply be applied to obtain this module's
section-normalized comparisons. The missing work is retained explicitly in existence,
not hidden by a change of definitions or an unjustified tensor identification.

I explored a mixed-universe arbitrary-target pairing transfer, adapting the published
unit-valued transfer and tensor-Hom equivalence. Its local lift, evaluation, addition
and scalar compatibility compiled. Restriction compatibility remained expensive to
elaborate. This unfinished prototype is retained only as scratch text, with no module,
private sorry or extra dependency in the delivery.

Edge cases checked mathematically: degree zero is the coefficient map; degree one is
the supplied isomorphism; negative degrees are forced by evaluation and cancellation;
zero rings cause no nonzero division; the formulas use no flatness. The split lemmas
retain the full site, slice, universe and cover hypotheses of the corresponding parts
of the original argument.

## New nodes

lem-pur-normalized-signed-line-pullback-exists records the separate single-line
existence argument: coefficient unit, positive tensor recursion and finite-free dual
comparison for negative powers, with the source proof and exact Lean statement.

lem-pur-signed-line-scalar-pullback-naturality records only naturality of given
normalized families. Its proof uses unit-compatible localization, compatible local
signed bases and scalar balancing. It constructs no family and asserts no uniqueness.

Both nodes include three kinds of Mathlib search and preserve the original unit.
The existing definition node is updated only to attach its unchanged declarations to
their new module. Change record:
coord/changes/signed-line-pullback-normalization-location.md.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
