## What changed

Prove `WeilConjectures.relative_product_input_domains` without changing its signature,
its definitions, or its public imports. The geometric conjunctions use Mathlib’s
base-change and composition instances. Finite-Tor closure uses the supplied
`SixFunctorDatum` preservation fields and normalization isomorphisms; a proved private
list lemma enumerates all 22 entries in the prescribed order. Finite witnesses use
`finiteRing_constructibleDerived_origin` and the actual realization equivalence.
Integral domains follow from `integral_residue_tor` and the constructibility of every
positive reduction. Two proved private comparison lemmas assemble coefficient passage
entrywise and compose the resulting `List.Forall₂` relations. Rational inputs use their
actual integral objects. Algebraically closed inputs are transported to the compositum
of their coefficient fields and then represented integrally there.

Add proof imports of `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` and
`Sheaf.Paper.FixProjectionCompactificationComparison`,
`Sheaf.Paper.DirectImagesConstructible` (the proved standing-prime unit lemma), and
`Sheaf.Paper.ProEtaleConstantModuleConstructibility` (isomorphism invariance via
restriction). Only the proved `identitySquare` constructor from
`FixProjectionCompactificationComparison` is used: it selects the existing tensor comparison
field for the given compactification; none of its projection theorems is used.
Update the existing node’s proof, proof dependencies, proof origin and obsolete tool uses
to describe this argument. No new module, public declaration, or node is added.

## Proved and sorry left

Closed: `WeilConjectures.relative_product_input_domains`
(node `lem-sf-relative-product-input-domains`), the item’s sole original hole.
Added: none. Remaining holes in the delivered module: none. Every private helper is proved.

This proves the item from existing named library declarations. It does not claim
that all imported declarations or their transitive proof dependencies are sorry-free.

## No longer needed

Remove the direct proof imports `Sheaf.Paper.FiniteTorStability`,
`Sheaf.Paper.ProEtaleConstructibleOrigin`,
`Sheaf.Paper.CanonicalOriginCompactSupportComposition`,
`Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`, and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`.

The node no longer uses `thm-sf-ctf-stability`: preservation and tensor closure are already
part of the supplied datum, transported through its normalization isomorphisms.
It does not need `lem-sf-package-coefficient-domain-realization` or its module
`Sheaf.Paper.SfPackageCoefficientDomains`: higher operations already take values in the
constructible categories and supply their coefficient comparisons.
It replaces `lem-sf-proetale-constructible-origin` by the existing finite-ring intrinsic
essential-image criterion `lem-weil-pbc-finite-ring-constructible-derived-origin`.
It does not need `thm-sf-comp-composition` or `thm-cbc-finite-level-proetale`: their
composition/exchange isomorphisms are not part of this domain assertion; the witnesses
are constructed directly. It does not use `def-exchange-projection` as a proof lemma;
that existing statement dependency and public import stay unchanged.

Delete the obsolete tool-use approvals for `thm-sf-ctf-stability`,
`lem-sf-package-coefficient-domain-realization`, `lem-sf-proetale-constructible-origin`,
`thm-sf-comp-composition`, and `thm-cbc-finite-level-proetale`.
These are dependencies pruned from this item’s argument, not a claim that their modules
have no other importers or are absent from its transitive import closure.
The blueprint unit’s statement and product-isomorphism route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The old proof plan asked for general preservation theorems already supplied by the
`SixFunctorDatum` hypothesis. It also cited composition and base-change isomorphisms
when only the domain witnesses were being asserted. The actual proof needs neither.
The finite-ring origin theorem already exposes the intrinsic-coefficient essential-image
criterion required here; it avoids another change of constant-ring presentation.
For integral lists, every entry is already a bundled constructible object, so the
residue-Tor theorem and reduction-origin argument apply directly to each entry.
The field comparisons are actual entrywise isomorphisms, including both tensor orders,
rather than an identification of field objects with their finite reductions.

Small cases: the finite-support bounds use a minimum, so the zero object and empty
support cause no failure. Positive coefficient exponents include one and are never
replaced by exponent zero. No nonempty scheme assumption is introduced. The common
compositum and stage isomorphisms work for equal or distinct coefficient fields;
no strict inclusion, compatible origin choices, or invertibility of the relative
product map is assumed. The unchanged 22-entry list includes the original inputs.

The existing finite-ring origin node is used as a tool from another unit; its theorem
is already proved. The projection-compactification module is used only for its proved
identity-square construction, not its mathematical comparison theorem.

The proof locally disables `IntegralHom.tensorLocalization` and
`IntegralHom.derivedCategory` while elaborating each declaration, following the
existing `IntegralConstructibleInternalHom` pattern. Their general module-universe
instances otherwise leave ambiguous universes for the fixed intrinsic categories.
This changes no exported attribute or existing definition. The finite-origin helper also
keeps `Padic.coefficientExtensionIdeal` locally irreducible: otherwise category-instance
search unfolds the quotient ideal repeatedly. It pins the fixed-module derived categories
to the canonical Grothendieck-abelian localization already used by their public types,
and supplies their derived-category instances directly. This avoids exploring unrelated
coefficient-reduction instances while elaborating the composition comparison.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
