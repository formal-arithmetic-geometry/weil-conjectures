## What changed

Completed the existing sandbox proof of
`RingHom.isNagataRing_and_jTwo_of_weaklyEtale` without changing its signature or public
imports. The proof uses a finite normal model for each finite residue extension for
both the Nagata and J-2 clauses. J-2 uses the inverse image of the source regular locus
and flat local regularity ascent, avoiding explicit principal-localization calculations.

The new module `Sheaf.RingTheory.WeaklyEtaleFiniteResidueModel` supplies
`RingHom.exists_finite_residue_model_of_weaklyEtale` with a full proof body:
choose a finite residue basis, normalize the resulting finite source subfield, base
change, and select the normal domain factor cut out by the multiplication-map kernel.
Its fraction-field proof uses the chosen basis. The original module's DAG route is
updated, and the normalization construction gets its own node. The unit record has
empty realized arrays; none of its statements or steps is bypassed or changed.

The earlier transport failures were followed by successful server compilation of both
current modules (`scratchpad/compile-final1.log`: 10.1 seconds for the model and
2.6 seconds for the item). The latest resumed delivery dry run passed at commit `a9efec6642`
(`scratchpad/dry-recovery.log`), classified CODEX because it adds a proved module and
updates the DAG. Both modules compiled and passed preflight; this run reported no
axiom-probe fallback. An earlier model axiom probe had timed out, but the current run
completed that check. Existing signatures, definitions and consumer modules are unchanged.

The normalization proof abstracts the small field copy by unpacking its existence
statement before constructing the integral closure. This keeps typeclass synthesis
from repeatedly unfolding the concrete `Shrink` field structure. No module was split
for compilation performance; the finite-model lemma is the separate normalization
construction used by both halves of the original argument.

## Proved and sorry left

Original module: one hole, in
`RingHom.isNagataRing_and_jTwo_of_weaklyEtale`; its body is replaced with a complete
proof from the existing J-2 criterion, local regularity ascent, and the new model lemma.
The new theorem `RingHom.exists_finite_residue_model_of_weaklyEtale` also has a complete
proof body. There are zero textual `sorry` holes in either delivered module, and zero
holes split off. Both modules have passed server compilation. The proof uses existing
project theorems, including the J-2 residue-field criterion; any pre-existing holes in
their dependencies remain outside this delivery. No declaration with `sorry` is added.
Thus the item closes one of one original holes and adds zero holes.

## No longer needed

Removed proof imports from the item:
- `Sheaf.RingTheory.WeaklyEtaleField`
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
- `Mathlib.RingTheory.RegularLocalRing.Defs`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`
- `WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso`
- `Sheaf.RingTheory.JapaneseDomain`
- `Mathlib.RingTheory.Localization.Integral`
- `Sheaf.RingTheory.NormalOfFlatNormalFibers`
- `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
- `Mathlib.RingTheory.Spectrum.Maximal.Localization`
- `Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Sheaf.RingTheory.RegularMapAscent`
- `Mathlib.CategoryTheory.MorphismProperty.Limits`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Sheaf.AlgebraicGeometry.IsRegularScheme`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`

Normality and finite-product dependencies move into the new finite-model module;
the following original proof dependencies are still used there, rather than pruned:
- `lem-weil-pbc-weak-etale-field`
- `def-weil-pbc-normal-ring`
- `lem-weil-pbc-integral-closure-finite-extension-normal`
- `lem-weil-pbc-localization-normal-domain`
- `lem-weil-pbc-flat-normal-fibres-noetherian-normal`
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`
- `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`

The following original DAG dependencies are not used by either delivered proof:
- `lem-weil-pbc-minimal-prime-reduced-localization-field`
- `lem-weil-pbc-weakly-etale-composition-base-change`
- `lem-weil-pbc-affine-chart-base-change-iso`
- `lem-weil-pbc-prime-localizations-jointly-injective`
- `lem-weil-pbc-spec-localization-away-basic-open`
- `lem-weil-pbc-localization-prime-residue-field-iso`
- `def-weil-regular-scheme`
- `lem-weil-pbc-regular-map-ascent`
- `lem-weil-pbc-product-prime-localization`

In particular, scheme affine-chart base-change is replaced by the ring tensor API;
the full regular-map-ascent lemma by its local regular closed-fibre theorem; and the
principal-open/product-localization route by the inverse image of the regular locus.
The unused entries of the parent's `tool_uses` are removed in their original order.
This report makes no assertion that another parent's imports cease reaching any of
these modules: pruning is relative to this proof.

## Where the brief, the DAG or earlier work was wrong

The old continuation note described a one-hole model lemma, but the retained source
already contained its full normalization and normal-factor proof. The saved compiler
log predates repairs visible in that source. It must be compiled afresh, rather than
restored to the obsolete one-hole draft.

The planned residue-field theorem is stated in one universe. This construction must
handle `A : Type u` and `B : Type v`, so the private `residue_algebraic` argument works
through the fibre localization directly. Only a finite subextension of the possibly
infinite algebraic residue extension is shrunk to the universe of A. No arbitrary
witness of an unproved mere-existence theorem is used in a definition.

The normalization/model statement is a separate part of the source argument: it uses
only Nagata, no J-2 hypothesis or regularity conclusion. All private helpers have
proof bodies. Edge cases: B=0 has no q; fibres are allowed to be zero; the nonempty
product factor is selected only in the presence of the field-valued map; the finite
residue extension need not have finite degree over the source residue field.

Checked Stacks Tags [092Q](https://stacks.math.columbia.edu/tag/092Q),
[0C22](https://stacks.math.columbia.edu/tag/0C22),
[030C](https://stacks.math.columbia.edu/tag/030C), and
[07PC](https://stacks.math.columbia.edu/tag/07PC) against the argument.

## New nodes

`lem-exc-weakly-etale-finite-residue-model` records the finite normal residue-model
construction (original parent steps 3–7), realized by
`RingHom.exists_finite_residue_model_of_weaklyEtale` in its own module. Its node includes
three recorded search kinds and a six-step proof. It is strictly smaller than the item:
it assumes no J-2 and proves no openness of regular loci or Nagata property of B.
No change record is needed: existing signatures and definitions are unchanged.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
