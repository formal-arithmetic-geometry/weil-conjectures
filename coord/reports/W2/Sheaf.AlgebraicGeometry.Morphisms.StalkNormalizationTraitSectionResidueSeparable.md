## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_residue_separable`
by a complete Lean assembly from the existing
`GaloisCover.stalk_normalization_trait_charts` and the new generic theorem
`AlgebraicGeometry.Scheme.tameRootProduct_residue_separable`.
All existing signatures and public imports are unchanged. New imports are proof-only.
Updated the original node's proof, proof_deps and proof_origin to match the assembly.

The private helpers prove transitivity of residue separability, descent along an
embedding of residue fields, separability for etale maps, descent from one etale
base chart, compatibility with the canonical stalk-map residue algebra, and the
assembly for a jointly surjective family of root charts. No helper contains sorry.
The proof actually works at every point of the local normalization: the closed
section equality and the generic section identities need not be used.

The normalization types require a larger heartbeat budget; abstracting the chart
assembly over a general morphism avoids repeatedly elaborating those concrete
normalization types. Both delivered modules compile locally within the 60-second
per-file limit. The full dependent proof previously timed out while reconstructing
these types directly; no definition, signature, or compiler wrapper was changed.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_residue_separable`
(node `lem-sbc-stalk-normalization-trait-section-residue-separable`).
Its proof is complete relative to the imported stated dependencies.

Added one hole:
`AlgebraicGeometry.Scheme.tameRootProduct_residue_separable`
(node `lem-sbc-tame-root-product-residue-separable`), in the new module
`Sheaf.AlgebraicGeometry.Morphisms.TameRootProductResidueSeparable`.
Its proof is exactly `by sorry`. This is a decomposition, not a sorry-free proof,
and the newly introduced hole balances the closed original hole. Existing holes
under the trait-chart construction remain existing dependencies; none was edited.

The remaining statement is strictly the algebra calculation for arbitrary root
charts: it has no schemes S or C, torsor, trait, normalization, section, spreading
model, or geometric hypotheses. The original proof combines it with the existing
geometric charts and a proved descent argument. It is not the original statement
under another name or a repackaged hypothesis.

## No longer needed

No original import was removed, and the original node had no proof_deps to prune.
No existing module can be claimed globally unreachable from this delivery.
Discarded the redundant exploratory proof imports
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, whose APIs are already available
through the existing public dependencies. Retained
`Mathlib.FieldTheory.SeparableDegree`, which supplies separability transitivity.

The proof does not use the alternative section-specific chart route:
`lem-sbc-stalk-normalization-trait-section-localized-root-chart`
(`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart`),
`lem-sbc-stalk-normalization-trait-section-root-presentation`
(`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionRootPresentation`),
`lem-sbc-stalk-normalization-trait-section-chart-generic-factor`
(`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionChartGenericFactor`), or
`lem-sbc-stalk-normalization-trait-section-cyclic-data`
(`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionCyclicData`).
These were inspected but not imported; other target branches may still need them.
No new normalization-comparison or section-chart theorem was introduced.

## Where the brief, the DAG or earlier work was wrong

The original node's plan was a prose proof with empty proof_deps, even though the
library already has the needed geometric chart interface. Its plan asks to retain
an equation vanishing at the closed section. The existing trait charts do not expose
that compatibility, but it is unnecessary: standard root charts have separable
residue extensions at both zero and nonzero values of the equation. The new algebra
lemma includes both cases. This avoids reconstructing the section-specific charts.

Edge cases were checked mathematically before stating the new lemma: m=0 gives
an empty spectrum, the zero ring has no points, e=1 is the identity root algebra,
f reducing to zero makes the root nilpotent and hence zero in a residue field,
and f reducing to a nonzero element gives a nonvanishing derivative because e
is invertible. The invertibility condition is essential in positive characteristic;
without it a nonzero fibre can give a purely inseparable root extension.

The unit `sk-prop-input-spreading` has empty realized statement/step lists. Its
trait route is preserved: the proof uses the existing tame normalization charts.
No statement or definition was changed, and no forced adaptations were needed.

The local checkout lacks the untracked Stacks sources. Tags 0EYH and 0EYJ were read
on their official Stacks pages. Searches were run through msearch.py (LeanSearch
unavailable, LeanFinder and Loogle successful, grep successful), plus direct rg
in Mathlib, the source library and Sheaf. No search was invented. The ancestor
script returned None for the original node; the new node's blueprint ancestry
was traced manually through its parent node to
`sbc-thm-spreading-finite-etale-galois`.

## New nodes

`lem-sbc-tame-root-product-residue-separable` states separability of every canonical
residue extension for the spectrum map of a finite product of R[T]/(T^e-f), with
positive invertible exponents. Source: Stacks Project Tag 0EYH, the displayed local
normal form, with the residue calculation written out in the docstring and node.
The proof separates zero and nonzero fibre values; the latter can use Mathlib
`Polynomial.separable_X_pow_sub_C`. LeanFinder found only unramified local-ring
criteria, not the ramified root-chart residue theorem. There are no change records.

## Second reading by W2

1. **Interface: pass.** Read both delivered modules and diffed the original module
   against the repository. Extracted the existing theorem signature through its
   `:= by` delimiter and checked byte equality. All hypotheses, the finite-map
   premise, the closed-section point condition, and the canonical stalk-induced
   residue algebra are unchanged. No definition or public import changed. The
   original node differs only in proof, proof_deps, and proof_origin. There are no
   adapted modules or change records.

2. **Proof and axioms: pass relative to stated dependencies.** Both modules compiled
   with lcompile.py in import order, without warnings (2.4 s and 16.3 s). A scratch
   copy printed axioms for every private theorem and the original theorem. The five
   field/descent/stalk helpers use only propext, Classical.choice, and Quot.sound.
   The root-chart assembly and original theorem additionally use sorryAx from the
   explicitly open imported statements. The original module has zero sorry tokens;
   the new module has exactly one, the named tameRootProduct_residue_separable.
   No forbidden declaration or attribute occurs. ResidueSeparableAt is a concrete
   private abbreviation, not data chosen from existence; the chart witnesses are
   eliminated inside a proposition proof and do not define an arbitrary object.

3. **Remaining statement: pass as a genuine decomposition.** A prime of a finite
   product selects a factor. After passing to the base residue field, its monic
   root algebra is finite-dimensional, so a prime quotient is a field generated by
   the root. If fbar=0, the root is zero and this field is the base field. Otherwise
   the invertible exponent makes the polynomial separable; its irreducible factor
   and resulting field extension are separable. This proves the stated assertion
   for arbitrary R, without the Noetherian and regularity assumptions of the
   geometric chart source. Checked m=0, the zero ring, e=1, f=0, and nonzero f in
   positive characteristic with exponent prime to that characteristic. If
   invertibility is dropped, F_p(s)[T]/(T^p-s) supplies the inseparable obstruction.
   The docstring gives this complete argument and the new node matches it. The
   lower statement removes the entire normalization, torsor, trait, and section
   construction; it is strictly part of the original argument, not its restatement.
   Repeated searches with a different LeanFinder query, Loogle, and rg across
   Mathlib, Sheaf, and WeilConjectures found no exact replacement. Read the returned
   residue-quotient criteria and Polynomial.separable_X_pow_sub_C types: they are
   ingredients, not complete replacements. Closing the canonical spectrum/product
   identifications would require substantial additional proof work, rather than
   a few-minute application of an existing theorem.

4. **Route and pruning: pass.** Read stalk_normalization_trait_charts and the unit
   sk-prop-input-spreading. The proof uses precisely the existing trait charts and
   the lower root calculation, then residueFieldMap_comp, separability transitivity,
   pullback point lifting, separability of etale residue maps, and descent through
   an algebra homomorphism. The final algebra_ext argument checks the canonical
   stalk quotient map on residue representatives. The unused section equality
   does not change the theorem: the argument proves separability at every point.
   The trait step of the unit still passes through the tame charts of 0EYH; no
   unit step is replaced. The unit's realized lists are empty and unchanged.
   The old proof_deps was empty, so there is nothing to prune from it. All three
   added imports are proof-only and used. Existing public imports support the
   unchanged signature. No existing module is claimed pruned or unreachable.
   Independently read [Stacks 0EYH](https://stacks.math.columbia.edu/tag/0EYH)
   and [Stacks 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ) to check the chart
   source and trait route.

5. **DAG consistency: pass.** Both lean.statement records occur verbatim in the
   delivered files; proof_deps equals the union of uses in each node's proof.
   Every statement/proof dependency names an existing node or the new node of
   this delivery. The original proof steps describe the actual chart assembly
   and descent helpers. The new node has its source, full residue calculation,
   searches, creation record, blueprint ancestry, chapter/unit, and Lean record.
   Its empty proof_deps accurately records a remaining elementary algebra
   calculation with Mathlib ingredients, not an invented geometric dependency.

Changes made by the second reader: added this detailed review and two independent
search records to the new node. No Lean repair was needed. One original hole is
closed and one lower hole is added: net zero, recorded as a decomposition. Temporary
axiom-probe files were removed before delivery.
