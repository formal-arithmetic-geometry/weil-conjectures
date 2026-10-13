## What changed
Proved `AlgebraicGeometry.Scheme.affine_open_supported_model_torsion` without changing
its signature. Exact affine sheafification and localization uniqueness identify the
sheafification of each module homology with restricted shifted cohomology. Added and
fully proved `AlgebraicGeometry.Scheme.affine_restricted_homology_support` in
`Sheaf.AlgebraicGeometry.AffineRestrictedHomologySupport` to transport this ordinary
sheaf identification to prime support. Mathlib localization criteria then extract an
annihilating power for each element. Added a proved private localization helper.
Updated both DAG proof records to match this route. No statements or definitions changed.

## Proved and sorry left
Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_open_supported_model_torsion`
(node `new-affine-open-supported-model-torsion`).
Also proved the new theorem
`AlgebraicGeometry.Scheme.affine_restricted_homology_support`
(node `new-affine-restricted-homology-support`) and the private helper
`torsion_of_localized_subsingleton`. No sorry remains in either delivered module;
no holes were added. This is a proof, not a decomposition.

## No longer needed
Removed proof imports and dependencies:
- `Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison`
  (`lem-pc-open-derived-restriction-comparison`): the support lemma uses exact
  restriction and the stalk comparison directly.
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
  (`lem-pc-affine-qcoh-derived-equivalence`).
- `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`
  (`lem-pc-affine-localized-site-derived-transport`).
- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`
  (`new-affine-derived-tilde-homology-comparison`).
The last three are bypassed by exactness of the explicit affine sheafification
functor and `Localization.liftNatIso`, followed by its homology comparison. These
nodes are not needed by this proof; other library users may still need them. No
unit statement or realized unit proof step was bypassed: the unit record has no
realized attachment to this node, and the affine support argument is retained.

## Where the brief, the DAG or earlier work was wrong
No false statement was found. The DAG's derived-equivalence route was longer than
necessary. The exact affine sheafification definition itself provides the required
homology comparison. The explicit source files under the source checkout contain
the generic exact-functor and stalk tools required for the shorter argument.

## New nodes
`new-affine-restricted-homology-support`, module
`Sheaf.AlgebraicGeometry.AffineRestrictedHomologySupport`, is a fully proved support
comparison for an ordinary module with a given cohomology sheaf isomorphism. It
has no derived module model, no functor factorization hypothesis, and no torsion
conclusion. Its proof handles arbitrary degrees and shifts without finite
generation and works for empty affine opens, zero rings, zero modules and f=0.
No change records were needed.

## Second reading by J2
1. Compared the delivered target module with the repository version. The theorem
   signature is byte-for-byte unchanged; only proof text and proof-only imports were
   changed. Verdict: pass.
2. Compiled both delivered modules and checked that there are no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof uses
   localization and exactness lemmas and introduces no hollow definitions. Verdict:
   pass.
3. Checked the added support theorem against its edge cases (empty affine opens,
   zero rings/modules, f = 0, and units) and against existing declarations; it is a
   strict support comparison needed by the target and is not a restatement of it.
   Independent grep, LeanFinder, and Loogle searches found the component criteria
   `LocalizedModule.subsingleton_iff_disjoint`, `Module.notMem_support_iff`, and
   `IsLocalizedModule.eq_zero_iff`, rather than an existing sheaf comparison theorem.
   Verdict: pass.
4. Confirmed the proof follows the exact affine sheafification route, retains the
   unit's affine support argument, and removes only dependencies unused by the new
   proof. Verdict: pass.
5. Compared both DAG records with the Lean declarations, proof steps, and imports;
   the new node has the required source, proof, search, and Lean metadata. Verdict:
   pass.

Changed only this report while second-reading; no Lean statements or definitions
needed repair.

Read [Stacks Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ), the affine
cohomology support paragraph, and [Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0),
the exact tilde/homology comparison. The proof uses only elementwise annihilation,
so neither finite generation nor a uniform exponent is silently assumed. In the
support lemma, `f.property` and `basicOpen_res` justify the global/local scalar
comparison, `restrictStalkNatIso` justifies both stalk transports, and `shiftIso`
uses degree `k + i`; these are the necessary identifications before applying
the localization criteria.
