## What changed

Replaced the hole in `CategoryTheory.ringFamilyGlobalExtension_tensor_iso` by tensor-length
induction. The factor comparison is proved using the sequential-colimit model of localization,
the scalar compatibility of the fixed extension-unit map, and the existing generic two-term
complex comparison. A separate proved lemma lifts a normalized strong monoidal structure from
module sheaves to complexes using the source library's `Functor.mapCochainComplexMonoidal`.
The constant-presheaf and full extension functors are proved to preserve small colimits.

Only the item and three new modules are changed. The item's original statement and public imports
are preserved. The new proof imports are `GlobalSectionComplexMonoidal` and
`GlobalSectionLocalizationFactor`. The auxiliary `smallClosedCochainMonoidal` is the
existing total tensor structure with its instance requirements cached; it changes no tensor data
and is not registered as a global instance.

Validation: `lcompile.py --all` compiles all four modules without warnings or errors. Fresh
compiles of the complex lift and item took approximately 23 and 26 seconds, respectively;
all files stay within the 60-second limit. No existing shared module or signature is modified.

## Proved and sorry left

Original hole closed: `CategoryTheory.ringFamilyGlobalExtension_tensor_iso` (one of one).
New hole added: `CategoryTheory.ringFamilyGlobalExtension_module_monoidal`, node
`lem-weil-pbc-global-section-module-monoidal` (one). This is a decomposition, with net zero
holes closed. The remaining statement concerns module sheaves only: it has no localization,
complex, list, differential, or augmentation of a tensor complex. The localization-colimit
comparison, complex lift, and tensor induction are actual proofs, rather than another name
for the original obligation.

Also proved: `CategoryTheory.ringFamilyGlobalExtension_preservesColimits`,
`CategoryTheory.ringFamilyGlobalExtension_complex_monoidal`, and
`CategoryTheory.ringFamilyGlobalExtension_localization_factor`. The only `sorry` in this
packet is the module-level normalized monoidal structure named above.

## No longer needed

The item's planned dependency `lem-weil-pbc-localization-base-change` is replaced by the
already proved sequential-colimit model from `Sheaf.CategoryTheory.RingedKoszulFactorColimit`.
No original public import is removed. `RingTensorCechCoordinates` supplies definitions;
its coordinate-isomorphism theorem is not used. No existing module is withdrawn, and no
adopted source declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The DAG describes a sectionwise localization-base-change calculation. Its conclusion follows
instead from preservation of the scalar multiplication sequence and its colimit; this also
makes compatibility with the specified localization unit explicit. Zero sections, repeated
sections, zero rings, empty lists, and empty sites require no extra hypotheses. The source
library already supplies the general lift of an additive monoidal functor to complexes.

The new statements preserve the prescribed unit map. Merely asserting an unspecified
isomorphism between the unit objects would not establish the augmentation equation.

## New nodes

`lem-weil-pbc-global-section-module-monoidal` records precisely the module-level tensor and
unit constraint still to be proved, together with the proved colimit-preservation declaration.
Its proof in words gives the balanced tensor formulas, their inverse, restriction
compatibility, sheafification, coherence, and equality with the existing fixed unit map.

`lem-weil-pbc-global-section-complex-monoidal` records the proved lift to complexes and its
normalization on the single complex. It uses the existing source-library construction.

`lem-weil-pbc-global-section-localization-factor` records the proved single-factor comparison.
It uses the existing module-level localization cocone and generic two-term comparison via
proof imports with `import all`; both helpers are already proved. Its colimit argument is
independent of tensor lists and the complex tensorator.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
