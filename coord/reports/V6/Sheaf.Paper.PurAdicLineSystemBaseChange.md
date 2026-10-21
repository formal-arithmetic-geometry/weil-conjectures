## What changed

The unchanged theorem `CategoryTheory.purAdicLineSystem_baseChange` now has a complete
Lean assembly proof. It proves positive-stride cofinality, integral comparison naturality,
uniqueness of the normalized integral map among arbitrary set-sheaf maps, and uniqueness
of the final normalized ring/module isomorphisms. The final uniqueness proof explicitly
transports the filtered-colimit preservation of ring and additive forgetful functors
through a small model of each site; it does not assume the inverse image preserves
inverse limits.

`PurAdicFilteredColimitExists` constructs the actual varying-ring scalar action from
Mathlib's sectionwise filtered-colimit module construction. It proves the same-stage
and common-upper-bound scalar equations, restriction compatibility, and the ring and
additive sheaf-colimit universal properties after module sheafification. In particular,
filtered-colimit existence is proved rather than included in the remaining comparison
hole.

The pointwise integral comparison, localization comparison, and inverse-image comparison
of supplied filtered-colimit pairs are isolated in three separate modules. Each is a
strict part of the original argument with a source, a complete proof in words, and a new
DAG node. None restates the full theorem. Their scopes are respectively: a fixed integral
index without naturality or uniqueness; localization for arbitrary pair diagrams without
any adic tower or coefficient colimit; and comparison of given colimit pairs without
localization, towers, colimit construction, or uniqueness.

To avoid circular imports, the original data interfaces move to
`PurAdicLineSystemData` and are publicly reexported by the original module. Their names,
universes, signatures, fields, and mathematical definition bodies are unchanged. The
new data module preserves all original public imports and adds Ring.Limits and
Sites.Equivalence. Three proved sheaf-composition helpers use an explicit small model;
they are local instances only in that module. No target or source-library declaration
changes, and no other group's module is adapted.

Validation: all six delivery modules compile cleanly together with lcompile.py. The
original theorem signature was compared after whitespace normalization and is identical.
A separate importer verified that the original public records remain accessible through
only the original module. `#print axioms` for the filtered-colimit existence theorem and
all three sheaf-composition helpers lists exactly propext, Classical.choice and
Quot.sound; the full theorem still lists sorryAx, as expected from its three named gaps.
Every Lean line has at most 100 characters. Every node dependency resolves and each
proof_deps list equals the union of its proof-step uses. The original module has no
current Lean importers; its unfinished DAG parent and the unit route are retained.

## Proved and sorry left

Original holes: 1. Closed body:
`CategoryTheory.purAdicLineSystem_baseChange`
(node `lem-pur-adic-line-system-base-change`).

Added holes: 3, each exactly the proof of a named public theorem:

- `CategoryTheory.purAdicIntegralComparison_exists`
  (`lem-pur-adic-integral-comparison`).
- `CategoryTheory.purAdicLocalizationComparison_exists`
  (`lem-pur-adic-localization-comparison`).
- `CategoryTheory.purAdicFilteredColimitComparison_exists`
  (`lem-pur-adic-filtered-colimit-comparison`).

This is a decomposition, not a net hole closure or an axiom-free proof of the full
base-change theorem: one original hole is replaced by three independent comparison
holes, so the packet's raw net is -2. The remaining declarations have no sorry. In
particular, `CategoryTheory.purAdicFilteredColimit_exists` is proved, as are
`purAdicHasSheafComposeRingSets`, `purAdicHasSheafComposeModuleSets`, and
`purAdicHasSheafComposeCoefficients`. All private helpers are proved. No axiom or hollow
definition is added, and no object definition chooses arbitrary data from an unproved
existence statement. The original theorem's proof chooses only existential witnesses
inside a proposition.

## No longer needed

Removed direct private imports from the item module:

- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`
- `Mathlib.RingTheory.Localization.BaseChange`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.Paper.PurInverseImageCompatibleFreeTower`
- `Sheaf.RingTheory.ModuleLocalizationFilteredColimit`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`

The original direct import of the compatible-free-tower theorem cannot instantiate this
item's independent universes. Its mathematical local-basis argument is retained in the
pointwise integral lemma's proof plan; it is not claimed to have become irrelevant to
the library. The localization tensor, module-localization colimit and sheafification
interfaces remain in the localization lemma's proof plan. Their approved tool_uses
entries are therefore retained. The original public imports remain available through
the public data reexport, including Functor.OfSequence for interface compatibility.

The proof no longer depends on these three original nodes:

- `lem-pur-inverse-image-compatible-free-tower`: its specialized Lean universes do not
  fit this item. The new pointwise integral comparison instead records the general
  cover argument; the existing theorem and its source module remain intact.
- `lem-weil-pbc-filtered-colimit-rings-zero`: no separate ring-zero criterion is used.
  Mathlib's varying-ring filtered-colimit module construction supplies the action
  directly, including zero rings.
- `lem-weil-pbc-filtered-colimit-modules-elementwise`: its fixed-ring module criterion
  is replaced by the varying-ring `IsColimit.module`, `IsColimit.ι_smul`, and concrete
  stage-representative API used in the proved construction.

These are removed proof dependencies, not declarations deleted from the library.
No existing module is withdrawn, and no globally unreachable node is claimed pruned.
The old direct proof dependencies are replaced by the three comparison nodes and the
proved filtered-colimit existence node, with the remaining mathematical dependencies
recorded on those nodes. The target-facing parent and unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan and prior review say every hypothesis of
`pur_inverse_image_compatible_free_tower` is available. Its actual Lean declaration
requires SmallCategory sites in one universe and coefficients in its successor universe;
this item permits independent object, morphism and coefficient universes. It also uses
the concrete Kan-extension/sheafification inverse image, whereas this item supplies a
left adjoint L. Thus it cannot be applied verbatim. The new integral lemma records the
same source argument at the needed interface, using one common cover, and its proof in
words explains the coproduct-of-sheafified-representables interpretation of that cover.

The public `existsUnique_localizationInverseImageRing` requires an already supplied
algebraic inverse-image lift of the localized ring. It does not alone construct that
lift or the natural localized pair diagrams; the new localization node includes precisely
that construction, together with the existing module-localization coherence argument.
No statement is marked disputed: the missing pieces are constructions, not discovered
counterexamples.

New statements were checked against zero rings, nilpotent or unit denominators,
singleton directed diagrams, noninjective coefficient transitions, and infinite covers.
The filtered-colimit construction uses representative criteria for arbitrary filtered
transitions and does not require injectivity. The integral argument requires one cover
with bases compatible at all levels, rather than independently chosen covers. Positive
strides are used only in the proved cofinality step. No blueprint unit is bypassed.

## New nodes

`def-pur-adic-line-system-data`: the unchanged diagram and normalization records,
relocated to break the proof-import cycle, together with three proved local
sheaf-composition helpers.

`lem-pur-adic-integral-comparison`: the pointwise normalized linear isomorphism for
compatible locally based adic towers; naturality and uniqueness are proved in the parent.

`lem-pur-adic-localization-comparison`: localization of a semilinear pair diagram and its
normalized inverse-image comparison; this result has no tower or filtered-colimit data.

`lem-pur-adic-filtered-colimit-exists`: proved construction of filtered-colimit pair
sheaves with the common-upper-bound scalar action, independent of inverse image.

`lem-pur-adic-filtered-colimit-comparison`: inverse-image comparison of supplied pair
colimits, normalized on coprojections; construction and uniqueness are proved elsewhere
in this packet.

Change record: `coord/changes/pur-adic-data-interface-relocation.md`.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
