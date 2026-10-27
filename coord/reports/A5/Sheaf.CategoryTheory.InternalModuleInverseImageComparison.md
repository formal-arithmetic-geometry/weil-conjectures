## What changed

Completed both remaining proof holes in
`Sheaf.CategoryTheory.InternalModuleInverseImageComparison`.

The private tensor extension is constructed using `TensorProduct.liftAddHom`,
the sheafification adjunction, and the inverse canonical tensor comparison.
The unit extension is constructed from the integer multiples of a compatible
section. Uniqueness tests descend through sheafification; the proof never assumes
arbitrary sections of a sheafified tensor are globally pure tensors.

Finite-product transport of the universal pairing is separately additive by
`AbelianInverseImagePresentation.map_add`. Its tensor extension satisfies naturality,
associativity, both unit laws, and braiding compatibility. Testing normalization on
the universal product and terminal sheaf proves uniqueness of the lax structure.
This proves `directLax_existsUnique`.

For the inverse image, the proof identifies the underlying adjunct of a map
using the given `unit_eq`. Applying injectivity of the set adjunction to the
universal pairing and integer-one maps gives the actual oplax mate equations.
The mate graph equations follow directly from tensor/unit normalization; no
equality of complete lax structures is needed for that calculation.
The previously constructed normalized maps are two-sided inverses of these mates:
one composite is tested on pure tensor pairings, the other by the lifted abelian
adjunction and set-adjunction injectivity. Inverting the mate and checking braiding
then proves `inverseBraided_existsUnique`, including uniqueness.

The ring, semilinear module, unbounded complex and localization comparison is
preserved. Private constructors assemble a module isomorphism from an additive,
linear underlying isomorphism, and obtain the complex comparison from a natural
isomorphism of functors preserving zero morphisms. These generic proofs keep the
large reconstructed module and localization structures out of elaboration.
Generic graph-comparison lemmas reuse the additive and bilinear transport arguments
for both rings and modules. Right additivity follows from left additivity and
symmetry. Right-unit coherence follows from left-unit coherence and braiding,
removing the duplicate right-unit section calculation and its two private helpers.
Triple tensor extensionality uses the monoidal local-equivalence property.
The naturality proof composes four commutative squares before evaluating on sections. The private `terminalSource` uses the inverse terminal
comparison directly, avoiding the expensive auxiliary `uniqueUpToIso` construction.
Both definitions select the unique section of the same terminal sheaf.
All existing public statements and definition bodies are unchanged. The node's proof and proof dependencies record the
actual direct tensor-extension route. Private irreducibility attributes and
transparency controls prevent elaboration from unfolding full sheafification
constructions during coherence checks. Change record:
`coord/changes/internal-module-inverse-image-normalized-structures-A5.md`.

## Proved and sorry left

Closed two of two existing holes:

- `CategoryTheory.InternalModuleInverseImage.directLax_existsUnique`.
- `CategoryTheory.InternalModuleInverseImage.inverseBraided_existsUnique`.

Both belong to `lem-sfb-internal-module-inverse-image-comparison`.
No holes added or split off. No `sorry` remains in the item or any added module
(there are no added modules). The existing
`CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison`
continues to be proved from these now-proved existence-and-uniqueness statements.
This claim is local to the item; imported declarations may retain their own holes.

## No longer needed

Removed redundant imports `Sheaf.CategoryTheory.SheafTensor` and
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. The retained imports already supply
the interfaces used here; the proof does not use the closed-tensor existence
theorems or the filtered-colimit API. No modules withdrawn.

Removed proof dependency `lem-pc-sites-sheaf-tensor-bilinear-universal`, whose module
is `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
The proof constructs the integer-tensor universal extension directly for abelian
sheaves via Mathlib's tensor and sheafification adjunction; conversion to the
general ring-module sheaf tensor interface is unnecessary. Its obsolete top-level
tool approval is removed from this node. This does not withdraw the source module
or claim it is unused by other targets.

Removed proof dependency `lem-weil-pbc-adjunction-lifts-abelian-group-objects`
(Mathlib `CategoryTheory.Adjunction.mapCommGrp`). The theorem already receives the
lifted adjunction and its underlying unit equation; `underlying_adjunct` derives
the precise compatibility needed directly. No additional abstract group-object
lifting theorem is required. The node now explicitly cites the existing
`def-trf-abelian-inverse-image-presentation` used by the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit-route error was found. The planned general
module-sheaf tensor and abstract group-object adjunction interfaces were more
general than required by the hypotheses of this item. The proof follows the same
six node steps with direct integer-tensor constructions instead.

Sources checked: Stacks `sites-modules.tex`, `lemma-pullback-module` (03D2),
`section-tensor-product` (03EK), `lemma-tensor-product-pullback` (03EL), and
`sites.tex`, `proposition-functoriality-algebraic-structures-topoi` (00YV).
The proof works without points or flatness hypotheses and for arbitrary independent
site universes. Its component identities include zero sheaves and the empty site;
complex comparisons remain valid in every integer degree without boundedness.
No new statement is left for a later worker.

Validation: the complete proof compiled through `lcompile.py` in 47.5 seconds
before the final mate simplification. The simplified construction through
`inverseBraided_existsUnique` compiled in 38.9 seconds; its two whitespace warnings
have been removed. The direct-image theorem separately passed `#print axioms`,
showing only `propext`, `Classical.choice`, and `Quot.sound`. Delivery runs the
final whole-file axiom and packet checks.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
