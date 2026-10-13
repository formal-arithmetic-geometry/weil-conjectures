## What changed

Proved `AlgebraicGeometry.koszul_supported_augmentation_eventually_zero` in
`Sheaf.AlgebraicGeometry.KoszulSupportedAugmentationVanishing`, with its existing
signature and public imports unchanged. Added the proof-only import
`Mathlib.CategoryTheory.Localization.HomEquiv` and two fully proved private helpers.

`supported_hom_colimit` obtains the comparison cocone from
`affine_perfect_open_represent_cohomology` in the standard localizations. It transports
the zero restriction using `mapDerivedCategoryFactors` and localization uniqueness,
and explicitly identifies restriction to the scheme of the open with the composite
through `Scheme.Modules.overEquiv`. The resulting Hom target is a singleton.
The natural localization Hom equivalences transport the cocone across possibly
different morphism universes using `Functor.CoconeTypes`; its point is then identified
with `PUnit` in the requested universe.

`augmentation_compatibility` transports the existing comparison theorem's augmentation
identity to the given localization. The main proof shifts the target by `-n`, proves
quasi-coherence and zero restriction of that shift, uses filtered-colimit equality to
obtain a later index, applies augmentation compatibility, and moves the shift back
using the shift adjunction.

Sources read: Stacks Equation the project server, Tag 08DC
(https://stacks.math.columbia.edu/tag/08DC), and Proposition 36.9.5, Tag 08DD
(https://stacks.math.columbia.edu/tag/08DD). The assigned node and its dependency's
Lean interface were checked. The unit has no realized statement or step nodes affected
by this proof, and its route is preserved.

Validation: the complete assigned module compiles through `lcompile.py` without warnings.
The argument is uniform for the empty family, the zero ring, zero target, and arbitrary
integer shifts; it introduces no nonemptiness, regularity, or universe assumptions.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.koszul_supported_augmentation_eventually_zero`
(node `lem-pc-koszul-supported-augmentation-vanishing`).

No `sorry` remains in the delivered module; no new holes or modules are added.
Both private helpers are proved. This is one hole closed and zero holes added,
not a decomposition into new unproved statements. The proof uses the existing
`affine_perfect_open_represent_cohomology`, which now reduces to the existing
`affine_perfect_open_represent_cohomology_core` and
`affine_perfect_open_represent_cohomology_colimit`; their unfinished proofs remain
outside this module and are not claimed closed by this delivery.

## No longer needed

None. All original imports and the planned dependency
`lem-sc-affine-perfect-open-represent-cohomology` remain needed. No DAG node or module
is pruned. The additional localization import is used by both private helpers.
The explicit comparison formula is unnecessary: its zero Hom target alone establishes
equality of the two images in the colimit.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The extra localization
instances required by the comparison theorem are supplied only inside the proof in
standard localizations, with explicit transport back to the original instances and
morphism universe; they have not been added to the public signature.

## Second reading by R4

1. Compared the sole delivered module against the repository using `diff`, and
   compared the complete existing theorem signature byte for byte. Verdict: unchanged
   universes, ring and finite-family parameters, localization instances, open equality,
   quasi-coherence, zero restriction, integer shift, morphism and eventual-zero conclusion.
   No definitions or public imports changed, and no change record is required. Restored
   the existing declaration docstring rather than changing that API documentation.
2. Compiled the full module and a scratch copy printing axioms of both private helpers
   and the public theorem, using only `lcompile.py`. Verdict: clean compilation;
   each uses only `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`.
   There is no local `sorry` or forbidden declaration. The chosen complex is Mathlib's
   proved essentially-surjective preimage, with an explicit isomorphism to E; it is not
   data obtained from an unproved arbitrary existence assertion. Local cocone witnesses
   are used solely to prove a proposition, with no new data definition.
3. No statements were split off and no holes were added. Read both fully proved private
   helpers: `supported_hom_colimit` transfers restriction through the localized-site
   equivalence and checks Hom-diagram transition naturality explicitly;
   `augmentation_compatibility` conjugates the compatibility equation through the
   localization natural isomorphism. Verdict: neither adds an assumption to the public
   theorem. Empty Fin 0, the zero ring, E = 0, zero or invertible entries and positive,
   negative or zero shifts require no special exclusion.
4. Read `KoszulOpenSystem`, the comparison theorem and its core interface; searched
   Sheaf and upstream WeilConjectures with augmentation/vanishing and Koszul terms.
   An independent LeanFinder search for supported derived maps killed by power tail
   augmentations returned degree-support/projective/injective vanishing lemmas, which
   do not give spatial-support vanishing for an arbitrary unbounded quasi-coherent E.
   Verdict: no applicable shorter theorem found. All imports are used: the system in
   signatures, comparison and localization transport in helpers, and filtered Types
   equality in the final proof. No old proof dependency is removed. Read the unit JSON:
   `sk-thm-picard-duality` has empty realized statement and step node lists; its route
   is preserved. The cited literature files are not present in this remote checkout;
   the review checks the existing source-backed interfaces, without claiming a new
   source reading or changing their statements.
5. Read the item node and its existing proof dependency. Verdict: the original node
   route needed a wording update: the implemented proof uses the singleton target of
   the colimit rather than its explicit comparison formula. Updated only `proof` and
   `proof_origin`, retaining `proof_deps` and all statement/interface fields. The second
   step now explicitly cites the comparison theorem for augmentation compatibility.

Changed in this reading: restored the existing theorem docstring, synchronized the
DAG proof route with singleton-colimit transport, corrected the report's attribution
of inherited holes to the comparison's core and colimit theorems, and added this review.
No Lean proof repair was needed; one original hole is closed and zero are added.
