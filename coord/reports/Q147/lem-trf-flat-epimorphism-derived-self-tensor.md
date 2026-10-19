## Worker report

The module `Sheaf.Algebra.Homology.FlatSurjectionDerivedSelfTensor` states
`DerivedCategory.isIso_derivedSelfTensorMultiplication_of_flat_surjective`.
Its sole theorem has proof `sorry`. The helper
`DerivedCategory.derivedSelfTensorMultiplication` constructs the actual canonical map;
its data contains no postponed proof. Both declarations belong to this item and are
listed in `lean.declarations`. No new nodes or dependency repairs are needed.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- Commutative rings A and B: `{A B : Type u} [CommRing A] [CommRing B]`.
  A common ambient universe is available for any two rings; no nontriviality,
  characteristic, finiteness, or Noetherian condition is imposed.
- The ring homomorphism A to B is `(f : A →+* B)`.
- Surjectivity is `(hf : Function.Surjective f)`.
- Flatness of B as an A-module through f is `(hflat : f.Flat)`, exactly
  `RingHom.Flat` from the recorded flat-ring-map node, whose definition installs
  `f.toAlgebra` and asks for `Module.Flat A B`.
- The derived categories are Mathlib `DerivedCategory (ModuleCat.{u} A)` and
  `DerivedCategory (ModuleCat.{u} B)`, with explicit localization-size binders
  `[HasDerivedCategory.{wA} (ModuleCat.{u} A)]` and
  `[HasDerivedCategory.{wB} (ModuleCat.{u} B)]`. These implement the chosen sizes
  of the recorded abstract-derived-category node and add no mathematical restriction.
- B as an A-module is `(ModuleCat.restrictScalars f).obj (ModuleCat.of B B)`.
  Its degree-zero complex is `HomologicalComplex.single ... (.up ℤ) 0` applied
  to that module. The second factor is the corresponding B-module single complex.
- The source of the canonical multiplication is the object obtained by applying
  `Classical.choose (exists_derivedTensor_second_factor_functor f).2` at that
  second complex and at `Q.obj` of the first complex. Thus it is precisely
  `B ⊗ᴸ_A B` for the dependency's fixed-second-factor derived tensor.
- The target is `Q.obj` of the degree-zero B-module complex, namely `B[0]` in D(B).
- The word canonical is implemented by the helper's body: take the published
  comparison ε of that same chosen derived functor, compose with `Q.map` of
  `mapBifunctorSingle₁Iso` followed by `singleMapHomologicalComplex`, and then
  apply the single functor to the left unitor followed by
  `(ModuleCat.extendRestrictScalarsAdj f).counit.app (ModuleCat.of B B)`.
  The mixed tensor target has underlying presentation `B ⊗_B (B ⊗_A B)`;
  the unitor and counit send `d ⊗ (c ⊗ b)` to `dcb`.
  The outer B and the c factor come from the node's second factor, so the
  B-action is exactly the second-factor action. Commutativity identifies cb with bc.
  There is no arbitrary map, isomorphism, or additional representative assumption.
- The conclusion is `IsIso (derivedSelfTensorMultiplication f)`, asserting
  invertibility of that very arrow, rather than existence of some isomorphism.

The selected functor and comparison are taken together from the recorded existence
statement. This is the permitted choice of a universal-property object: the
left-derived-functor property determines the pair up to its unique compatible
isomorphism. The same selection is used in the type and body. No new derived
functor or tensor predicate is introduced. The complete four-step natural-language
proof from the node is included in the theorem docstring.

Recorded dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  Read the size convention, localization functor, and localization instance.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat` in
  `Mathlib.RingTheory.RingHom.Flat`, including its full defining expression.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, and `TensorProduct.lift` and
  `TensorProduct.ext'` from `Mathlib.LinearAlgebra.TensorProduct.Basic`.
  The module uses this existing tensor through `ModuleCat.mixedTensor` and
  the extension/restriction counit, whose lift construction was read in full.
- `lem-pc-derived-tensor-second-factor-functor`:
  `DerivedCategory.exists_derivedTensor_second_factor_functor` in
  `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`. Read the complete
  declaration, including the chosen ε, its left-derived property, and its K-flat
  computation clause. Its `ModuleCat.mixedTensor` is from
  `Sheaf.Algebra.Homology.MixedTotalTensor`; its action and tensor order were checked.

Proof dependencies are imported as well: `Module.Flat.rTensor_exact` and
`Module.Flat.lTensor_exact` in `Mathlib.RingTheory.Flat.Basic`, and
`CategoryTheory.MorphismProperty.kFlat` in
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`.
The additional canonical single-complex isomorphisms are from
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` and
`Mathlib.Algebra.Homology.Additive`. Their full signatures and construction were read.

Source reading: `literature/stacks-project/cotangent.tex`, lemma-when-zero
(Tag 08R2), explicitly applies the surjective-flat case to `B ⊗_A B → B`.
`literature/stacks-project/more-algebra.tex`, Section 06Y5 immediately before
lemma-derived-base-change (Tag 06Y6), defines the functor D(A) to D(B) by total
mixed tensor and K-flat resolutions. This is the exact model used here.

Edge cases checked before writing:

- The identity map: flat and surjective; ordinary multiplication and its inverse
  are the unit tensor identifications, so the derived multiplication is invertible.
- A map to the zero ring, including the zero-ring identity: B[0] is zero, and
  its self-tensor and canonical multiplication have the same zero model.
  No `Nontrivial` binder excludes this case.
- Projection `k × k → k`: a flat surjection; the tensor multiplication and
  inverse `c ↦ 1 ⊗ c` give the expected answer even with nonzero kernel.
- `ℤ → ℤ/2`: surjective but not flat; the omitted flatness would leave higher
  self-Tor. A field extension is flat but usually not surjective; its ordinary
  multiplication is not generally injective. Neither hypothesis is hollow.
- No boundedness is imposed beyond the intrinsic degree-zero inputs; arbitrary
  derived-category morphism universes wA and wB are explicitly retained.

Searches for existing notions and statements:

- `msearch.py leanfinder`: "A flat surjective homomorphism of commutative rings has
  derived self tensor multiplication isomorphic to the ring" returned eight hits,
  including `Module.FaithfullyFlat.surjective_of_tensorProduct`,
  `LinearMap.kerLTensorEquivOfSurjective`, and formal smoothness/differentials results.
  None states invertibility of the canonical derived multiplication.
- `msearch.py loogle`: "DerivedCategory, TensorProduct, Module.Flat" returned no hits.
- `msearch.py grep`: "derived.*[Tt]ensor|[Tt]ensor.*derived|mul._bijective_of_surjective"
  in Mathlib `Algebra` returned no hits.
- `msearch.py leansearch`: "For a flat surjective ring map the canonical derived
  self tensor multiplication is an isomorphism" returned eight hits, notably
  `TensorProduct.lid'`, `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`,
  and `RingHom.Flat`. These supply ordinary tensor or flatness, not this derived arrow.
- Direct `rg` searches of `WeilConjectures` and `lean/Sheaf` for the item id,
  derived multiplication/self-tensor, mixed tensor, and second-factor derived tensor
  found the recorded mixed tensor construction and other specialized sheaf
  multiplications, but no exact theorem for a flat surjective commutative ring map.
  The existing `changeOfRingsFixedTensor` and its comparison use the same explicit
  selection from the recorded theorem; no duplicate named choice is added here.
- Direct searches of Mathlib tensor-product, homology, and ChangeOfRings files
  found the canonical counit and single-complex isomorphisms used for the helper.
- Exact searches of Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for both proposed declaration names found no collision.

Validation: `scompile.py Q147 lem-trf-flat-epimorphism-derived-self-tensor` compiled
this file successfully as both a sandbox module (6.2 seconds) and its real library
module (7.0 seconds), with no compiler diagnostics. The JSON changes only `lean`.
No statement dispute or node fault was found. No independent second reader was
started, in accordance with the dispatcher's direct-delivery instructions.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
