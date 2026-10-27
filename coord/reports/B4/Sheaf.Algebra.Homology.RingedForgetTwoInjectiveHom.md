## What changed

Reduced AlgebraicGeometry.ProEtaleWeilSheaf.native_two_injective_hom_model to the separate
native and underlying derived-representative constructions. The assembly now constructs the
standard source and target models, proves the coefficient interpretation, supplies the sign
isomorphism and its naturality, applies ringedHomComplexComparison with the actual underlying
internal-Hom identity, and applies kInjectiveHomComparisonDescent with both localization legs.
The existing ringed_forget_two_injective_hom proof and all original signatures stay unchanged.

StandardBifunctorHomModel constructs the simultaneous native Hom functor. Its explicit model
has the native complex and projections (-1)^(n*p) times the native projections. Product
universality, differential and map equations are proved. This allows the sign chain map to be
the identity while retaining exactly the required signed projection formula; no arbitrary
product or unproved data are selected. Each representative extension is determined by its
natural representative maps up to their unique compatible natural isomorphism.

Added private proof imports of RingedHomComplexComparison, KInjectiveHomComparisonDescent,
NativeStandardHomRepresentatives and UnderlyingStandardHomRepresentatives. Updated the item
node's proof, proof_deps and proof_origin to match. Change record:
coord/changes/B4-native-standard-hom-model.md.

Validation: all four Lean modules compiled through lcompile.py. The final item compilation
completed successfully in 48.4 seconds, using the three compiled new modules.

## Proved and sorry left

Closed the item's one textual hole, native_two_injective_hom_model, by decomposition.
The existing ringed_forget_two_injective_hom theorem remains proved. The explicit standard
model, its product/differential/map fields, the coefficient comparison, both sign fields,
and the chain/derived forgetting assembly have complete Lean proofs.

Added two holes, each the whole proof of a public theorem in its own module:

- AlgebraicGeometry.ProEtaleWeilSheaf.nativeStandardHomRepresentatives
  (lem-sf-native-standard-hom-representatives): source derived extension and native slice
  normalization only; it asserts no coefficient, sign construction or forgetting comparison.
- AlgebraicGeometry.ProEtaleWeilSheaf.underlyingStandardHomRepresentatives
  (lem-sf-underlying-standard-hom-representatives): underlying derived representatives only;
  it asserts no Weil structure, native slice comparison or forgetting comparison.

This is a decomposition: one hole closed, two holes added, zero holes remain in the item.
It is not claimed as a net reduction of the sorry ledger. Both new lemmas include full
proof sketches, sources and DAG attachments.

## No longer needed

No existing module is withdrawn and no original public import is removed. There are no
unused new private imports. No globally pruned node or module is claimed.

The native specialization does not need to transport through the twisted action ringed-site
presentation, nor the triangulated-exactness theorem for bifunctorHomHomotopyFunctor: it works
directly in the actual native and underlying module categories. The native proof steps no
longer cite lem-sf-twisted-action-ringed-site or lem-sf-bifunctor-homotopy-exact directly.
Their relevant constructions remain in existing statement dependencies and other modules;
this delivery does not remove those declarations or claim them globally unnecessary.
The concrete forgetKInjective proof already belongs to def-sf-ringed-two-injective-models;
the native assembly does not reprove the exact orbit-adjoint criterion independently.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. The remaining native proof requires a genuine extension
in the second variable and representative maps for arbitrary source complexes. The existing
bifunctorRHomOfComplexObjIso only supplies the K-injective source comparison for a fixed target
slice, so it alone does not give those two-variable data. The two split lemmas isolate this
missing part instead of repeating the complete native theorem.

The unit record has empty realized statement/step lists. The construction retains the native
internal-Hom paragraph and its sign and forgetting requirements. Edge cases checked: empty
scheme, zero and acyclic sources, arbitrary unbounded complexes, negative n and p, and
characteristic two in the generic sign model. Signs are integer units, so cancellation uses
only their square being one. The coefficient proof works locally on every test space and
requires no compactness of that space.

## New nodes

- def-sf-standard-bifunctor-hom-model: the explicit native complex bifunctor with rescaled
  product projections and proved standard differential/map equations. No hole.
- lem-sf-native-standard-hom-representatives: native universal derived extension with natural
  arbitrary-source/K-injective-target representatives and the native slice normalization.
- lem-sf-underlying-standard-hom-representatives: the corresponding ordinary module derived
  extension, without native normalization or forgetting data.

Blueprint searches for K-injective and sign normalization found no duplicate statement;
existing rowIso and sliceModel helpers are private in a module importing this item and assume
its model. Mathlib searches are recorded in each new node. No unit or chapter record changes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
