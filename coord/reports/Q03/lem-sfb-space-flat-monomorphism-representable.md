## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatMonomorphismRepresentable` states
`AlgebraicGeometry.AlgebraicSpace.flat_monomorphism_representable` with its whole proof
postponed by `sorry`. No definitions, helper statements, dependency repairs, new nodes,
or statement corrections are introduced. The item's only changed field is `lean`.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`, lemma-flat-case,
Tag 0B8A, attributed to David Rydh, including its whole proof. Its assertion is exactly
that a flat monomorphism of algebraic spaces is representable by schemes. The module's
docstring records all six steps of the accepted DAG proof, including its refinement of
fpqc descent through the existing open-immersion descent node.

Clause correspondence:

- Base scheme: `{S : Scheme.{u}}`.
- Algebraic spaces over that base: `{X Y : AlgebraicSpace S}`. The existing full
  subcategory bundles the fppf sheaf, representable diagonal, and surjective étale atlas.
- Size convention: explicit `universe u`; the existing definition uses `Scheme.{u}`,
  the big site of `Over S`, and `Type u`-valued sheaves. All scheme tests and
  representing schemes are in this same convention, with no extra universe restriction.
- Morphism over the base: `(f : X ⟶ Y)` is a morphism of the existing full subcategory,
  hence a natural transformation of fppf sheaves on `Over S`.
- Flatness: `(hf : MapIsFlat f)`. This unfolds to `MapIsLocally (@Flat) f`, exactly
  the compatible representable étale scheme-chart test in the dependency node.
- Monomorphism in the node's explicitly stated meaning:
  `(hmono : ∀ H : Over S, Function.Injective (f.hom.hom.app (op H)))`.
  Here `f.hom` is the underlying sheaf morphism, and its `.hom` is the underlying
  natural transformation. Its component at `op H` is the actual section map X(H) → Y(H).
- Conclusion: `IsRepresentable f.hom.hom`. The recorded dependency definition unfolds
  to `IsRepresentableWith ⊤`, universally quantifying over every `T : Over S` and
  every `a : yoneda.obj T ⟶ Y.obj.obj`, and giving `U : Over S`, `p : U ⟶ T`,
  and `q : yoneda.obj U ⟶ X.obj.obj` with
  `IsPullback q (yoneda.map p) f.hom.hom a`. This is precisely representation of
  X ×_Y h_T by the S-scheme U. The property `⊤` adds no condition on the projection.
  Presheaf pullbacks of these sheaves compute the sheaf fibre product; the existing
  fibre-product dependency gives its algebraic-space structure. No surjectivity,
  finite type, finite presentation, quasi-compactness, or open-immersion conclusion
  is imposed on f.
- The finite-type chart convention in the node is contextual, not an assumption:
  its recorded Mathlib module is publicly imported, and the existing
  `MapIsFiniteType` retains precisely quasi-compactness and its chart test. The
  theorem does not use or assume this property.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentable`, `IsRepresentableWith`, `IsAlgebraicSpace`.
- `def-weil-size-convention` is a metatheoretic convention; its record explicitly
  supplies no module or declaration. The theorem states its universe explicitly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, `MapIsFlat`; also read the
  module's other predicates, including `MapIsFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and its recorded quasi-compactness
  declaration `AlgebraicGeometry.QuasiCompact` in `Morphisms.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, `etale_fibreProduct_isScheme`.

Proof-only imports preserve the stated proof plan: AlgebraicSpaceFlatProperFpLocality,
AlgebraicSpaceAffineAtlasOpenCover, AlgebraicSpacePointOpenCalculus,
SpaceQuasiCompactAffineTests; and Mathlib Morphisms.Affine, Morphisms.Separated,
Limits, Morphisms.UniversallyOpen (`Flat.generalizingMap`), and Sites.Fpqc
(`Scheme.fpqcPrecoverage`). These are ordinary imports. The following proof nodes
have neither a Lean record nor a Mathlib match in the read repository, so their
modules cannot yet be imported: `lem-sfb-space-largest-schematic-open`,
`lem-sfb-space-qcqs-permanence`, `lem-sfb-space-schemehood-local-ring-test`, and
`lem-sfb-space-fpqc-open-immersion-descent`. They are proof dependencies only;
no missing notion is needed to state this theorem. No import cycle is introduced.

Edge cases checked before writing:

- An empty source remains permitted, and its empty scheme fibre products are
  representable. No nonemptiness assumption enters either binder.
- An empty base or target is allowed by the existing algebraic-space definition.
- Identity maps satisfy the two hypotheses and their tests are represented by T.
- Non-quasi-compact sources are allowed, for example the identity on an infinite
  disjoint union of copies of Spec(k). Non-quasi-compact morphisms are also allowed:
  take the open immersion D(I) → Spec(k[x₁,x₂,…]), where I is generated by all the
  variables. No finite subset of the standard opens D(xᵢ) covers D(I), so that
  immersion is not quasi-compact. The conclusion asks only representability.
- The flat monomorphism Spec(Q) → Spec(Z) is allowed: the theorem does not assert
  that its image is open and does not add a local finite presentation hypothesis.
- Every S-scheme test H and T is quantified, not only affine or field-valued tests.
  No independent smaller test universe, characteristic, Noetherianity, or
  separatedness hypothesis excludes cases.

Searches for an existing declaration (2026-10-24):

- `msearch.py leanfinder`, query `A flat monomorphism of algebraic spaces is
  representable by schemes`: 8 results, including scheme-only
  `IsOpenImmersion.of_flat_of_mono` and `Flat.isIso_of_surjective_of_mono`.
- `msearch.py loogle`, query `AlgebraicGeometry.Flat, CategoryTheory.Mono`:
  6 results, the same two scheme-only candidates and scheme pushout-section lemmas.
- `msearch.py leansearch`, query `Flat monomorphisms of algebraic spaces are
  representable by schemes`: 8 results. The scheme-only flat-monomorphism results
  and `Scheme.LocalRepresentability.isRepresentable` do not state this theorem.
- `msearch.py grep`, query `flat.*mono|mono.*flat|AlgebraicSpace`, subdirectory
  `AlgebraicGeometry`: 11 hits, primarily Morphisms.Flat and Morphisms.FlatMono.
  The former is scheme flatness; the latter assumes sources already schemes and
  adds finite presentation or quasi-compactness plus surjectivity.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, by the item id and by
  flat/monomorphism/representability combinations: no exact theorem.
  `FlatMonomorphismLocalStructure.lean` was opened: its theorem concerns schemes,
  assumes quasi-compactness and gives local structure, so is not this result.
  The proposed declaration names were also searched in those trees and
  `dag/lean_names_upstream.json`: no name collision. The upstream item-id search
  had no hit.

No node fault or disputed statement was found. The source and accepted DAG statement
agree, and all statement dependencies have usable interfaces.

Validation: `scompile.py Q03 lem-sfb-space-flat-monomorphism-representable` on the
single delivered module succeeded in both sandbox and library mode (1.6 seconds
for each); there were no errors or unexpected warnings. The file has no line over
100 characters, no auto-bound implicit variables, and one named theorem with
`sorry` as its whole proof.

## Second reading by Q03

I reread the item and completed file, checking each binder against the node and the
full definitions of MapIsFlat and IsRepresentable. The section map is the component
of f.hom.hom, rather than the point-class map: this retains precisely the node's
monomorphy assumption on every S-scheme. The conclusion quantifies over all scheme
tests and maps to Y and supplies a representing S-scheme through an actual pullback
square. It adds no projection property. The theorem makes no finite-type assumption
and no claim that f is an open immersion. I found no mismatch requiring a change.
This is the author's second pass, not an independent agent review: the dispatcher
explicitly forbids starting other agents and assigns independent review to the
maintainer after delivery.
