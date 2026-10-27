## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeFibreSchemeNeighbourhood` states
`AlgebraicGeometry.AlgebraicSpace.finiteLocallyFree_fibre_scheme_neighbourhood_iff`.
Its sole proof is `sorry`; it introduces no definitions. The statement matches the node
and Stacks Project, Decent Spaces, Tag 0BA1, `lemma-when-quotient-scheme-at-point`
(`literature/stacks-project/decent-spaces.tex`, lines 2157–2210), read locally.
No statement correction, new node, or dependency repair is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the two algebraic spaces are
  `(E B : AlgebraicSpace S)`; their morphism is `(p : E ⟶ B)`.
- Representable, surjective and finite locally free means exactly
  `IsRepresentableWith (fun _ _ q ↦ Surjective q.left ∧ q.left.IsFiniteLocallyFree)
  p.hom.hom`. Expanding the existing definition quantifies over every scheme `T : Over S`
  and every Yoneda map into B, supplying a representing scheme, its projection and a
  cartesian square, with both required properties of that same projection. There is
  no extra atlas, finiteness of the base, or choice of representing schemes in the input.
- The point is `(b : Point B.obj.obj)`. The imported `pointTopologicalSpace` supplies the
  specified atlas topology; the assertion itself only needs point-image membership.
- Clause (i) is `∃ N : OpenSubspace B, b ∈ pointImage N.val.ι ∧ ...`.
  The final `∃ T : Over S, Nonempty (N.val.toFunctor ≅ yoneda.obj T)` says precisely
  that the open subfunctor N is represented by an S-scheme.
- The equivalence between (i) and (ii) is the outer `↔`, with both existential statements
  parenthesized to fix its scope.
- Clause (ii) begins `∃ A : OpenSubspace E`. Its affine-scheme representation is
  `∃ T : Over S, IsAffine T.left ∧ Nonempty (A.val.toFunctor ≅ yoneda.obj T)`.
  Thus affineness applies to the scheme representing A, not to E or B.
- Containment of the entire inverse image of `{b}` is
  `∀ e : PointRepresentative E.obj.obj,
  Quot.mk _ (e.map p.hom.hom) = b → Quot.mk _ e ∈ pointImage A.val.ι`.
  Every point class has a representative, so this is exactly containment of every
  point above b. It neither chooses a representative nor asks for a lift over a fixed
  field. Point-image membership already permits extension of fields.
- No separatedness, Noetherianity, quasi-compactness, or schemeness condition on E or B
  occurs. The only structure assumed on them is `AlgebraicSpace S`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; these notions are available through the public imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`;
  the latter's actual scheme-test signature is used directly, without a private copy.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` provide the recorded sheaf-fibre-product framework;
  the representing cartesian square is supplied by `IsRepresentableWith`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, the existing class extending `IsFinite`, `Flat`,
  and `LocallyOfFinitePresentation`. No rank or degree assumption is imposed.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage`,
  `PointRepresentative.map`, and `pointTopologicalSpace`; the imported
  `AlgebraicSpacePointClasses` supplies `Point` and `PointRepresentative`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`, the subtype of
  subfunctors with inclusion representable by open immersions. Representation of its
  underlying `toFunctor` is the ordinary Yoneda representation, not a new notion.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`, the usual affine-scheme class,
  available through the public dependencies and equivalent to being a spectrum.

Recorded proof dependencies with usable modules are imported privately:
`Mathlib.AlgebraicGeometry.Morphisms.Finite` (`IsFinite`),
`Mathlib.AlgebraicGeometry.Morphisms.Affine` (`IsAffineHom`),
`Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient` (`space_invariant_open_quotient`),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests`
(`openSubspace_preimage_schemeTests`, `openSubspace_factor_schemeTests`,
`openSubspace_pullback_image`), and
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus` (`point_open_calculus`).
The theorem docstring carries all three proof steps and their cited node ids.
The proof-only nodes `lem-sfb-finite-locally-free-open-affine-cover` and
`lem-sfb-finite-space-morphism-topology` had no recorded Lean declaration or usable
Mathlib match when read, so there is no module to import for them yet; they remain
explicit in the proof plan. They are not required to type this statement.

Edge cases checked before writing:

- For empty B there is no b, and the statement makes no false nonemptiness demand.
- For `p = id`, the assertion reduces to the usual equivalence between a scheme open
  neighbourhood and an affine open neighbourhood of the point.
- A fibre with several points is covered in full by one affine open: the universal
  quantifier over representatives is not an existential choice of one fibre point.
- Finite locally free rank zero over a nonempty target is excluded by surjectivity,
  not by an added degree or rank hypothesis.
- The representing neighbourhood T may be non-quasi-compact on the left; no such
  restriction is imposed on E, B, or the open W used in the proof's shrinking step.
- The same universe u is used for S-schemes, fields, and the recorded presheaves;
  `Point` has its recorded universe u+1. No unrelated smaller test universe occurs.
- Common-field extension is built into point classes, so no rational-point lifting or
  algebraically closed base field is silently assumed.

Searches for existing statements:

- `msearch.py ... leanfinder "A point of an algebraic space has a scheme neighbourhood
  iff its fibre under a finite locally free surjection lies in an affine open"`:
  eight hits, all scheme results such as `reduce_to_affine_nbhd`, `Scheme.local_affine`
  and the affine characterization of `IsFinite`; none is this algebraic-space assertion.
- `msearch.py ... loogle '"IsFiniteLocallyFree", "IsAffine"'`: zero hits.
- `msearch.py ... grep
  'AlgebraicSpace|finiteLocallyFree.*neighbourhood|finiteLocallyFree.*neighborhood'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for `finiteLocallyFree`, `scheme_neigh`,
  `schemeNeigh`, `fibre.scheme.neigh` and `fiber.scheme.neigh` found existing finite
  locally free scheme/module lemmas, but no algebraic-space neighbourhood equivalence.
- `rg` over `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`
  for `0BA1`, `when.quotient.scheme.at.point`, and the proposed declaration fragments:
  no existing match. The exact item id has no upstream Lean occurrence.
- The prescribed CompactObject example is now a withdrawn empty module. Its node
  records the upstream `WeilConjectures.CategoryTheory.CompactObject`; that file was
  also read for the current public-module, namespace and documentation conventions.

Validation: scompile.py compiled the delivered file in sandbox and actual library
module modes, both successfully (6.8 s and 8.7 s respectively), with no diagnostics.
Every variable and universe is explicitly bound and `autoImplicit` is disabled.

## Second reading by Q28

Independent second reading (maintainer review service, 2026-10-24; the delivery's own
section was a same-session rereading by the author, H11, and is replaced by this one).

Node statement as a list, with the Lean that renders it and the verdict:

1. A scheme S (def-pc-scheme): `{S : Scheme.{u}}` — correct.
2. Algebraic spaces E, B over S (def-trf-algebraic-space): `(E B : AlgebraicSpace S)` — correct;
   no extra instance or hypothesis on E or B.
3. A morphism p : E → B: `(p : E ⟶ B)`, used through `p.hom.hom` (the natural
   transformation of underlying presheaves) — correct.
4. p representable, surjective and finite locally free on every scheme test
   (lem-trf-space-fibre-products-etale-covers, def-pc-finite-locally-free):
   `IsRepresentableWith (fun _ _ q ↦ Surjective q.left ∧ q.left.IsFiniteLocallyFree) p.hom.hom`.
   By the recorded definition (Sheaf/AlgebraicGeometry/AlgebraicSpace.lean:43) this says:
   for every `T : Over S` and `a : yoneda.obj T ⟶ B`, there is a representing S-scheme U,
   a projection `U ⟶ T` and a pullback square, with the projection surjective and
   `Scheme.Hom.IsFiniteLocallyFree` (finite + flat + lfp, the recorded node declaration).
   This is the node's hypothesis, no stronger: no rank, no atlas choice. Stacks 0BA1 states
   "surjective finite locally free morphism of algebraic spaces", which for spaces includes
   representability (finite ⇒ affine ⇒ representable), so the node and Lean agree with the source.
5. The atlas point topology (def-a1-space-point-topology): the imported
   `pointTopologicalSpace`; the statement needs only point classes `Point` and `pointImage`.
6. b ∈ |B|: `(b : Point B.obj.obj)` — `Point` is the quotient of field-valued
   representatives by the common-extension relation (def-a1-algebraic-space-point-classes).
7. (i) an open subspace N ⊆ B (def-a1-space-open-subspace) containing b and represented by a
   scheme: `∃ N : OpenSubspace B, b ∈ pointImage N.val.ι ∧ ∃ T : Over S,
   Nonempty (N.val.toFunctor ≅ yoneda.obj T)`. `OpenSubspace` is the recorded subtype of
   subfunctors with inclusion representable by open immersions; the point set of N is the
   point image of its inclusion; representability by an S-scheme is the Yoneda isomorphism
   (the same convention as AlgebraicSpaceUniversalIsomorphismOpen). Correct.
8. (ii) an open subspace A ⊆ E represented by an affine scheme (def-weil-affine-spectrum):
   `∃ T : Over S, IsAffine T.left ∧ Nonempty (A.val.toFunctor ≅ yoneda.obj T)`.
   Mathlib's `IsAffine` is "isomorphic to Spec of a ring" (def-pc-scheme's affine clause,
   via `Spec` of def-weil-affine-spectrum); affineness is on the representing scheme of A,
   not on E. Correct.
9. |A| contains the entire inverse image |p|⁻¹({b}):
   `∀ e : PointRepresentative E.obj.obj, Quot.mk _ (e.map p.hom.hom) = b →
   Quot.mk _ e ∈ pointImage A.val.ι`. Every point of |E| is the class of some
   representative, and the class of `e.map p` is |p|(class of e) by the definition of
   `pointImage`; so this is exactly |p|⁻¹({b}) ⊆ |A|, universally over all fibre points.
   Correct.
10. "the following are equivalent": the outer `↔`, both sides parenthesized — correct,
    neither direction weakened.
11. No separatedness, Noetherianity, quasi-compactness or schemeness of E, B: none occurs.

Source: literature/stacks-project/decent-spaces.tex, Tag 0BA1
(lemma-when-quotient-scheme-at-point): "Let X → Y be a surjective finite locally free morphism
of algebraic spaces over S. For y ∈ |Y| TFAE (1) y is in the schematic locus of Y, (2) there
exists an affine open U ⊂ X containing the preimage of y." Clause (1) = existence of an open
subspace containing y that is a scheme, i.e. item 7. Matches.

Edge cases: B empty (no b; vacuous); E empty forces B empty by surjectivity; p = id
(reduces to scheme-neighbourhood ⇔ affine neighbourhood of b); fibres with several points
(universal quantifier over all representatives); representatives over different fields of the
same class (both sides are invariant: `pointImage` is defined on classes); rank-zero locus
excluded by surjectivity only. Universes: S-schemes, fields and presheaves in `u`, points in
`u+1`, all bound; no universe restriction beyond the recorded algebraic-space convention.

One definition per notion: no new definitions; the declarations used are the recorded ones
of the seven stmt_deps. Searched lean/Sheaf for schematic-locus/representability notions
(`IsScheme*`, `IsSchematic`, `schematicLocus`, `IsRepresentedByScheme`): the only hit,
`IsRepresentedByScheme` (StablePointedModuliGroupoids), is for based categories/groupoids,
not presheaves; the Yoneda-iso form is the project convention for subfunctors. No existing
statement of 0BA1 in Mathlib or the project (also the worker's searches).

Records: the node copy differs from the live node only by the new `lean` record;
`lean.statement` is verbatim the signature in the file; the docstring carries the source place,
`(blueprint: …)` and all three proof steps with their cited nodes; the proof is `sorry`;
private imports are proof-dependency modules only. No mismatch was found; nothing in the Lean
was changed. This second reading replaces the delivery's self-audit section.
