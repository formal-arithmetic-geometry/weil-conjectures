## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage` states
`AlgebraicGeometry.AlgebraicSpace.etaleSchemeMap_openImage`, with a single `sorry`.
It introduces no definitions and changes only the item's `lean` field. No statement
correction, disputed statement, new node, or dependency repair is needed.

I read Stacks `spaces-properties.tex`, Tag 06NF, `lemma-etale-image-open`, first assertion
and factorization (lines 536–555). Its quotient-presentation assertion is intentionally
absent from this node and from the Lean statement. I also read the four statement
dependencies and their recorded declarations, including their full signatures/docstrings.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space over it is
  `(X : AlgebraicSpace S)`. This is the existing full subcategory of fppf sheaves
  with representable diagonal and a surjective étale scheme atlas.
- The S-scheme is `(U : Over S)`, with `h_U` rendered as `yoneda.obj U`.
  The map is `(f : yoneda.obj U ⟶ X.obj.obj)`. Morphisms of spaces are the existing
  full-subcategory sheaf maps, whose underlying natural transformations are `.hom.hom`.
- Representability is `(hf : IsRepresentable f)`; representable étaleness is
  `(he : IsEtale f)`. These are the dependency's scheme-test predicates, not private
  copies, and quantify over every test scheme and map to the target presheaf.
- The size convention is the explicit universe `u`. All schemes, fields K and L,
  and presheaf values have exactly the universes of the existing big-site interface.
  No independent lower test universe is introduced.
- Existence of the algebraic space X_f and its inclusion is
  `∃ (Xf : AlgebraicSpace S) (j : Xf ⟶ X) ...`. Identification as a subfunctor is
  `∀ T : (Over S)ᵒᵖ, Function.Injective (j.hom.hom.app T)`. It specifies an embedded
  copy; literally replacing it with its componentwise range gives the subfunctor.
- The representable inclusion that becomes an open immersion on every scheme base
  change is `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`.
  The existing `IsRepresentableWith` supplies an actual scheme representing each
  pullback square, with that projection property.
- The factor map is `(ff : yoneda.obj U ⟶ Xf.obj.obj)`, and the factorization is
  `ff ≫ j.hom.hom = f` (Lean composition reads left to right).
- Its representability, surjectivity and étaleness are exactly
  `IsRepresentable ff ∧ IsSurjective ff ∧ IsEtale ff`. In particular surjectivity
  is the prescribed scheme-base-change predicate, not surjectivity on rational points.
- The final universal quantification ranges over a field `K : Type u`, a structure
  map `s : Spec (CommRingCat.of K) ⟶ S`, and a field-valued section `x` of X.
  Its left side says this section factors through Xf: `∃ y, j.hom.hom.app _ y = x`.
  Its right side says that for some extension field L and ring homomorphism `e : K →+* L`,
  there is an S-map `y : Over.mk (Spec.map (CommRingCat.ofHom e) ≫ s) ⟶ U` whose
  image under f equals the restriction of x to L. The restriction uses the existing
  presheaf map on `(Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl).op`.
  Thus the equality of point images is expanded directly on representatives, with no
  new point quotient or private definition. Ring maps between fields are injective.
  Equality of classes originally represented over different fields yields exactly
  such a lift by restricting the U-representative to their common extension.
  Conversely the displayed extension witnesses equality of classes. For an open
  subspace, belonging to its class image is equivalent to factoring the original
  representative: its pullback to Spec K is an open subscheme, which is all of
  Spec K if it becomes nonempty over any field extension. This is why the left side
  correctly renders the class image, without a rational-point surjectivity claim.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-size-convention` is recorded as a metatheoretic convention; its node
  explicitly asks citers to state their universe levels directly.

The statement imports the space interface and open-immersion module publicly.
The sole proof dependency `lem-a1-space-etale-open-image` currently has neither a Lean
record nor a Mathlib match; there is no module to import. It is the general theorem
used only by the postponed proof, not a notion needed to type this statement. Its
specialization to `E = h_U` is recorded step by step in the theorem docstring. The
maintainer can add the proof-only import when that separate node is stated, as the
stage rules prescribe. No duplicate general theorem is introduced.

Edge cases checked before writing:

- Empty U gives the empty open subspace; both sides of the field-section equivalence
  are false, so no nonempty hypothesis appears. Empty S and empty X are also allowed.
- An open immersion f has its original open subspace as image; its factor ff is an
  isomorphism. Injectivity of the inclusion states the actual subfunctor condition.
- A surjective étale atlas has all of X as its open image.
- A nontrivial finite separable extension of fields may have no lift of a K-point
  over K itself; the RHS allows L/K, so it states point-class image rather than the
  false surjectivity condition on K-rational points.
- An étale non-monomorphism (for example squaring on the multiplicative group in
  characteristic different from two) is allowed: only j, not f or ff, is injective.
- No characteristic, separation, quasi-compactness or finiteness assumption is imposed.

Searches for reuse (2026-10-18):

- `msearch.py leanfinder`: “The image of an etale morphism from a scheme to an
  algebraic space is an open subspace and the morphism to its image is etale and
  surjective”. Eight results: `AlgebraicGeometry.IsEtale`, `Scheme.Etale`, their
  category/forgetful declarations and smooth/unramified/composition instances.
  No algebraic-space open-image theorem.
- `msearch.py loogle`: `AlgebraicGeometry.AlgebraicSpace, IsEtale`. Zero hits;
  Mathlib's search index does not contain `AlgebraicGeometry.AlgebraicSpace`.
- `msearch.py leansearch`: “An etale map from a scheme to an algebraic space factors
  as a surjective etale map followed by an open immersion onto its point image”.
  Eight hits concern scheme étaleness, open immersions and `Scheme.Hom.mem_opensRange`;
  none states the algebraic-space assertion.
- `msearch.py grep`: `AlgebraicSpace|etale.*image.*open|open.*image.*etale` in
  Mathlib's AlgebraicGeometry directory: zero hits.
- Direct `rg` in Mathlib and the upstream `WeilConjectures` tree found no
  `AlgebraicSpace` declaration; direct search for this item's blueprint id in the
  upstream tree found no hit. Broader étale/image search found scheme-only results.
- Direct `rg` in `lean/Sheaf` found the existing algebraic-space interface,
  `AlgebraicSpaceJointSurjectivity`, and `AlgebraicSpaceFibreProductsEtaleCovers`.
  None states this theorem. The joint-surjectivity module independently confirms
  the same field-extension expansion of quotient point images used here; it defines
  a covering-family predicate, which this single-map image statement does not need.
- Search for `etaleSchemeMap_openImage`, `etaleSchemeMap`, and `openImage` in the
  relevant project interfaces, upstream name index, upstream Lean, and Mathlib found
  no name collision.

Validation: the required `scompile.py NJ lem-a1-etale-scheme-map-open-image` check
compiled this delivered module cleanly, with no errors or unexpected warnings.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
