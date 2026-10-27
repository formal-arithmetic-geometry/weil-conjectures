## Worker report

The module `Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle` states
`AlgebraicGeometry.Scheme.exists_scheme_of_zariski_cocycle`, with `sorry` as its
entire proof. It defines no new notion. The node is unchanged except for `lean`.
Its statement is the current blueprint's lemma in
`literature/blueprint/latest/blueprint/sec-curve-estimates/sk-thm-curveestimate/lem-galois-glue.md`.
The construction follows the accepted node proof and Stacks 01JB, 01JC, 01JR,
read in `literature/stacks-project/schemes.tex` (glueing-schemes and
open-fibre-product). No statement correction or disputed statement is needed.

Hypothesis-by-hypothesis correspondence:

* “Let Y be a scheme” is `(Y : Scheme.{u})`.
* The arbitrary cover index set is `(I : Type v)`; the base charts and local
  schemes are `(Yᵢ Pᵢ : I → Scheme.{u})`. Both universes are explicitly bound.
* “Yᵢ → Y a Zariski cover” is `(b : ∀ i : I, Yᵢ i ⟶ Y)`,
  `[∀ i : I, IsOpenImmersion (b i)]`, and
  `hcover : ∀ y : Y, ∃ (i : I) (x : Yᵢ i), b i x = y`.
  Open immersions and joint pointwise surjectivity are exactly a Zariski cover;
  the cover need not be finite, locally directed, or nonempty.
* “For each i, Pᵢ → Yᵢ a scheme” is `(f : ∀ i : I, Pᵢ i ⟶ Yᵢ i)`.
  The resulting structure map to Y is `f i ≫ b i`.
* The given overlap isomorphism is
  `φ i j : pullback (f i ≫ b i) (b j) ≅ pullback (f j ≫ b j) (b i)`.
* “Over Yᵢ ×_Y Yⱼ” is exactly the two equations of `hφ`. On the target overlap
  the Yⱼ-coordinate is `pullback.fst ... ≫ f j` and its Yᵢ-coordinate is
  `pullback.snd ...`. On the source these are respectively `pullback.snd ...`
  and `pullback.fst ... ≫ f i`. Preserving both coordinates is equivalent to
  commuting with the map to their fibre product, by its universal property.
* “φᵢᵢ = id” is `hφ_self : ∀ i : I, φ i i = Iso.refl _`, on the same chosen
  pullback object on each side. It does not require identifying a pullback
  definitionally with Pᵢ.
* The triple cocycle is `hcocycle`. It is expressed by morphisms of schemes,
  rather than by equality on underlying points: for every `T : Scheme.{u}`,
  `a : T ⟶ Uᵢⱼ`, `d : T ⟶ Uⱼₖ`, and `c : T ⟶ Uᵢₖ`, three antecedent
  equations require (1) the Pⱼ-coordinate of φᵢⱼ a to be the Pⱼ-coordinate of d,
  (2) the initial Pᵢ-coordinates of a and c to agree, and (3) the Yₖ-coordinates
  of d and c to agree. Its conclusion equates the Pₖ-coordinate of φⱼₖ d with
  that of φᵢₖ c. These are exactly the two routes on a common triple overlap.
  Their remaining coordinate is already equal by `hφ`.

For completeness, this test-scheme cocycle is equivalent to the usual restricted
morphism equality, with no domain condition omitted. Given a pair of compatible
maps into Uᵢⱼ and Uᵢₖ, `hφ` ensures that the Pⱼ-coordinate after the first
transition and the Yₖ-coordinate define a unique map d to Uⱼₖ. Thus all three
antecedents hold on the universal triple overlap
`Uᵢⱼ ×_{Pᵢ} Uᵢₖ`. Applying `hcocycle` there gives the ordinary cocycle;
conversely, composing that cocycle with any such a, d, c gives `hcocycle`.
Taking test schemes in universe u is sufficient because this universal triple
overlap is itself a `Scheme.{u}`. Equality of morphisms is retained, including
nilpotent structure, rather than checked only on field-valued points.

Conclusion-by-conclusion correspondence:

* The Y-scheme P is `∃ (P : Scheme.{u}) (p : P ⟶ Y)`.
* The local identifications are the further existential datum
  `(e : ∀ i : I, pullback p (b i) ≅ Pᵢ i)`.
* They are “over Yᵢ” by the first conjunct
  `∀ i, (e i).hom ≫ f i = pullback.snd p (b i)`.
* Write qᵢ for `(e i).inv ≫ pullback.fst p (b i)`. The second conjunct is
  precisely `pullback.fst ... ≫ qᵢ = (φ i j).hom ≫ pullback.fst ... ≫ qⱼ`
  on Uᵢⱼ. Since qᵢ are the open embeddings of the inverse-image charts, this
  means that the induced transition is exactly φᵢⱼ. No chosen identification
  of iterated fibre products or arbitrary comparison map is assumed.
* “Unique up to unique isomorphism” quantifies over every other P', p', e'
  satisfying the same base and overlap equations and asserts `∃! h : P ≅ P'`.
  The predicate requires `h.hom ≫ p' = p` and, for every i,
  `qᵢ ≫ h.hom = q'ᵢ`. Thus the isomorphism is over Y and respects the chosen
  local identifications, as required by step 5 of the node proof. It does not
  incorrectly assert uniqueness among all automorphisms of the underlying
  Y-scheme without chart compatibility.

Dependency declarations used and read in full, including their docstrings:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`. They are the locally affine locally ringed
  spaces and their morphisms, as the dependency states.
* `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, from
  `Mathlib.AlgebraicGeometry.OpenImmersion`. It abbreviates open immersion of
  the underlying locally ringed spaces; no private predicate is introduced.
* `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  and `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The scheme
  existence instance is supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
  All four are public statement imports.
* Proof prerequisite `lem-weil-pbc-open-preimage-fibre-product` has the Mathlib
  match `AlgebraicGeometry.isPullback_morphismRestrict` and the associated
  `pullbackRestrictIsoRestrict`, in `Mathlib.AlgebraicGeometry.Restrict`.
* Proof prerequisite `lem-weil-pbc-glue-schemes` uses
  `AlgebraicGeometry.Scheme.GlueData`, `GlueData.glued`, its open and jointly
  surjective chart embeddings, `glue_condition`, and `vPullbackConeIsLimit`.
  `lem-weil-pbc-scheme-morphism-gluing` uses `Scheme.Cover.glueMorphisms`,
  `ι_glueMorphisms`, and `hom_ext`. They are in
  `Mathlib.AlgebraicGeometry.Gluing`. These two proof modules are plain imports;
  the theorem docstring includes all five accepted proof steps with their nodes.

Edge cases checked before writing:

* Empty index set: `hcover` forces Y empty, and a scheme over the empty scheme
  is empty. The statement has no `Nonempty I` restriction; existence and unique
  compatible isomorphism are valid in this case.
* Empty Y, empty charts, and empty Pᵢ: no nonemptiness hypotheses exclude them;
  their overlap equations have the intended empty domains.
* One identity base chart: normalization and the chart isomorphism recover Pᵢ;
  uniqueness respects that isomorphism, even when Pᵢ has automorphisms.
* Disjoint charts: mixed overlaps are empty and the gluing is the disjoint union.
* Repeated charts: transitions can be nontrivial while satisfying the cocycle;
  no injectivity of the coproduct relation map is used or claimed. In particular,
  the known erroneous claim in the blueprint proof is avoided, following the
  repaired DAG proof.
* Arbitrary index universe v: the theorem does not require a small coproduct
  of all Pᵢ as an extra hypothesis. An open cover of Y has a subcover indexed
  by its points, and the cocycle identifies the remaining charts. The result
  can remain in the same scheme universe u; no universe equality is imposed.
* Nonreduced schemes: cocycle and compatibility are equalities of scheme
  morphisms, retaining the structure sheaf data.

Searches made (2026-10-24):

* `msearch.py leanfinder`: “Schemes over a Zariski cover with cocycle transition
  isomorphisms glue uniquely with compatible local identifications”. Eight hits
  included `Scheme.GlueData`, `Cover.gluedCover`, `Cover.glueMorphisms`, and
  `Cover.RelativeGluingData.mk.inj`; none is this relative arbitrary-cover
  existence and compatible uniqueness statement.
* `msearch.py loogle`: `AlgebraicGeometry.Scheme.GlueData, CategoryTheory.DescentData`.
  No hits; the latter identifier is unknown. This failed query did not supply
  an interface or justify assuming a new structure.
* `msearch.py leansearch`: “Schemes glue along open subschemes satisfying a
  cocycle condition uniquely with local isomorphisms”. Eight hits included
  `Scheme.GlueData.glued`, `Scheme.GlueData`, and `Scheme.LocalRepresentability.glueData`.
  These give general gluing, not all relative chart and uniqueness clauses.
* `msearch.py grep`: `descent|Descent|glue|Glue` in
  `AlgebraicGeometry/RelativeGluing.lean`. Five hits. Directly reading the full
  `RelativeGluingData` declaration and its results confirms that they concern
  locally directed covers with a categorical index and an equifibered diagram.
  Requiring that extra structure would alter the input of the present lemma.
* Direct `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `lem-galois-glue`, `galois.*[Gg]lu|Galois.*[Gg]lu|relative.*[Gg]lu`, and
  `galois_glue|exists_relative_gluing|glue_schemes_over`: no exact declaration.
  The relevant existing finite-locally-constant relative gluing construction
  is specialized to representing sheaves and uses a locally directed cover.
* Direct `rg` for `exists_scheme_of_zariski_cocycle` in Mathlib, both source
  roots, and `dag/lean_names_upstream.json`: no name collision.

Validation: the prescribed `scompile.py Q107 lem-galois-glue` compiled both
the sandbox and library module forms cleanly (2.1 s and 2.5 s), with no errors
or warnings. The final dry run and delivery repeat the per-file check.

## Second reading by Q107

No second worker was started: the dispatcher explicitly requires direct delivery
and the maintainer supplies the independent review. A final self-check reopened
the node and module and verified every correspondence above. In particular,
both base coordinates of φ are preserved, the cocycle is on arbitrary scheme
test objects, the charts are isomorphisms over Yᵢ, and the unique isomorphism
preserves those charts. The only edit from this check corrected the explanatory
docstring's name for the middle test morphism from b to d; no signature changed.
