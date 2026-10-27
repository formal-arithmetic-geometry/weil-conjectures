## Worker report

Group Q81, stage 2. Item: lem-trf-space-etale-source-atlas-detection.

The new module `Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection` states
`AlgebraicGeometry.AlgebraicSpace.etale_source_atlas_detection` with one `sorry`.
It contains no new definition, helper theorem, axiom, or proof. The node copy
changes only `lean`; its mathematical statement, dependencies and proof are unchanged.

The previous dispatch failure concerned an already reviewed stage-1 split. The live
node has `reviewed` from Q88, but no `lean` or `reviewed_lean`: its stage-2 statement
is still missing. The Q88 report expressly describes stage 1. There is no repair
note for this item. This delivery states the node without splitting it again.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`, with `universe u` explicitly declared and
  `autoImplicit false`. Algebraic spaces are the existing `AlgebraicSpace S`.
  An S-scheme is `Over S`, retaining its structure map; `yoneda.obj W` is h_W.
  Morphisms of spaces are existing full-subcategory morphisms; `f.hom.hom` is
  their underlying natural transformation.
- Representable etale and representable surjective mean the existing predicates
  `AlgebraicSpace.IsEtale` and `AlgebraicSpace.IsSurjective`. Each includes its
  scheme-test representability condition; no extra representability hypothesis
  is needed. Scheme etaleness and surjectivity are `Etale p.left` and
  `Surjective p.left`, exactly as the dependency declarations prescribe.
- Clause (1) is the first conjunct, quantified over `Y`, both arbitrary S-schemes
  `W V`, `q : yoneda.obj W ⟶ Y.obj.obj`, and `p : V ⟶ W`. Its three hypotheses
  are `Etale p.left`, `Surjective p.left`, and
  `IsEtale (yoneda.map p ≫ q)`. Its conclusion is `IsEtale q`. Lean composition
  is in diagrammatic order, so `yoneda.map p ≫ q` is q composed with h_p.
- Clause (2) is the second conjunct, quantified over `X Y R : AlgebraicSpace S`,
  `f : X ⟶ Y`, and `p : R ⟶ X`. The cover hypotheses are `IsEtale p.hom.hom`
  and `IsSurjective p.hom.hom`. Etaleness of f composed with p is
  `IsEtale (p.hom.hom ≫ f.hom.hom)`. Its conclusion quantifies over every
  `W : Over S` and `a : yoneda.obj W ⟶ X.obj.obj`, and says
  `IsEtale a → IsEtale (a ≫ f.hom.hom)`. This is precisely chartwise etaleness.
  There is no assumption that R is a scheme.
- Clause (3), its equivalence for EVERY atlas, is the third conjunct: `X Y f U p`
  are universally quantified; `IsEtale p → IsSurjective p →` supplies the atlas
  hypotheses. The left side of the iff is the same chartwise condition; the
  right side is `IsEtale (p ≫ f.hom.hom)`.
- The final sentence of clause (3), atlas existence for EVERY X, is the fourth
  conjunct: `∀ X, ∃ (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj),
  IsEtale p ∧ IsSurjective p`. No atlas is chosen or added as data.
- Fibre products occur in the proof plan, not as extra conclusions or hypotheses.
  The public import of the fibre-products dependency fixes the intended sheaf
  pullbacks and their algebraic-space interpretation.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`,
  `IsAlgebraicSpace`; also its composition theorem in the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and their universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`.
- The size convention is metatheoretic: no Lean object is required; the explicit
  `u` agrees with the existing space and presheaf universes and excludes no
  schemes within that bound.
- Proof-only import `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`:
  `AlgebraicGeometry.Etale.of_comp_of_surjective_etale`.
  The other proof dependency, `lem-trf-space-representable-etale-scheme-tests`,
  currently has no recorded Lean declaration. It is not needed for the signature,
  is retained in the DAG proof plan and docstring, and has no import to add yet.

One definition per notion: `IsChartwiseEtale` already exists in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`, lines 43-49. Its definition
was read in full. We write its quantified condition directly, literally the
same formula, rather than define another predicate or import the downstream
site module. The enlarged-site node depends through chartwise permanence on
this item, so adding it as a dependency would close a DAG cycle. No existing
notion is redefined and no new node is required.

Sources read: `literature/stacks-project/spaces-properties.tex`,
`lemma-etale-over-space` (03EC), lines 2019-2090, and `lemma-etale-local` (03FS),
lines 2111-2160. Clause (1) is 03EC(3); clause (2) is its scheme-test descent
argument after pulling back a chart along the representable cover; clause (3)
is the atlas criterion of 03FS. The theorem docstring contains all three DAG
proof steps, including the scheme source-descent input and atlas existence.

Edge cases checked before writing: empty W and V (a surjective map from empty
V forces W empty), empty X and its empty atlas, identity covers, arbitrary
non-scheme R, and non-quasi-compact/non-separated/non-Noetherian spaces. None
is excluded by a `Nonempty`, finiteness, separation or scheme-source binder.
Surjectivity is essential: an empty cover of a nonempty source cannot test
etaleness and is correctly ruled out by `IsSurjective`/`Surjective`.
The chart condition quantifies over all schemes in the same bound as the
existing representability definition, not an independent smaller universe.

Searches performed with `msearch.py Q81 lem-trf-space-etale-source-atlas-detection`:

- `leanfinder`: "Etaleness of a morphism of algebraic spaces is detected after a
  surjective etale atlas of the source". Eight results: scheme Etale composition,
  cancellation and base-change properties, and ring-etale results; no algebraic
  space source-atlas theorem.
- `loogle`: `"IsEtale", "Surjective"`. Zero results.
- `grep`: `IsChartwiseEtale|etale.*atlas|atlas.*etale`. Zero Mathlib results.
- `leansearch`: "An algebraic space morphism is etale on every scheme chart if
  its composite with a representable surjective etale source cover is etale".
  Eight results about schemes or rings, none stating the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `IsChartwiseEtale`, chartwise/etale atlas patterns and the proposed theorem
  name. The existing chartwise predicate and downstream permanence theorem
  were found and read; no declaration supplies all of these source-cover
  detection clauses. No name clash for `etale_source_atlas_detection`.
  The precise new theorem name was also searched in Mathlib: no match.

Validation: `scompile.py Q81 lem-trf-space-etale-source-atlas-detection` checked
this delivered module against the live server build, in sandbox and library
modes, with no errors or warnings (8.2 s and 4.9 s). The node `lean.statement`
is extracted verbatim from `theorem` through the type before `:=`.

No statement correction, dependency repair, or disputed statement.
The maintainer performs the independent review; this report records the
worker's own correspondence check and does not claim an independent reading.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
