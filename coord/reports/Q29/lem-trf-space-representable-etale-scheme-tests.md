## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests` states
`AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests`. Its proof is `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The ten conjuncts cover the whole item.

The earlier Q100 PASS and merge in the ledger are for stage 1: the live node has a
split proof and `reviewed`, but no `lean` record. Thus the previous worker's application
of stage-1 live-wins to this stage-2 task was mistaken. This delivery preserves the split.
No repair note for this item exists in the read repository.

### Hypotheses and clauses

The binder `{S : Scheme.{u}}` allows every base scheme. `AlgebraicSpace S` is the
recorded full subcategory of fppf sheaves with representable diagonal and a surjective
etale scheme atlas. `U T V : Over S` are arbitrary S-schemes; their underlying schemes
are `.left`. Their represented presheaves are `yoneda.obj U` and their induced maps are
`yoneda.map r`. `F.obj.obj` is the underlying presheaf of the algebraic space.
All universes are explicit (`universe u`), and `autoImplicit` is disabled. In particular
the scheme tests and the schemes being tested use the same bound; no smaller independent
test universe or extra smallness hypothesis has been introduced.

1. Every scheme-source map is representable: the first conjunct quantifies over
   `F`, `U`, and `a : yoneda.obj U ⟶ F.obj.obj` and concludes `IsRepresentable a`.
2. The second conjunct quantifies over both scheme-source maps to the same `F` and
   concludes `∃ P : Over S, Nonempty (Limits.pullback a b ≅ yoneda.obj P)`.
   This states representability of precisely the fibre-product presheaf. Since the
   inputs are sheaves, it is also their sheaf fibre product. The isomorphism is a
   natural isomorphism on all S-schemes, not merely agreement on field-valued points.
3. Composition of representable etale algebraic-space maps is conjunct three:
   `IsEtale f.hom.hom → IsEtale g.hom.hom → IsEtale (f ≫ g).hom.hom`.
4. Arbitrary algebraic-space base change is conjunct four: for `f : A ⟶ B` and
   arbitrary `g : C ⟶ B`, it asserts
   `IsEtale (Limits.pullback.snd f.hom g.hom).hom`. This is the projection
   `A ×_B C → C` of the actual sheaf pullback. The recorded fibre-product theorem
   already supplies its algebraic-space status; the statement needs no chosen atlas.
5. Every isomorphism is representable etale and representable surjective etale:
   conjunct five has `IsIso f → IsEtale f.hom.hom ∧ IsSurjective f.hom.hom`.
6. Conjunct six assumes the two recorded predicates for each factor and concludes
   both predicates for their composite. Thus it states surjective-etale composition.
7. Conjunct seven assumes both predicates for `f`, imposes no property on `g`, and
   concludes both for the same sheaf pullback projection. This gives arbitrary
   base change of representable surjective etale maps.
8. Conjunct eight states `IsEtale (yoneda.map r) ↔ Etale r.left`, for every
   S-scheme map `r : U ⟶ V`, including both implications.
9. Conjunct nine assumes `Etale r.left` and `Surjective r.left` and concludes
   `IsEtale (yoneda.map r) ∧ IsSurjective (yoneda.map r)`.
10. The last conjunct takes arbitrary scheme charts `a`, `b`, and scheme map `r`,
    assumes `IsEtale a`, `IsEtale b`, and exactly `yoneda.map r ≫ b = a`, and
    concludes `Etale r.left`. The equation is precisely `b ∘ h_r = a`.
    Neither chart is assumed surjective or separated.

Throughout, `AlgebraicSpace.IsEtale` and `AlgebraicSpace.IsSurjective` include
representability and use scheme projections, as the node requires. They do not mean
surjectivity of a natural transformation on individual sets of sections.

### Dependencies and source

Read the statement and binding of every statement dependency and the full declarations
and docstrings in the following modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsRepresentable`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`. Its already stated
  `isEtale_comp` supplies an input to the composition conjunct; no notion is duplicated.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, its affine
  local definition, composition, base-change instances, and `Etale.of_comp`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`, and the pullback universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `def-weil-size-convention` is the recorded metatheoretic convention, rendered by
  explicit universe polymorphism rather than a spurious Lean hypothesis.

Statement modules are public imports. The recorded proof inputs are imported normally:
Yoneda, OpenImmersion, Sites.MorphismProperty (cover composition and base change), and
Limits.MorphismProperty (finite-limit formulation of etale scheme base change).
The proof docstring reproduces all six live proof steps and names their DAG inputs.

Read the local Stacks sources: `spaces.tex`, the relative representable property and
Tags 025W (`lemma-representable-diagonal`), 02WJ, 02WK, 02WL; and
`spaces-properties.tex`, Tag 03EC (`lemma-etale-over-space`), statement and proof.
The source's scheme-test notion is precisely the dependency's predicate. The final
graph-section proof is the live node's equivalent argument: cancellation makes the
section etale and composition makes the comparison map etale.

### Searches

The prescribed `msearch.py` calls ran for Q29 and this item; their exact outputs are
retained in the sandbox `searches.jsonl`:

- LeanFinder: "Representable etale morphisms of algebraic spaces compose and are
  stable under base change; maps between etale scheme charts are etale". Eight hits,
  all scheme etale properties/categories; none states the algebraic-space suite.
- Loogle: `"IsRepresentableWith", "Etale"`. Zero hits.
- Mathlib grep: `AlgebraicSpace|IsRepresentableWith.*[Ee]tale|[Ee]tale.*IsRepresentableWith`.
  Zero hits.
- LeanSearch: "Scheme tests of representable etale algebraic space morphisms and
  comparison maps between etale scheme charts". Eight hits, involving scheme/ring
  etaleness and the small etale site; none states the item.
- `rg` for the exact blueprint id over `lean/WeilConjectures` and `lean/Sheaf` found
  no existing statement. `rg` for `IsRepresentableWith` and scheme-test/comparison
  names found the defining AlgebraicSpace module and open-immersion applications,
  not a declaration with the item's full conclusion. The broad etale/comparison
  search returned unrelated site and cohomology comparisons.

Read `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean` to check the service hits: the
indexed `IsEtale` name is a deprecated alias of scheme `Etale`, not a missing
algebraic-space implementation. The recorded algebraic-space composition helper
alone covers only one clause and is not an exact existing match for the item.

### Edge cases and validation

Checked empty schemes and spaces: all quantified maps and identity tests remain
valid, and no nonemptiness hypothesis has been imposed. Surjectivity of the empty
scheme map is required only in the clauses explicitly assuming it. Arbitrary
non-surjective etale charts, including open immersions, satisfy the final clause;
no covering assumption is needed. Nonseparated etale charts are allowed: the graph
section need not be closed, and the argument only uses etale cancellation.
A closed immersion of a point into the affine line is a negative test of the
scheme-map equivalence: its Yoneda map must not qualify as representable etale.
Nonreduced test schemes remain included in the Yoneda pullback condition.

The module compiles through `scompile.py` against the published live library in
both sandbox and library modes (2.2 and 2.4 seconds). No errors or warnings were
printed. The only postponed proof is the named main theorem. No statement dispute
or dependency fault was found.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
