## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFormallyUnramifiedEtaleCharts` states Tag 04G8
conditions (1)--(3) as `List.TFAE`. Both declarations have exactly `by sorry` proofs.
There are no definitions, choices of atlases, new nodes, dependency repairs, or statement
corrections. The auxiliary theorem records the scheme specialization asserted in the node.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `{Z X : AlgebraicSpace S}` and `(f : Z ⟶ X)`
  are the arbitrary algebraic spaces and their morphism over S. The single explicit
  universe u is exactly the existing algebraic-space interface: presheaves of `Type u`
  on `(Over S)ᵒᵖ`. Tests and charts belong to that same scheme category. No independent
  smaller test universe is used.
- A scheme over S is `Over S`; its scheme is `.left`. A morphism `i : T ⟶ T'` in
  that category is an S-morphism. The implications `IsAffine T.left → IsAffine T'.left`
  restrict precisely to affine tests. `IsFirstOrderThickening i.left` is the existing
  predicate `IsClosedImmersion i.left ∧ i.left.ker ^ 2 = ⊥`. Scheme base change gives
  precisely the node's representable closed immersion with square-zero ideal.
- Condition (1) is the first entry of `List.TFAE`. A map to X is
  `b : yoneda.obj T' ⟶ X.obj.obj`; the two candidate lifts are
  `a₁ a₂ : yoneda.obj T' ⟶ Z.obj.obj`. Their being over that fixed X-map is expressed
  separately by `a₁ ≫ f.hom.hom = b` and `a₂ ≫ f.hom.hom = b`. Restriction along
  the thickening is precomposition by `yoneda.map i`. The final implication says
  equal restrictions force `a₁ = a₂`, exactly injectivity on Hom over X. This
  two-lift formulation also covers an empty Hom set, with no lift-existence demand.
- Condition (2) is the second entry. `V U : Over S` are arbitrary schemes over S,
  `p` and `q` are their maps to Z and X, and `g : V ⟶ U` is the scheme map over S.
  `IsEtale p` and `IsEtale q` use representable étaleness on scheme base changes.
  `p ≫ f.hom.hom = yoneda.map g ≫ q` is the square's commutativity, with the
  same orientation as f p = q g. The conclusion is Mathlib's
  `FormallyUnramified g.left`.
- Condition (3) is the third entry. The same schemes, chart maps, and scheme map
  are existentially quantified. Both `IsEtale` predicates, both `IsSurjective`
  predicates, the commutative-square equality, and `FormallyUnramified g.left`
  are conjuncts. Surjectivity is the existing representable scheme-test
  surjectivity, without selecting an atlas or assuming f representable.
- `List.TFAE` says all three entries are pairwise equivalent. It imposes no
  local finite type, quasi-compactness, separation, nonemptiness, or finiteness.
- The scheme-agreement clause is
  `scheme_formallyUnramified_iff_affine_firstOrder`: for any scheme map g,
  Mathlib's `FormallyUnramified g` is equivalent to uniqueness for every affine
  first-order thickening, for two maps with the same image under g and equal
  restrictions. Their common image is the implicit structure map to the target;
  explicitly quantifying that common map is equivalent. Yoneda identifies this
  with the restriction condition used for spaces. No existence clause is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  schemes are locally ringed spaces locally affine and arrows are their morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, `IsSurjective`. The full subcategory's maps unwrap as `f.hom.hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  accessed through the owning thickening module's public import.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (scheme affine-locally
  étale ring maps), in contrast with `AlgebraicSpace.IsEtale` on presheaf maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`:
  `FormallyUnramified`, `FormallyUnramified.hom_ext`,
  `FormallyUnramified.of_hom_ext`. The two agreement criteria were read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. This statement dependency is publicly imported;
  its fibre-product/cover conclusions are used in the proof plan, not hypotheses.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
  Its owner `def-sbc-first-order-thickening` was already a proof dependency with
  a landed Lean record and is added to `stmt_deps` under the existing-owner rule.
  No other field besides `lean` and this permitted `stmt_deps` addition changes.
- Proof imports are `WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale`
  (`flat_unramified_formally_etale`) and
  `WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange`
  (`IsFirstOrderThickening.baseChange`). Scheme étale composition/cancellation
  and the fppf topology are supplied by the imported Etale and AlgebraicSpace
  modules (`Etale.of_comp`, `Etale.etale_comp`, open-immersion étaleness;
  `Scheme.fppfTopology`). The compatible-chart proof dependency
  `lem-sfb-unramified-etale-compatible-charts` currently has no Lean record and
  is not needed in the signature; its absent module is not imported. It remains
  explicitly cited in the proof docstring. No unavailable statement notion remains.
- The size dependency is a convention, with no declaration/module to import.
  `Mathlib.Data.List.TFAE` supplies the standard logical conjunction of pairwise
  equivalences; it introduces no algebraic-geometric notion.

Searches (2026-10-24):

- `msearch.py ... leanfinder "A morphism of algebraic spaces is formally unramified
  if and only if every compatible etale scheme chart is formally unramified"`:
  8 hits, all scheme/ring formal unramifiedness; no space chart criterion.
- `msearch.py ... loogle '"FormallyUnramified", "etale"'`: 12 hits about rings,
  algebras, and `AlgebraicGeometry.Etale.instFormallyUnramified`; no space criterion.
- `msearch.py ... grep 'formallyUnramified.*(etale|cover)|formally_unramified.*(etale|chart)'
  AlgebraicGeometry`: 3 hits in scheme Etale and FormallyUnramified, no match.
- `msearch.py ... leansearch "Formal unramifiedness of algebraic spaces is equivalent
  to formal unramifiedness on compatible etale scheme charts"`: 8 scheme/ring hits;
  no match. The node's own earlier searches were also read.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and
  `dag/lean_names_upstream.json` found no declaration with either proposed name.
  Searching the node id under `lean/WeilConjectures` found nothing.
- Concept searches found `SpaceFormallyUnramified` in
  `Sheaf.AlgebraicGeometry.SpaceUniversalConormal`. I read that definition and
  its owning node. It tests ALL schemes, whereas this node explicitly states
  affine tests. More importantly, its owner has THIS item as a proof dependency
  and needs its import for stage 3. Importing that downstream theorem module
  would create an import cycle. Therefore no second predicate is defined here:
  the exact affine uniqueness formula is expanded inside the theorem statement.
- Local sources and `scompile.py --source` confirm the conormal module is live.
  A speculative lookup of `Sheaf.AlgebraicGeometry.UnramifiedEtaleCompatibleCharts`
  found no module; the corresponding node has no Lean record. This is only an
  unstated proof dependency, not a missing object used by the delivered signature.
- Read Stacks `spaces-more-morphisms.tex`, lemma-formally-unramified, and confirmed
  tags 04G8 and 04AL in `tags/tags`; the source's three clauses match the node.

Edge cases checked before writing:

- Empty schemes/spaces: no `Nonempty` hypothesis occurs; affine empty schemes
  and empty atlases remain permitted. Fppf separatedness detects equality even
  on the empty cover. This matches the last step of the node's proof.
- Identity thickenings and zero ideals are allowed: square zero includes the zero
  ideal, so the uniqueness condition specializes to the evident identity test.
- Candidate lifts need not exist; the implication over a pair of candidates
  asserts only injectivity, as required for formal unramifiedness.
- Neither vertical chart map is assumed surjective in condition (2); both are
  required surjective in (3). The general f has no representability assumption.
- Arbitrary relative dimension, nonseparated spaces, non-quasi-compact spaces,
  and arbitrary characteristic are not excluded by any binder.

Validation: `scompile.py Q34 lem-sfb-space-formally-unramified-etale-charts <module>`
compiled both its sandbox and library form without errors or warnings (1.5 s and
1.6 s respectively). Only the two declared theorem proofs are postponed.
No `STATEMENT-DISPUTED` issue or source correction was found.

## Second reading by Q34

This is a second pass by the same sole dispatcher-started worker, not a claim of
an independent agent review; the brief prohibits starting other agents and assigns
independent review to the maintainer. I reopened the node and delivered module.
The comparison checked all three TFAE entries against the numbered source clauses:
affineness occurs only in entry (1), chart étaleness in entries (2) and (3), and
both surjectivity predicates only in entry (3). The square uses the underlying
presheaf morphism of the actual f, and the conclusion uses the scheme g.left,
without strengthening either to a representable space morphism. The scheme
agreement quantifies every affine first-order test and only asks uniqueness.
The check also confirmed explicit universe/variable binding, real imported
thickening data, no duplicated predicate, no let binders or local notation, and
an owner record for the added thickening dependency. No mismatch required a change.
