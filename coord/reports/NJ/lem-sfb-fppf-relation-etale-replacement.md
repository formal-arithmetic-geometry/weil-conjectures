## Worker report

The delivery states `AlgebraicGeometry.fppf_relation_etale_replacement` in
`Sheaf.AlgebraicGeometry.FppfRelationEtaleReplacement`. Its single theorem has
`sorry`; no definition or extra theorem is introduced. The node statement and
accepted proof are unchanged. The statement-dependency list additionally names
`def-sfb-restricted-groupoid-relation`, an existing landed definition node owning
the three reused restriction constructions.

Source read: `literature/stacks-project/bootstrap.tex`, theorem-final-bootstrap,
Tag 04S6, especially the affine locally quasi-finite paragraphs (lines 1540–1650).
They construct finitely many affine etale neighborhoods, divide each open finite
locally free subgroupoid, descend flatness and finite presentation, descend the
open unit, and conclude etaleness and equality of the quotient sheaves. The
latest blueprint direct-images proof (3) was also read; this is the supporting
final-bootstrap prerequisite recorded in the DAG, not a change to that unit.
No repair note for this item was present.

Clause-by-clause correspondence:

- Base scheme and bound: `{S : Scheme.{u}}`; all original, chart and replacement
  schemes are `Over S`, hence have scheme universe `u`. Test objects are every
  `T : Over S`, with no smaller independent universe. Orbit values are lifted to
  `Type (u + 1)` so the big site, whose object universe is `u+1`, has the standard
  sheafification. This implements the recorded metatheoretic size convention.
- Original S-schemes and S-morphisms: `{R V : Over S}` and `(s t : R ⟶ V)`.
  Slice morphisms include all required compatibility with the structure maps.
- Injectivity of `j=(s,t)` on every test scheme:
  `[Mono (prod.lift s t)]` in `Over S`. The slice categorical product is precisely
  `V ×_S V`. Categorical monicity is injectivity of maps into that product on all
  test objects. It imposes no separatedness hypothesis on the base.
- Equivalence relation on sections: `hrel` explicitly quantifies over all
  `T : Over S` and says `Equivalence` of existence of an arrow `r` with the two
  prescribed endpoints. Together with monicity this identifies `R(T)` with the
  relation, exactly as the node asks. No groupoid operations are extra inputs.
- Affineness: `[IsAffine V.left]`.
- Flatness: `[Flat s.left] [Flat t.left]`.
- Local finite presentation: both `LocallyOfFinitePresentation` instances.
- Local quasi-finiteness: `hs` and `ht` use the recorded Stacks predicates
  `Scheme.Hom.IsLocallyQuasiFinite`, retaining the finite-type condition.
- Finite index set: `∃ (I : Type u) (_ : Finite I)`. A finite type in this bound
  represents any required finite set; no `Nonempty I` is assumed.
- Affine S-chart schemes and etale S-maps: `W : I → Over S`,
  `g : ∀ i, W i ⟶ V`, and `∀ i, IsAffine (W i).left ∧ Etale (g i).left`.
- Jointly surjective images: every point `v : V.left` has `i`, `w` with
  `(g i).left w = v`. No individual chart is required to be surjective.
- Restricted relation `R_i`: `restrictedEtaleRelation s t (g i)` is the existing
  iterated pullback `W_i ×_V R ×_V W_i`. Its recorded source and target maps enter
  the two Yoneda maps of its orbit presheaf. Their underlying definitions require
  no etaleness of `s` or `t`.
- Replacement S-schemes: for each `i`, existential `Wbar Rbar : Over S`, with
  `sbar tbar : Rbar ⟶ Wbar`. Neither affineness nor a choice of a quotient map is
  imposed on these schemes, since the conclusion does not require either.
- Replacement equivalence relation: `Mono (prod.lift sbar tbar)` and the explicit
  `∀ T, Equivalence` clause, with the same endpoint interpretation as above.
- Etale replacement projections: `Etale sbar.left ∧ Etale tbar.left`.
- Quotients: `coequalizer` of the two `uliftYoneda.{u+1}.map` arrows is the
  pointwise quotient presheaf. For an equivalence relation the generated
  equivalence relation already is the given relation, so these are exactly the
  presheaves `T ↦ V(T)/R(T)` in the node, with a harmless universe lift.
- Isomorphism of fppf sheaves: `Nonempty` of an actual categorical isomorphism
  between the two `presheafToSheaf (Scheme.fppfTopology.over S) (Type (u+1))`
  objects. This is existence of an isomorphism, not an assumed arbitrary map or
  an isomorphism merely of section types.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections and universal lift; used by the existing restricted relation.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`. The sheafification existence instance in
  `Mathlib.CategoryTheory.Sites.LeftExact` applies to `Type (u+1)`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over`. These give precisely the recorded big fppf site.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, whose stalkwise criterion
  is `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, whose full definition was read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`; the old dependency record
  names this exact class and requires no repair.
- `def-weil-size-convention` has a convention-only record, so no object or
  artificial hypothesis is added for it.
- `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`:
  `AlgebraicSpace.restrictedEtaleRelation`,
  `AlgebraicSpace.restrictedEtaleRelationSource`,
  `AlgebraicSpace.restrictedEtaleRelationTarget`. These are owned by the added
  existing definition dependency `def-sfb-restricted-groupoid-relation`.

All currently recorded proof-dependency modules are imported non-publicly.
The three proof-only nodes `lem-sfb-divide-finite-flat-subgroupoid`,
`lem-sfb-representable-fppf-etale-open-descent`, and
`lem-sfb-groupoid-open-unit-etale` have no Lean record or Mathlib match in the
read snapshot, so their imports are omitted under stage 2 rule 7; none supplies
an object needed to type this statement. Their complete intended use is retained
in the seven-step proof docstring. No proof-dependency record is modified.

Edge cases checked: empty `V` permits `I = Empty` (or its universe lift); the
joint-surjectivity condition is vacuous and no replacement data is demanded.
For nonempty `V` that condition forces a nonempty family without adding such a
hypothesis. For the diagonal relation one can take the identity affine chart and
the diagonal replacement. The statement also covers a relation already etale,
non-separated bases, non-Noetherian schemes, and arbitrary characteristic.
There is no residue-field or separability hypothesis hidden in the signature.
No statement fault or STATEMENT-DISPUTED issue was found.

Searches actually performed:

- `msearch.py ... leanfinder`, query: "An affine flat locally quasi finite
  equivalence relation has a finite etale cover whose quotient sheaves have
  etale equivalence relation presentations". Eight hits, including local finite
  presentation, ordinary etale morphisms and etale algebra presentations; none
  states the finite-chart quotient replacement theorem.
- `msearch.py ... loogle`, query: `"Scheme", "Etale", "coequalizer"`.
  Zero hits.
- `msearch.py ... grep`, query:
  `etale.*replacement|quotient.*equivalence.*relation|equivalence.*relation.*quotient`.
  Twenty-five hits on general quotient types and unrelated algebra; no match.
- `msearch.py ... leansearch`, query: "An affine flat locally quasi finite scheme
  equivalence relation admits finite etale local quotient presentations by etale
  equivalence relations". Service unavailable (curl timeout); not a no-match result.
- `rg` in `lean/WeilConjectures/AlgebraicGeometry` for equivalence relations,
  etale replacement and fppf quotients found etale-limit replacement modules and
  torsor/general quotient comments, not this statement. An item-id search in
  `lean/WeilConjectures` found no declaration.
- `rg` in `lean/Sheaf` found restriction and quotient-presentation theorems but no
  `fppf_relation_etale_replacement` or `relation_etale_replacement` declaration.
  Reading `EtaleRelationRestrictionQuotient` and
  `FppfGroupoidRestrictionQuotient` identified the existing unrestricted pullback
  construction and the correct lifted-Yoneda sheafification encoding.

Validation: `scompile.py NJ lem-sfb-fppf-relation-etale-replacement` compiled the
module both as a sandbox file and under its delivery module name, without errors
or warnings. Every variable and the universe `u` is explicitly bound.

## Second reading by NJ

This is the worker's separate second pass, not an independent agent review;
the dispatcher explicitly forbids starting other agents. The maintainer's
independent review remains the delivery's independent reading.

I reopened the node and the complete theorem signature. I checked the two
original S-maps, monicity, the sectionwise equivalence condition, affineness,
both flatness hypotheses, both local finite presentation hypotheses and both
Stacks local quasi-finiteness hypotheses. Each is present exactly once and no
separatedness or groupoid-structure assumption was added. I checked the finite
index type, each affine etale chart, joint surjectivity, the iterated restricted
relation, each pair of replacement S-schemes and endpoint maps, monicity and
sectionwise equivalence of the replacement, both etale properties and the
isomorphism of the sheafified quotients. The replacement is not required to be
affine, and the isomorphism is not required to arise from extra specified data.
These match the node rather than strengthen it. The empty-index case and all
universe levels are retained. The existing restriction definition node was added
to `stmt_deps` to make ownership explicit. No new nodes, dependency modules or
statement correction were needed. A leading space in a module-docstring line was
removed during this pass; no mathematical change was needed.
