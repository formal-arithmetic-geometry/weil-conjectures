## Worker report

Stage-2 statement of `lem-sfb-space-lfp-formally-etale-criterion` in
`Sheaf.AlgebraicGeometry.SpaceLfpFormallyEtaleCriterion`, declaration
`AlgebraicGeometry.AlgebraicSpace.etale_on_charts_of_lfp_of_unique_affine_thickening_lifts`.
The only proof is `sorry`. No new definition, dependency repair, or statement correction.

The inherited BLOCKED message concerned a stage-1 unchanged-split refusal. The current
`coord/queue.tsv` assigns this node to stage 2, its accepted Q79 split is preserved, and
it has no Lean record. The stage-handoff instruction in `coord/brief-stage2.md` §0
therefore applies. There is no item-specific repair note in the read clone.

Clause-by-clause rendering:

- A scheme S: `{S : Scheme.{u}}`. No Noetherian, characteristic, or separation assumption.
- Algebraic spaces X and Y over S: `{X Y : AlgebraicSpace S}`. This is the dependency's
  full subcategory of fppf sheaves with representable diagonal and an étale surjective atlas.
- A morphism over S: `(f : X ⟶ Y)`; its presheaf natural transformation is `f.hom.hom`.
- Local finite presentation on every compatible étale scheme chart:
  `(hlfp : MapIsLocallyOfFinitePresentation f)`. This unfolds to the existing
  `MapIsLocally (@LocallyOfFinitePresentation) f`, testing every pair `U V : Over S`,
  representable étale maps `a : yoneda.obj U ⟶ X.obj.obj` and
  `b : yoneda.obj V ⟶ Y.obj.obj`, and `h : U ⟶ V` satisfying
  `a ≫ f.hom.hom = yoneda.map h ≫ b`. The tested property is
  `LocallyOfFinitePresentation h.left`.
- Every pair of affine S-schemes: `∀ (T₀ T : Over S) [IsAffine T₀.left]
  [IsAffine T.left]`. `Over S` includes all base maps. These test schemes use the same
  universe u as the base and the algebraic-space sheaves; there is no independent
  smaller testing universe.
- Every first order thickening over S: `(j : T₀ ⟶ T),
  IsFirstOrderThickening j.left →`. The upstream predicate is exactly
  `IsClosedImmersion j.left ∧ j.left.ker ^ 2 = ⊥`; the morphism in `Over S` imposes
  base compatibility. No topological surjectivity is imposed separately.
- Every a₀ and b over S: natural transformations
  `(a₀ : yoneda.obj T₀ ⟶ X.obj.obj) (b : yoneda.obj T ⟶ Y.obj.obj)`.
  Yoneda represents the schemes over S, without choosing presentations or atlases.
- The solid square commutes: `a₀ ≫ f.hom.hom = yoneda.map j ≫ b`.
- Existence and uniqueness of a lift: `∃! a : yoneda.obj T ⟶ X.obj.obj, ...`.
  The predicate includes both equations, `yoneda.map j ≫ a = a₀` and
  `a ≫ f.hom.hom = b`. Uniqueness ranges over every such natural transformation.
- Conclusion: `MapIsLocally (@Etale) f`. This reuses precisely the same chart test as
  the finite-presentation hypothesis, now with `Etale h.left`. It states the node's
  stipulated chartwise meaning of étaleness without imposing scheme representability
  as an additional hypothesis or requiring a chosen surjective chart.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and `IsRepresentableWith` (the latter two occur inside
  the chart-test definitions).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Thickening`:
  `AlgebraicGeometry.IsFirstOrderThickening`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` and
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation`.
  Its owning, already landed node `def-sfb-space-morphism-properties` was added to
  the item's `stmt_deps`, as allowed by brief-stage2 §5. No private copy was introduced.

The two proof dependencies `lem-sfb-formally-etale-space-chart-locality` and
`lem-sfb-lfp-unique-infinitesimal-lifts-etale` have neither a Lean record nor a Mathlib
match in the current DAG. They require no new interface to state this item; their names
and the complete three-step accepted proof are in the theorem docstring. There is no
module available to import for them. All recorded statement dependencies are public
imports, directly or through the chart-properties module.

Sources checked: the full definitions and theorem in
`literature/stacks-project/spaces-more-morphisms.tex`, definition-formally-smooth-etale-
unramified (lines 2443ff), definition-formally-etale (3491ff), lemma-formally-etale
(3502ff), and lemma-etale-formally-etale (3641ff). These are the source passages of
Tags 04GC, 04GD and 0616. The theorem is exactly implication (2) to (1); the report
and docstring retain the elementary base-structure conversion in the accepted split.

Edge cases checked before writing:

- Empty spaces and empty affine tests are allowed; there is no nonemptiness or
  surjectivity hypothesis on a chart. The empty source is étale on charts.
- Identity thickenings have square-zero zero ideal and are included. Their lift is
  forced to be the initial map; there is no assumption that the thickening is proper.
- For `Spec(k[ε]/ε²) → Spec(k)`, infinitesimal maps give different ε-values, so the
  existence-and-uniqueness condition excludes this non-étale morphism.
- For the closed origin `Spec(k) → A¹_k`, the square-zero test sending the coordinate
  to ε prevents a lift; existence is a substantive condition.
- Identity maps and open immersions meet the criterion; no characteristic restriction
  or invertibility condition was added.
- Local finite presentation is separately assumed, rather than omitted on the basis of
  the lifting property. All scheme/chart/test universes are explicitly bound.

Searches performed for an existing statement, with the prescribed msearch.py wrapper:

- LeanFinder: "Locally finitely presented morphism of algebraic spaces with unique lifts
  across affine first order thickenings is etale". Eight hits, including scheme
  `AlgebraicGeometry.IsEtale`, its formal-unramified instance and composition properties,
  `Scheme.Etale`, and a ring étale-locus criterion. None states the algebraic-space
  infinitesimal criterion.
- LeanSearch: "Infinitesimal lifting criterion for etale morphisms of algebraic spaces".
  Eight hits: ring `Algebra.FormallyEtale`, `RingHom.FormallyEtale`, the standard-étale
  square-zero lifting theorem, scheme `IsEtale` and `Scheme.Etale`, and ring instances
  and decomposition results. None has the node's algebraic-space statement.
- Loogle: `"FormallyEtale", "FinitePresentation"`: zero hits.
- Mathlib grep: `AlgebraicSpace|formallyEtale|formally_etale` in AlgebraicGeometry:
  zero hits. Local Mathlib source inspection confirmed the scheme-level `Etale` and
  `LocallyOfFinitePresentation` declarations and their docstrings.
- Project rg: `AlgebraicSpace` in `lean/WeilConjectures`: zero hits; item-id search there:
  zero hits. Searches for `FormallyEtale|formallyEtale|formally_etale|SpaceChart|
  spaceChart|IsRepresentableWith|firstOrder` in the algebraic-geometry sources found
  scheme lifting results and the existing algebraic-space representability interfaces,
  without this theorem. Searches for `LocallyOfFinitePresentation|formally|Formally`
  in the algebraic-space modules found the reusable `MapIsLocallyOfFinitePresentation`.
  A followup search for `space_lfp_formally_etale|etale_of_lfp_of_unique|
  MapIsLocally.*Etale|FormallyEtale` in algebraic-space modules and
  `dag/lean_names_upstream.json` found no duplicate theorem.
- DAG search for `MapIsLocally|MapIsLocallyOfFinitePresentation` found the landed owning
  node `def-sfb-space-morphism-properties`; its complete statement, Lean record,
  definitions and docstrings were read.

No STATEMENT-DISPUTED issue. The example CompactObject Sheaf module is now withdrawn;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, which was read for
current module/docstring conventions.

Validation: scompile.py compiled this file in both sandbox and library module modes
cleanly (7.5 s and 9.1 s). Only the prescribed wrapper was used; no global build or
live-source edit was performed.

## Second reading by Q68

A separate second pass by the same worker reopened the node and the finished file.
No independent worker was started, as the dispatcher brief forbids it; the maintainer
performs the independent review. This pass checked: S and both spaces use the recorded
category; local finite presentation uses every compatible chart; affine tests are over S;
j uses the upstream square-zero closed-immersion predicate; the commutative solid square
has the correct orientation; `∃!` covers both lift equations and all lifts; and the
conclusion tests étaleness on the same charts without surjectivity restrictions. No
hypothesis or conclusion mismatch was found. The initially considered inline chart tests
were replaced before delivery by the existing landed chart-test declarations, and their
owning node was added to stmt_deps. No source-statement correction was needed.
