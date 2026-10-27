## Worker report

Q61 states `AlgebraicGeometry.AlgebraicSpace.eventually_isClosedImmersion_of_sheafLimit`
in `Sheaf.AlgebraicGeometry.SpaceEventualClosedImmersion`. The only theorem has proof
`sorry`; there are no new definitions, helper theorems, or changed natural-language
statements. Source read: `literature/stacks-project/spaces-limits.tex`,
`lemma-finite-type-eventually-closed`, Tag 0828(1), statement and proof.

The previous worker's stage-1 live-wins objection is inapplicable: the current
`coord/brief-stage2.md` section 0 explicitly says that an accepted stage-1 split is
input to stage 2. The node is queued for stage 2 and has no Lean record. Its accepted
statement and eight-step split are preserved.

Every hypothesis and conclusion is rendered as follows:

- The scheme S is `{S : Scheme.{u}}`. The algebraic space B is `(B : AlgebraicSpace S)`.
  The source, all stages, and the limit are algebraic spaces in this same existing
  category, whose objects are fppf sheaves with representable diagonal and an atlas.
- The small nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. This uses the project's current directed-set convention,
  without requiring antisymmetry. The index lives in the scheme universe.
- The inverse system over B is `D : Iᵒᵖ ⥤ Over B`. Its morphisms, cone arrows, and h
  commute with the maps to B by their `Over` types. No extra compatibility assumption
  or choice of base morphism is introduced.
- The quasi-compactness of every X_i is `hqc`: existence of a scheme U over S,
  `CompactSpace U.left`, and a map from its Yoneda presheaf that satisfies both
  `IsEtale a` and `IsSurjective a`. This is exactly the node's atlas definition,
  rather than an assumption that X_i is a scheme or is quasi-separated.
- Affine transitions are `haff`, namely `IsRepresentableWith
  (fun _ _ p ↦ IsAffineHom p.left) (D.map f).left.hom.hom` for every transition.
  The existing representability predicate supplies a representing scheme pullback
  and requires its projection to be affine. Testing all schemes with affine
  projections is equivalent to the node's affine-target scheme tests.
- The limit X is `c.pt.left` for `c : Cone D`. The hypothesis `hc` is `IsLimit` of
  the cone after forgetting B and including algebraic spaces in fppf sheaves.
  Thus it asserts precisely the sheaf-limit property in the node, rather than
  only a universal property with algebraic-space test objects. X is algebraic
  because the cone is valued in `Over B` for B in `AlgebraicSpace S`.
- T and the B-morphism h are `(T : Over B) (h : T ⟶ c.pt)`. The closed immersion
  hypothesis is `hclosed`, with the existing `IsRepresentableWith` predicate
  applied to the Mathlib `IsClosedImmersion` property of each scheme projection.
- T to B locally of finite type is `hlft : MapIsLocally (@LocallyOfFiniteType) T.hom`.
  It uses exactly every compatible pair of representable etale scheme charts as
  stipulated by the node. It does not assert local finite presentation or finite
  presentation of this map.
- The eventual conclusion is `∃ i₁ : I, ∀ i : I, i₁ ≤ i → ...`. The tested map is
  the actual composite `(h.left ≫ (c.π.app (op i)).left).hom.hom`; its scheme-test
  closed-immersion property includes representability at every such stage.
- The preliminary quasi-separatedness, quasi-compact morphism, local finite
  presentation and finite presentation descriptions in the node are conventions,
  not further hypotheses or conclusions of clause (1). No such assumption is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsAlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`; the full-subcategory inclusion
  is Mathlib's `ObjectProperty.ι`. These definitions are reused without copies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`; imported as the statement dependency's module.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `IsClosedImmersion`. Their signatures and docstrings were read.
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  the explicit universe u and `I : Type u` implement its relevant size requirements.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
  Its already-landed owner `def-sfb-space-morphism-properties` is added to
  `stmt_deps`, as permitted for landed definition nodes. This supplies the common
  algebraic-space chart-test interface rather than defining another predicate.

The file also imports the recorded, available proof-dependency modules:
`Sheaf.SecPurity.QcMapAffineEtaleNeighbourhood` (exists_affine_etale_neighbourhood),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
(representable_etale_scheme_tests),
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition` (exists_limit_affine_transition),
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` (global sections colimit),
`Mathlib.AlgebraicGeometry.Morphisms.Etale` (Etale), plus the statement imports
for the affine-cover closed-immersion and local-finite-type tests. Four current
proof dependencies have no recorded Lean declaration and therefore no module to
import: lem-trf-space-qc-finite-affine-atlas-refinement,
lem-sfb-space-affine-limits-schematic-stages, lem-sfb-space-affine-locality,
and lem-sfb-space-closed-immersion-fppf-descent. Their roles remain explicit in the
proof docstring. They are not required to type the statement.

Edge cases checked before drafting: a singleton directed system yields the original
closed immersion; the empty T gives the empty closed subspace at every stage;
empty X_i force the compatible limit and T to be empty on its tail; non-surjective
transitions remain allowed; the generator argument permits zero generators; B and
X_i need not be quasi-separated or separated; B need not be a scheme. The bound i₁
exists because the directed set is nonempty, as required by the source. The general
preorder presentation retains the non-antisymmetric case.

Searches made through msearch.py, recorded in searches.jsonl:

- LeanFinder: "A closed immersion from a locally finite type algebraic space into
  an inverse limit of quasi compact algebraic spaces with affine transitions is
  eventually a closed immersion at finite stages". Eight hits: scheme results
  on affine limits, finite type, and closed immersions; no algebraic-space match.
- Loogle: "AlgebraicGeometry.IsClosedImmersion, CategoryTheory.Limits.IsLimit".
  Zero hits.
- grep in Mathlib/AlgebraicGeometry: "eventually.*[Cc]losed|[Cc]losed.*eventually|AlgebraicSpace".
  Zero hits.
- LeanSearch: "A closed immersion of a locally finite type algebraic space into
  an inverse limit with affine transition maps is eventually a closed immersion".
  Eight scheme closed-immersion hits, no matching statement.
- rg of lean/Sheaf and lean/WeilConjectures for eventual closed immersions and the
  item id: no declaration of this item. The closest upstream declaration is
  `AlgebraicGeometry.eventually_isClosedImmersion_of_isLimit` in
  `WeilConjectures.AlgebraicGeometry.EventuallyClosedImmersion`, Tag 0A0N.
  Its full signature was read: it concerns scheme structure maps from a system
  with closed transitions into a fixed qcqs scheme target; it has different
  objects, map direction, and hypotheses. ClosedLimitLfpStabilization is likewise
  a different scheme theorem. Neither can be recorded as this node.
- The already-landed `MapIsLocally` definition and algebraic-space interfaces were
  found by rg in lean/Sheaf/AlgebraicGeometry and checked against their DAG records.

No statement dispute, dependency-interface repair, or new node is needed.

Validation: scompile.py compiled this file in sandbox and library module modes
cleanly (2.0 s and 1.7 s before the explicit public-import cleanup). The delivery
wrapper will repeat compilation of the final file and run server preflight.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
