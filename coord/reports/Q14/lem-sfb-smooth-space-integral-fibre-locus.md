## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothSpaceIntegralFibreLocus` states
`AlgebraicGeometry.AlgebraicSpace.isConstructible_integralGeometricFibreLocus` with
one `sorry`. It supplies three explicit helpers belonging to the fibre locus introduced
in this node: `fieldFibrePresheaf`, `IsIntegralFieldFibre`, and
`integralGeometricFibreLocus`. They have real definitions and no postponed data or proofs.
No separate general-purpose notion, extra theorem, or independent definition node is added.

The statement is unchanged. Its statement dependencies gain the already landed
`def-sfb-proper-curve-moduli`, because that node owns the existing scheme-target chart,
separatedness, and affine-test quasi-compactness predicates used here. This does not impose
properness, curve dimension, flatness, a group law, or any of that node's family conditions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes and algebraic spaces | `{S : Scheme.{u}}`, `X : AlgebraicSpace S`, `B : Over S`; `B.left` is the scheme called B in the node. |
| A morphism X to B | `f : X.obj.obj ⟶ yoneda.obj B`, a natural transformation to the represented scheme, with no representability hypothesis. |
| B Noetherian: quasi-compact and locally Noetherian | `[IsNoetherian B.left]`; Mathlib's class extends exactly `IsLocallyNoetherian B.left` and `CompactSpace B.left`. |
| Smoothness on etale charts | `hsmooth : MapToSchemeIsLocally (@Smooth) X B f`, testing every representable etale scheme chart using its actual induced morphism to B. |
| Separated | `hsep : MapToSchemeIsSeparated X B f`, representability of the relative diagonal by closed immersions on every scheme test. |
| Locally finitely presented | `hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X B f`. |
| Quasi-compact morphism | `hqc : MapIsQuasiCompact f`, compactness of the point space of each affine scheme-test pullback. |
| Quasi-separated morphism | `hqs : MapIsQuasiCompact (pullback.diagonal f)`. Together with hlfp and hqc this is the node's finite-presentation hypothesis. |
| Sheaf fibre product | `fieldFibrePresheaf f K a` is `Limits.pullback f (yoneda.map ...)` in presheaves, the underlying presheaf of the sheaf fibre product. The existing fppf sheaves and represented schemes have their pointwise sheaf pullback; no arbitrary representative or nonempty choice replaces it. |
| Geometric fibre at b | In `integralGeometricFibreLocus`, `K = AlgebraicClosure (B.left.residueField b)` and `a` is `Spec.map` of its algebra map, followed by `B.left.fromSpecResidueField b`. |
| Nonempty and irreducible with atlas topology | First conjunct of `IsIntegralFieldFibre`: `IrreducibleSpace (Point (fieldFibrePresheaf f K a))`. `IrreducibleSpace` includes nonemptiness, and `Point` has the existing `pointTopologicalSpace` final etale-chart topology. |
| Reduced geometric fibre | Second conjunct: every `p : yoneda.obj U ⟶ fieldFibrePresheaf f K a` with `IsEtale p` has `IsReduced U.left`. This is the etale-local definition of a reduced algebraic space, not reducedness or integrality of one arbitrarily chosen atlas. |
| E is the integral geometric-fibre locus | `integralGeometricFibreLocus f` is the set comprehension of exactly that predicate. |
| Constructible subset of the scheme base | First conclusion: `Topology.IsConstructible (integralGeometricFibreLocus f)`. |
| Independent of algebraic closures | Second conclusion quantifies over each b and every `K : Type u`, `[Field K]`, `[Algebra (B.left.residueField b) K]`, `[IsAlgClosure (B.left.residueField b) K]`, identifying the integral predicate for that actual field fibre with membership in the fixed locus. Thus any two choices give equal loci. |
| Every morphism B' to B, no Noetherian assumption on B' | Third conclusion quantifies over arbitrary `B' : Over S` and `h : B' ⟶ B`, without a Noetherian, finite type, or separation assumption. Every scheme map to B gives exactly such an over-S morphism by composing with B's map to S. |
| Corresponding locus for the actual base change equals h inverse image | `integralGeometricFibreLocus (Limits.pullback.snd f (yoneda.map h)) = h.left ⁻¹' integralGeometricFibreLocus f`. The helper accepts the presheaf of the actual pullback directly; no schematicity assumption is added. |
| No properness, group, or nonempty-fibre hypothesis | None occurs among the binders. Irreducibility is only the tested fibre condition inside E, never an assumption about all fibres. |

All schemes and field tests use the common universe `u` prescribed by the algebraic-space
framework. Point classes live in `Type (u+1)`, as defined upstream in this project; no
assumption equates these universes or truncates them to schemes. `autoImplicit` is false.
There are no local notations, local instances, hidden lets, or unbound parameters.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and its scheme-test representability definition
  (def-trf-algebraic-space).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` give the interpretation and closure of sheaf pullbacks.
  The underlying presheaf pullback itself is the existing categorical `Limits.pullback`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`
  (pqf-def-locnoeth and the item's explicit Noetherian convention).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, `Scheme.Hom.residueFieldMap` (def-weil-residue-field).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`; its import
  `Mathlib.FieldTheory.IsAlgClosed.Basic` provides `IsAlgClosure`, the recorded Mathlib
  match of def-weil-algebraic-closure, whose node has no lean field and needs none.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `Point`,
  `pointTopologicalSpace` (def-a1-space-point-topology and its point-class dependency).
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`
  (def-weil-constructible-subset's recorded Mathlib match).
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally`,
  `MapToSchemeIsSeparated`, `MapIsQuasiCompact` (the added existing dependency).
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, already publicly available from
  the scheme/chart modules. The node itself spells out reducedness in its integrality
  definition. No replacement predicate for scheme reducedness is introduced.

All stated proof-dependency modules are imported with plain imports unless also used in
the statement, including the atlas presentation, normal etale components, affine atlas
point topology, generic component splitting, geometric generic cover model, Noetherian
atlas relation, Noetherian constructibility criterion, smooth geometric normality,
common extension fields, and reduced induced closed subscheme. Their existing Mathlib
proof inputs are imported through the Noetherian, finite-presentation, quasi-compactness,
quasi-separatedness and finite-irreducible-component modules. The four proof nodes
lem-sfb-qc-space-affine-etale-atlas, lem-sfb-space-separated-fp-composition,
lem-sfb-space-sepclosed-components-base-change, and
lem-sfb-space-smooth-surjective-fppf-locality are presently unstated; they are not needed
to type this statement, and there is no module to import for them. The theorem docstring
contains all eight proof steps and their node citations verbatim, line-wrapped for Lean.

Edge cases checked mathematically before writing:

- Empty X: each geometric fibre is empty, and `IrreducibleSpace` is false, so E is empty;
  constructibility and the inverse-image equality both hold.
- Empty B: there are no points or closure tests; the constructible set is empty, and
  every map B' to B has empty B'. No inhabitant of B is required.
- Identity B to B: all geometric fibres are single reduced points, so E is the whole base.
- Open immersion U to B: E is exactly U, including empty fibres over its complement;
  this checks that no surjectivity or nonempty-fibre assumption has slipped in.
- Two disjoint copies of B: fibres have two components and are reduced but not integral;
  reducedness alone does not place a point in E.
- Affine line over B: smooth and finitely presented but not proper; fibres are integral,
  so E is the whole base. No properness is needed.
- Base change to a non-Noetherian scheme (e.g. an infinitely generated polynomial
  algebra over a field base) is included in the final universal quantifier. The
  definition of its corresponding locus needs no Noetherian instance.
- Different residue-field algebraic closures are explicitly compared by the second
  conjunct; field-extension compatibility of fibres explains the final equality.

Searches made (2026-10-24), all through the prescribed msearch.py wrapper where applicable:

- LeanFinder: "For a smooth separated algebraic space of finite presentation over a
  Noetherian scheme the locus of geometrically integral fibres is constructible and
  commutes with arbitrary base change". Eight hits: integral scheme morphism properties,
  scheme Chevalley, and global-section integrality. None states this assertion for spaces.
- Loogle: `"GeometricallyIntegral"`. Twelve scheme-only hits including
  `AlgebraicGeometry.GeometricallyIntegral` and stability under base change. This is a
  property of scheme morphisms, not this algebraic-space fibre locus or its constructibility.
- LeanSearch: "constructibility of the locus of integral geometric fibres of a smooth
  algebraic space". Eight hits: ring smooth locus, scheme smoothness, scheme IsIntegral,
  and scheme constructible image. No exact statement.
- Mathlib grep: `geometricallyIntegral|integral.*[Ll]ocus|[Ii]ntegral.*[Ff]ib`, restricted
  to AlgebraicGeometry. Nine hits, all scheme geometric integrality or abelian schemes;
  no algebraic-space locus theorem.
- Project rg in `lean/WeilConjectures` and `lean/Sheaf` for smooth/integral fibre phrases,
  chart and morphism properties, and candidate helper names. The precise blueprint id
  has no upstream declaration. `RegularGroupSpace.GroupSpaceIntegralFibres` uses the same
  existing irreducible-point-space and reduced-etale-chart formulation, but only for
  a group structural morphism and with all fibres integral as a hypothesis; it does not
  supply this general fibre locus or the theorem. No private copy of it is used here.
- Exact name search for `fieldFibrePresheaf|IsIntegralFieldFibre|integralGeometricFibreLocus`
  across Mathlib, WeilConjectures and Sheaf found no declaration before writing this file.

Source read locally: more-morphisms.tex, lemma-nr-geom-irreducible-components-constructible
(Tag 055B), and spaces-more-morphisms.tex, lemma-geometrically-reduced-constructible
(Tag 0E0A), together with the reviewed node's full algebraic-space proof. The node correctly
labels its extension as agent-formulated and does not attribute algebraic-space sources
to the scheme-only 055B. No mathematical fault, statement correction, or dispute was found.

## Second reading by Q14

The assigned worker performed a fresh clause-by-clause pass with the node and completed
Lean file open; the dispatcher explicitly forbids starting a second agent. Independent
maintainer review is supplied by the delivery process, not claimed here as already done.

I checked that `B.left` is the Noetherian scheme, that f is an arbitrary natural
transformation from an algebraic space to its represented base, and that the five
morphism hypotheses are precisely smooth, separated, lfp, qc, and qs. The definition of
the field fibre uses the correct contravariant Spec map and residue-field map to B.
Integrality includes nonemptiness via IrreducibleSpace and reducedness of every etale
chart, rather than integrality of an atlas (which could have many components).
The first conclusion is constructibility on B, not on a point-class proxy for B.
The second ranges over every algebraic closure with its algebra structure.
The last conclusion uses the actual second projection of the categorical pullback and
sets on B', with no Noetherian requirement on B'. No group or properness condition occurs.
The three helpers only name objects and the predicate already introduced in this node.
The sole formatting fault discovered by compilation was a double trailing newline in the
theorem docstring; it was repaired without changing a mathematical signature.
