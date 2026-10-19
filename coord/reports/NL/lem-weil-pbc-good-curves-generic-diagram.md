## Worker report

States `AlgebraicGeometry.exists_good_curves_generic_diagram` in
`Sheaf.AlgebraicGeometry.GoodCurvesGenericDiagram`. The only proof is `by sorry`.
The module docstring cites Stacks Tag 0GK7, assertions (1)-(8); the theorem
has the complete ten-step DAG proof and its input identifiers in its docstring.
Read the local Stacks source at `more-morphisms.tex`, lemma-make-good-curves,
including the statement and the proof. No statement correction, new node, or
dependency module is needed.

Clause-by-clause correspondence:

- Schemes and morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Separated: `[IsSeparated f]`.
- Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, exactly the convention node's Stacks 01TP meaning.
- Generic point of an irreducible component: `(η : S)` and
  `hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z`.
- Generic fibre dimension at most one: `hdim : topologicalKrullDim (f.fiber η) ≤ 1`.
- Open neighbourhood: `∃ (U : S.Opens) (_ : η ∈ U)`.
- Base cover: `(V : Scheme.{u}) (g : V ⟶ U.toScheme)` with
  `IsFinite g ∧ Surjective g ∧ UniversallyInjective g`.
- Finite family: `(n : ℕ)` and `(T Y Ybar : Fin n → Scheme.{u})`.
  Any finite family can be reindexed by `Fin n`; no nonemptiness is imposed.
- Finite étale maps: `(t : ∀ i, T i ⟶ V)` and
  `∀ i, IsFinite (t i) ∧ Etale (t i)`; this is the unbundled object condition
  of the recorded `(@IsFinite ⊓ @Etale).Over ⊤ V` specialization.
- Diagram maps: `(j : ∀ i, Y i ⟶ Ybar i)` and
  `(p : ∀ i, Ybar i ⟶ T i)`; the map `Y i ⟶ T i` is their composite.
- Base-changed X is literally `pullback f (g ≫ U.ι)`.
- Coproduct and its map: `ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)`.
- Commutativity over V: for every i,
  `Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i`.
- Finite surjective ν: `IsFinite ν ∧ Surjective ν`.
- Open immersions: `∀ i, IsOpenImmersion (j i)`.
- Smooth surjective open curves: `∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)`.
- Smooth proper compactifications: `Smooth (p i) ∧ IsProper (p i)`.
- Every compactification fibre geometrically connected and dimension at most one:
  for each `s : T i`, `GeometricallyConnected ((p i).fiberToSpecResidueField s)`
  and `topologicalKrullDim ((p i).fiber s) ≤ 1`. The geometric property is
  applied to the fibre's actual residue-field structure morphism.
- Open W: `∃ W : (pullback f (g ≫ U.ι)).Opens`.
- W dense in every fibre over V: for every v, `Dense` of the preimage of W
  under `(pullback.snd f (g ≫ U.ι)).fiberι v`.
- W_i dense in every fibre over T_i: for every i and s, `Dense` of the preimage
  of W under `(j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν`. Pulling back W along
  the component inclusion is exactly `ν⁻¹(W) ∩ Y_i`; pulling that open back
  to the fibre is the set tested here.
- Thickening: `IsThickening (pullback.snd ν W.ι)`; its source is ν⁻¹(W)
  and target is W. The recorded predicate is closed immersion AND surjective,
  without any square-zero condition.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Convention node: no declaration of its own, as its record explicitly says;
  use Mathlib `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`,
  `QuasiSeparated`, `IsFinite`, `Surjective`, `UniversallyInjective`,
  `IsOpenImmersion`, and `IsProper` for its property conventions.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.snd` (the pullback module arrives through Fiber).
- `Mathlib.AlgebraicGeometry.Limits`: the discrete colimit instance,
  `sigmaOpenCover`, `disjoint_opensRange_sigmaι`; its scheme coproduct and
  standard `Sigma.ι` implement the family node's recorded Mathlib match.
- `Mathlib.CategoryTheory.MorphismProperty.Comma`: `MorphismProperty.Over`,
  and `OverAdjunction`: `MorphismProperty.Over.pullback`; read their signatures.
  The statement needs only the finite étale object's unbundled property,
  `IsFinite (t i) ∧ Etale (t i)`, not the category's arrows or base-change functor.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`; `Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`: `GeometricallyConnected`;
  this is the connected alternative explicitly named by the dependency's match.
- `Sheaf.AlgebraicGeometry.Thickening`: `IsThickening` (full definition read).

Public imports cover statement dependencies. Nonpublic imports include every
proof-dependency module having a non-null recorded module and not already public:
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
- `Sheaf.FieldTheory.PurelyInseparableDegreePIntermediate`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`.
- `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Sheaf.AlgebraicGeometry.DescendFinite`.
- `Sheaf.AlgebraicGeometry.DescendSurjective`.
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`.
- `Sheaf.AlgebraicGeometry.EventuallyProper`.
- `Sheaf.AlgebraicGeometry.DescendClosedImmersion`.
- `Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore`.
- `Mathlib.AlgebraicGeometry.Properties`.

Proof dependencies without a recorded Lean module cannot yet be imported; they
remain named in the theorem's proof docstring and in the unchanged DAG. No
imports of available proof dependencies were omitted to avoid a cycle.

Edge cases checked before writing:

- Empty generic fibre has dimension ⊥, hence satisfies the bound; `n = 0`
  permits the empty coproduct, and the surjectivity conclusion then forces
  the base-changed X empty. W may be empty, and density in empty fibres is valid.
- Zero-dimensional fibres are included by `≤ 1`, rather than requiring curves
  to have exactly dimension one.
- No integrality, reducedness, Noetherian, characteristic, algebraic-closure,
  affine-base, or nonempty-family assumptions have been added.
- η itself makes the base nonempty; no independent nonemptiness hypothesis.
- All schemes use the same explicit universe u. The finite index type `Fin n`
  works at every u and excludes no cardinalities. All variables are explicitly bound.
- No density of j's image, quasi-compactness of W, or first-order thickening
  condition is asserted, since the node does not assert those stronger clauses.

Searches for an existing statement (msearch.py, item-specific log):

- LeanFinder: "Separated finite presentation scheme morphism generic fibre
  dimension at most one admits finite radicial cover and finite surjection from
  smooth curves with proper smooth compactifications". Eight hits: generic
  finite/proper/smooth facts; none states this diagram theorem.
- Loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.GeometricallyConnected`.
  Zero hits.
- Mathlib grep: `good.curves|make.good.curves|generic.diagram` in AlgebraicGeometry.
  Zero hits.
- LeanSearch: "finite radicial cover of base gives smooth proper curve
  compactification near generic point". Unavailable: Internal Server Error.
- Direct rg: `good.curves|make.good.curves|generic.diagram|` followed by the item id,
  in upstream WeilConjectures and project lean/Sheaf. Zero hits.
- Direct rg of finite étale definitions located upstream fundamental-group
  modules, but their notions are the existing finite étale category, not this
  existence statement; the dependency's recorded unbundled specialization suffices.

Validation: scompile.py compiled the delivered module alone on the server,
nice 19, two threads, 60 seconds per file; 1.5 seconds, no errors or warnings.

## Second reading by NL

Independently read the node statement, all twelve statement-dependency nodes,
their recorded declarations and matches, the delivered module, and the complete
statement and proof of Stacks `more-morphisms.tex`, `lemma-make-good-curves`
(Tag 0GK7). The preceding section introduces no standing hypotheses beyond
schemes. The source assumes separatedness and finite presentation, not a
Noetherian, reduced, integral, or characteristic restriction. Its temporary
reductions in the proof are not hypotheses of the lemma.

Object, hypothesis, and conclusion checklist (each verdict is exact):

1. Arbitrary schemes S and X and a morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   These are Mathlib schemes and scheme morphisms, not affine schemes or varieties.
2. Separated f: `[IsSeparated f]`, the closed-diagonal condition.
3. Finite presentation: `[LocallyOfFinitePresentation f] [QuasiCompact f]
   [QuasiSeparated f]`, precisely the Stacks 01TP convention specified by
   `def-weil-pbc-scheme-conventions`. The last property also follows from
   separatedness, so its explicit inclusion does not strengthen the hypotheses.
4. A generic point of an irreducible component: `(η : S)` and
   `hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z`. Maximal
   irreducibility and `closure {η} = Z` use exactly the recorded topology notions.
5. Dimension of the scheme-theoretic generic fibre at most one:
   `hdim : topologicalKrullDim (f.fiber η) ≤ 1`.
6. An open neighbourhood of η: `∃ (U : S.Opens) (_ : η ∈ U)`.
7. A cover of that neighbourhood: `(V : Scheme.{u}) (g : V ⟶ U.toScheme)`
   followed by `IsFinite g ∧ Surjective g ∧ UniversallyInjective g`.
8. A finite, possibly empty, family: `(n : ℕ)` and
   `(T Y Ybar : Fin n → Scheme.{u})`. Reindexing any finite family by `Fin n`
   loses no data relevant to this existential statement.
9. Finite etale T_i over V: `(t : ∀ i, T i ⟶ V)` and
   `∀ i, IsFinite (t i) ∧ Etale (t i)`. This unbundles exactly the object
   condition of `(@IsFinite ⊓ @Etale).Over ⊤ V`; it adds no condition on arrows.
10. Arrows Y_i to their compactifications and then T_i:
    `(j : ∀ i, Y i ⟶ Ybar i) (p : ∀ i, Ybar i ⟶ T i)`.
    The structure map of Y_i is the specified composite `j i ≫ p i`.
11. X_V is the actual base change: `pullback f (g ≫ U.ι)`.
    The omitted intermediate symbol X_U denotes the canonical base change to U;
    its further base change is canonically this pullback. No extra choice or
    property of X_U is lost by suppressing that redundant object.
12. Map from the disjoint union: `(ν : (∐ Y) ⟶ pullback f (g ≫ U.ι))`.
    `∐ Y` and `Sigma.ι Y i` are the recorded scheme coproduct, not a set union.
13. Commutative diagrams over V: for every i,
    `Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i`.
    This is exactly equality of the two structure maps on each component;
    the coproduct universal property supplies the displayed whole diagram.
14. Finite surjective ν: `IsFinite ν ∧ Surjective ν`.
15. Open immersions: `∀ i, IsOpenImmersion (j i)`. Equivalently the induced map
    of disjoint unions is an open immersion, as in source assertion (5).
16. Smooth surjective Y_i over T_i:
    `∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)`.
17. Smooth proper compactifications: for each i,
    `Smooth (p i) ∧ IsProper (p i)`.
18. Every compactification fibre is geometrically connected:
    `∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s)`.
    The property is on the residue-field structure map of the fibre, as required;
    it is not merely ordinary connectedness of its underlying space.
19. Dimension bound on those same fibres:
    `topologicalKrullDim ((p i).fiber s) ≤ 1`, for every s and i.
20. One open W in X_V: `∃ W : (pullback f (g ≫ U.ι)).Opens`.
    This quantifier follows all diagram objects and properties and precedes
    the simultaneous density and thickening clauses, exactly as the node requires.
21. W dense in every fibre over V:
    `∀ v : V, Dense ((pullback.snd f (g ≫ U.ι)).fiberι v ⁻¹' (W : Set _))`.
    The preimage is a subset of the actual scheme-theoretic fibre with its
    induced topology; the recorded fibre homeomorphism identifies the usual
    topological-fibre formulation.
22. W_i dense in every fibre over T_i: for every i and s,
    `Dense (((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _))`.
    First pulling W back to Y_i gives precisely ν⁻¹(W) intersected with that
    coproduct component; its further pullback to the fibre is the displayed set.
23. The restricted map is a thickening:
    `IsThickening (pullback.snd ν W.ι)`. The pullback has source ν⁻¹(W), target W,
    and the recorded predicate is `IsClosedImmersion ... ∧ Surjective ...`.
    There is no added nilpotence bound or square-zero assertion.

Dependency inspection: opened Mathlib's `Scheme.lean` (the scheme structure),
`Fiber.lean` (`Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`),
`Topology/Irreducible.lean` (`irreducibleComponents`), `Topology/Sober.lean`
(`IsGenericPoint`), and `Topology/KrullDimension.lean` (`topologicalKrullDim`).
Read the morphism classes in `Morphisms/FinitePresentation`, `Separated`,
`QuasiCompact`, `QuasiSeparated`, `Finite`, `UniversallyInjective`, `Smooth`,
`Etale`, `Proper`, and `UnderlyingMap`. They have the scheme domains and
property meanings used above. Read `Geometrically/Connected.lean`:
`GeometricallyConnected f` tests connectedness after field-valued base changes,
which specializes correctly to each fibre's residue field. Read the whole
project `Sheaf.AlgebraicGeometry.Thickening` definition module. In particular,
the dependency node's principal name `IsFirstOrderThickening` does not mean that
all citers must use first order: its `declarations` also explicitly records the
correct `IsThickening` used here.

Read `MorphismProperty/Comma.lean` (`MorphismProperty.Over`) and
`MorphismProperty/OverAdjunction.lean` (`Over.pullback`): the finite-etale
notion has exactly the unbundled object data used above. Read the discrete
colimit instance, `sigmaOpenCover`, and `disjoint_opensRange_sigmaι` in scheme
`Limits.lean`: they supply the correct coproduct with open disjoint components
and cover, for the small type `Fin n` at every universe u. Thus no missing
notion or unusable statement dependency requires a new node or sibling module.
The sandbox contains only the item node and its module; no new definition node,
dependency module, existing-declaration claim, or statement correction to audit.

Edge cases: `n = 0` is allowed. If the generic fibre is empty, the empty family
and eventually empty X_V are permitted; ν's surjectivity correctly forces X_V
empty in this case, and both density clauses allow empty fibres. Empty S has
no η and therefore yields no inadmissible input. Zero-dimensional fibres are
included by `≤ 1`; they are not forced to have dimension exactly one. There is
no characteristic, algebraic-closure, Noetherian, integrality, or reducedness
hypothesis. All schemes lie in arbitrary explicit universe u, with no
independent smaller test universe and no unbound universe or variable. A finite
index type in universe zero is small in every u and excludes no finite family.
The objects are schemes, so no separate additive zero-object case arises.

Independent duplicate searches, using different wording from the first reader:

- LeanFinder via msearch: `finite universal homeomorphism near generic point
  giving smooth proper models for relative curves`: eight hits, all general
  smoothness, relative dimension, or etale declarations; no diagram theorem.
- Loogle via msearch: `AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.UniversallyInjective`: zero hits.
- Grep via msearch: `good_curve|makeGoodCurve|goodCurves|0GK7`: zero hits.
- Direct rg over Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf: `good.?[Cc]urve|make.good.curve|exists_good_curves|0GK7|` followed by
  `radicial.*(diagram|compactification)|compactification.*radicial`: zero hits.
- LeanSearch via msearch: `A relative curve near a generic point admits a finite
  surjective map from smooth curves with smooth proper compactifications after
  a finite radicial change of base`: unavailable, Internal Server Error.
  This is an unavailable service, not evidence of absence; the successful
  semantic, signature, and direct-source searches provide the duplicate check.

No mathematical or encoding mismatch found; no Lean or node change was needed.
The source citation and blueprint tag are present in both docstrings. The
statement docstring renders every one of the ten node proof steps, including
its input identifiers and empty-family treatment. The sole theorem has only
`by sorry`, no definition data or auxiliary proof. The available recorded
proof-dependency modules are imported, publicly when also statement dependencies
and otherwise nonpublicly. No file-local notation, instance, private definition,
or hidden `let`/`show` binder occurs. The node's lean.statement is verbatim the
file signature. Second reading changed only this report.

Second-reader validation: scompile.py compiled the sole delivered module cleanly
on the server in 1.5 seconds, nice 19, two threads, 60-second per-file limit.
Signature equality and the 100-column limit were also checked.
