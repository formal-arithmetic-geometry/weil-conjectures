## Worker report

The module `Sheaf.AlgebraicGeometry.GroupOpenArithmeticModel` states
`AlgebraicGeometry.AlgebraicSpace.exists_group_open_arithmetic_model` with a single
`sorry` proof. It introduces no definitions and proves no theorems. The natural-language
statement is unchanged. Two already-landed definition nodes are added to `stmt_deps`:
`def-sfb-smooth-integral-group-space` and `def-a1-space-point-topology`. They own the
geometric predicate and the topology actually used; neither node is modified.

### Hypotheses and clauses

- Locally Noetherian scheme S: `{S : Scheme.{u}} [IsLocallyNoetherian S]`.
- Group algebraic space over S: `G : AlgebraicSpace S`,
  `F : (Over S)ᵒᵖ ⥤ GrpCat.{u}`, and `e : F ⋙ forget GrpCat ≅ G.obj.obj`.
  This is actual group data on its functor of points. Morphisms in GrpCat preserve
  multiplication, inverse and identity, so all operations are natural and all group
  identities hold. Conjugating through e gives the operations on G. There is no
  commutativity assumption; in particular, `CommutativeSpaceGroup` is NOT used.
- Smooth, separated, finitely presented, integral geometric fibres:
  `hG : IsSmoothIntegralGroupSpace G`. Unfolding this existing predicate gives,
  in order, the compatible-etale-chart test `MapIsLocally (@Smooth)`,
  `MapIsSeparated` (relative diagonal representable by closed immersions),
  `MapIsLocallyOfFinitePresentation`, quasi-compactness of the structure map,
  quasi-compactness of its relative diagonal, and `GroupSpaceIntegralFibres`.
  The last is irreducibility of every geometric fibre point space together with
  reducedness on every etale scheme chart. `IrreducibleSpace` includes nonemptiness.
  The predicate itself does not impose any group structure or commutativity.
- Open V: `V : OpenSubspace G`, the existing subfunctor with inclusion representable
  by open immersions. Quasi-compactness is `hVqc : CompactSpace (Point V.val.toFunctor)`
  for its existing atlas topology, without a quasi-compactness assumption on S.
- Meeting every geometric fibre: `hV` quantifies over every algebraically closed
  field K in the scheme universe and every `a : Spec K ⟶ S`. It requires
  `Nonempty (Point (pullback (V.ι ≫ p) (yoneda.map a)))`, where p is the existing
  structural map. This is precisely nonemptiness of the open's geometric fibre,
  not existence of a global section of V, nor merely nonemptiness of V itself.
- Every point s: the binder `(s : S)` follows the hypotheses.
- Affine open neighbourhood: `∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧ ...`.
- Affine arithmetic target and map: `∃ (R : CommRingCat.{u})
  (f : U.toScheme ⟶ Spec R), Algebra.FiniteType ℤ R ∧ ...`.
  `Algebra.FiniteType ℤ R` uses the canonical integer algebra structure, and says
  that R is a finitely generated integer algebra. The target T is written as
  `Spec R`, so no independent affine identification is needed.
- Noetherian and finite-dimensional T: `IsNoetherian (Spec R)` and
  `∃ n : ℕ, topologicalKrullDim (Spec R) ≤ (n : WithBot ℕ∞)`.
  A natural bound expresses finiteness and also correctly includes an empty spectrum.
- Nonnegative integer d, model group and open: existential `d : ℕ`,
  `G₀ : AlgebraicSpace (Spec R)`, `F₀ : (Over (Spec R))ᵒᵖ ⥤ GrpCat.{u}`,
  `e₀ : F₀ ⋙ forget GrpCat ≅ G₀.obj.obj`, and `V₀ : OpenSubspace G₀`.
  The model group is not assumed commutative or schematic.
- Smoothness, separatedness, finite presentation, integrality of all model fibres:
  `IsSmoothIntegralGroupSpace G₀`, with the same six constituents as above.
- Quasi-compact model open: `CompactSpace (Point V₀.val.toFunctor)`.
- Constant dimension and fibrewise nonemptiness: for every algebraically closed K
  and `a : Spec K ⟶ Spec R`, the conjunction asserts that
  `topologicalKrullDim (Point (pullback p₀ (yoneda.map a))) = (d : WithBot ℕ∞)`
  and that the corresponding fibre of `V₀.ι ≫ p₀` has a nonempty point space.
  Thus the dimension is exactly the topological Krull dimension specified by the
  item, not the dimension of a chosen atlas or a local tangent dimension.
- Isomorphism of groups after base change:
  `∃ α : (Over.map U.ι).op ⋙ F ≅ (Over.map f).op ⋙ F₀, ...`.
  Restriction to schemes over U computes the fibre product: the test scheme
  already has its fixed map to U. Thus α, after forgetting groups and transporting
  along e and e₀, is the required isomorphism `G|U ≅ G₀ ×_T U`.
  It preserves the entire group structure, not merely the underlying spaces.
- Identification of the opens: for every U-test scheme T and every section x of
  the restricted F, the final equivalence says `e(x) ∈ V(T)` if and only if
  `e₀(α(x)) ∈ V₀(T)`. Since α is invertible, this is equality of the transported
  open subfunctors on ALL scheme tests, including nonreduced tests, and hence the
  required identification of their base changes.

### Dependencies and source reading

Read the full signatures and docstrings of all original statement dependencies:
`Mathlib.AlgebraicGeometry.Scheme` (`Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`),
`Sheaf.AlgebraicGeometry.AlgebraicSpace` (`AlgebraicSpace`, scheme-test
representability and etale maps), `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
(`Smooth`), `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
(`LocallyOfFinitePresentation`), `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`
(`OpenSubspace`), `Mathlib.AlgebraicGeometry.Noetherian` (`IsLocallyNoetherian`),
and `Mathlib.Topology.KrullDimension` (`topologicalKrullDim`). They are used through
public imports, including the public imports of `RegularGroupSpace`.

The additional landed dependency `RegularGroupSpace` supplies `groupSpaceProjection`,
`GroupSpaceIntegralFibres` and `IsSmoothIntegralGroupSpace`; its full source was read.
`AlgebraicSpacePointTopology` supplies `pointTopologicalSpace`; its point construction
and topology were read together with `AlgebraicSpacePointClasses`. The chart predicates
are the existing ones in `AlgebraicSpaceMorphismProperties`; the finite-presentation
constituents agree with the existing `flat_proper_fp_locality` interface. The group
encoding reuses Mathlib's `GrpCat` and `CategoryTheory.Over.map`, whose definitions
were read. No dependency interface required repair.

Plain imports record the stated proof dependencies: `AlgebraicSpaceFlatProperFpLocality`,
`AffineTransitionLimit` (`Scheme.NoetherianApproximation.ofIsAffine`),
`AlgebraicSpaceQuasiCompactFppfLocal`, `AlgebraicSpaceEventuallySurjectiveMap`,
`LimitContainedInConstructible`, and `FiniteTypeGeometryFibreBound`. The remaining
proof-dependency nodes without a Lean record supply the future proof plan in the
item theorem's docstring; no interface was fabricated for them.

Read the supporting local Stacks source `spaces-limits.tex`: the full statements and
surrounding descent arguments at `lemma-descend-finite-presentation` (07SK),
`lemma-descend-smooth` (0CN2), `lemma-descend-separated-morphism` (0851), and
`lemma-descend-surjective` (07SN). These justify descending finite diagrams and
properties, not the geometric-integrality or constant-dimension refinements by
07SK alone. The docstring retains the node's separate constructible-locus and
locally constant group-dimension steps. The latest blueprint direct-image proof
was read at `sec-six-functors-basics/sk-thm-sf-ctf-stability/`;
as the node records, this is an auxiliary node of the inherited longer reduction.
The local Deligne PDF remains recorded as WANTED in the source node; no change to
its source or statement was necessary. The requested CompactObject example is
currently withdrawn in the read clone; its node record was also read.

### Edge cases

Empty S is retained: there is no s to instantiate the conclusion. On a nonempty
base an empty V violates `hV`, since every point has a geometric point and the
empty presheaf fibre has no field-valued point class. The identity of the group
prevents empty group fibres; the integrality predicate also explicitly enforces
this through `IrreducibleSpace`. The trivial group and d = 0 are included. A finite
disconnected group fails the geometric-integrality hypothesis, as it should.
A disconnected base with varying relative dimensions is allowed: d is chosen
after s and U, not globally. No characteristic, reducedness of S, commutativity,
affineness of G, or connectedness of S is imposed. All fields and scheme tests
use the scheme universe u; point-class spaces correctly live in u+1. There is
no independent smaller test universe, no additional universe equality, and no
restriction to field tests in the open-identification clause.

### Searches

Ran the prescribed `msearch.py` searches (actual outputs are in `searches.jsonl`):

- LeanFinder: “A smooth separated group algebraic space with integral geometric
  fibres and a quasi compact open descends locally to a finitely generated integer
  algebra”. Eight hits, including `IsIntegral`, `LocallyOfFinitePresentation`,
  and scheme affine/smooth/finite-type results; none states this approximation.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, GrpObj, Algebra.FiniteType`.
  Zero hits; the service does not know the project's `AlgebraicSpace` identifier.
- Mathlib grep: `arithmeticModel|group.*arithmetic|structure.*SpaceGroup|
  GroupSpaceIntegralFibres`. Twenty-five unrelated modular-form arithmetic hits.
- Targeted Mathlib grep in `AlgebraicGeometry`:
  `arithmeticModel|arithmetic_model|GroupOpen|group_open`. Zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the node id and arithmetic
  group model names found no statement of this node. Broader group-space searches
  found `RegularGroupSpace` and `SeparatedGroupSpaceGeometricScheme`. The former's
  geometric predicates are reused; the latter confirms the existing noncommutative
  group-valued-functor encoding and is about schematic geometric fibres, not models.
- The upstream declaration-name inventory was searched for arithmetic group model
  names; no exact declaration was found. DAG metadata searches located the owning
  nodes of all reused notions. No new definition node was needed.

No statement dispute, statement correction, or dependency fault remains.

### Validation

Compiled the file through `scompile.py` on the server, both as a sandbox module
and as `Sheaf.AlgebraicGeometry.GroupOpenArithmeticModel`: clean, with no errors
or non-sorry warnings. The initial compile exposed one extra closing parenthesis
in the geometric-fibre clause; this was corrected before the successful compile.
The record's `lean.statement` is the signature extracted verbatim from the final file.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
