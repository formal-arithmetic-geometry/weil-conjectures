## Worker report

The delivery states Milne Proposition 16.64 and its uniqueness sentence in
`Sheaf.AlgebraicGeometry.TorusPositiveRaySubgroup`, declaration
`AlgebraicGeometry.TorusCharacterTangent.exists_torus_positiveRay_subgroup`.
Its only theorem has proof `by sorry`. No proof is attempted. The auxiliary
module `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights` defines the
missing character tangent-weight / positive-ray interface with actual data;
it has no postponed theorem, existence choice, or sorry.

The live item is split and reviewed pass, has no Lean record, and is present in
coord/queue.tsv at stage 2. The preserved sandbox contained only dispatcher
brief markers. The inherited BLOCKED ending describes a stage-1 refusal and
is superseded by brief-stage2 §0: a reviewed split is the input to stage 2.
There is no repair note for this item. The accepted statement, proof,
proof_deps, status and review records are retained verbatim. stmt_deps gains
the new definition and the two already recorded definition nodes whose exact
notions the statement uses. There is no statement correction or disputed claim.

Hypotheses and clauses, individually matched:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
  The universe is explicit and is shared by the schemes and all test algebras.
- H is an F-group scheme: `H : Grp (Over (Spec (.of F)))`. Its affine, finite
  type, smooth and connected hypotheses are `[IsAffine H.X.left]`,
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, `[Smooth H.X.hom]`,
  and `[ConnectedSpace H.X.left]`, respectively. Finite type is exactly the
  conjunction used by the recorded def-weil-finite-type-morphism.
- S is an F-group scheme, `S : Grp (Over (Spec (.of F)))`; the finite split
  rank is `(r : ℕ)` and `hS : Nonempty (S ≅ MultiplicativeType.splitTorus F r)`.
  This is an isomorphism of group schemes, with the existing rank-zero product.
  No embedding of S into H or faithful action is assumed.
- The scheme action is `[ModObj S.X H.X]`: its multiplication morphism and
  unit/associativity laws are Mathlib's internal action structure. `hAut :
  ActsByGroupAutomorphisms S H` asserts multiplication preservation on every
  test scheme. Each acting element is invertible by the S-action laws; a
  multiplicative bijection preserves 1 and inverse. Thus this is precisely an
  action by group-scheme automorphisms, with no extra hypothesis on the action.
- Characters are actual morphisms of group objects
  `S ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)`, not arbitrary functions
  on rational points or Lie-algebra characters. `heta : eta.hom.hom ≠ 1`
  excludes the trivial character.
  Pointwise multiplication is the additive character-lattice law translated
  multiplicatively.
- `GrpObj.Lie H.X` is the existing tangent space at the identity. For each
  character, `weightSpace S H χ` is the F-span of vectors whose dual-number
  tangent points transform by the scalar χ(s), for every s in S(F). The
  constant dual-number extension is precomposition with `toUnit`.
  χ(s) is the pullback of the Laurent coordinate T 1, transported from
  Γ(Spec F, O) to F by `Scheme.ΓSpecIso`. This is the differentiated S-action
  on tangent vectors while retaining the group character itself. These
  eigenspaces are already linear because the action preserves the group
  structure; the span is exactly the same space. Because S is a split torus
  over algebraically closed F, S(F) is dense, and testing all F-points equals
  testing the character as a scheme representation. This does not differentiate
  χ or reduce any integer exponent modulo the characteristic.
- `InPositiveRay eta χ` means `∃ m n : ℕ, 0 < m ∧ 0 < n ∧
  χ.hom.hom ^ m = eta.hom.hom ^ n`. This is exactly mχ = nη with positive
  integers; no primitiveness or occurrence of η as a weight is assumed.
- `positiveRaySpace S H eta` is the supremum of those character subspaces,
  hence the subspace underlying the displayed direct sum V_eta. Supremum is
  the sum inside Lie(H); independence of distinct torus characters identifies
  it with the direct-sum notation of the node.
- Existence is `∃ (U : Grp (...)) (i : U ⟶ H)`. Closed subgroup, smoothness,
  connectedness, unipotence and S-stability are the first five conjuncts:
  `IsClosedSubgroupScheme i.hom.hom`, `Smooth U.X.hom`,
  `ConnectedSpace U.X.left`, `SolvableGroupStructure.IsUnipotent U`,
  and `IsStable S H i`. U inherits affineness and finite type from its closed
  immersion into H. Unipotence is the recorded faithful finite-dimensional
  matrix condition on all algebraically closed extension fields.
- `IsStable` tests the represented subfunctor on every test F-scheme W:
  for s in S(W), x in U(W), s·i(x) factors through i. This also includes all
  nonreduced test algebras, and s-inverse gives equality with the translate.
- The tangent equality is
  `(GrpObj.differential i.hom.hom).toLinearMap.range = positiveRaySpace S H eta`.
  The range identifies Lie(U) with its image in Lie(H), as the node intends.
- Each comparison quantifies over every group scheme K and group homomorphism
  j into H, assuming exactly closed subgroup, smoothness, connectedness and
  S-stability. These are the four implication premises. There is no unipotence
  assumption on K and no extra reductivity or characteristic hypothesis.
- The first comparison is inclusion of V_eta in the range of dj, implying
  `∃ f : U ⟶ K, f ≫ j = i`; this is the closed-subgroup containment U ⊆ K.
- The second comparison reverses the tangent inclusion and concludes
  `∃ f : K ⟶ U, f ≫ i = j`, precisely K ⊆ U. The factorization is a
  homomorphism of group schemes, rather than containment of rational points.
- The final quantified clause has the same four premises and equality of
  tangent spaces, concluding `∃ e : K ≅ U, e.hom ≫ i = j`. This is equality
  of the closed subgroup schemes inside H; its compatible isomorphism is unique
  because i is a closed immersion. It covers every smooth connected S-stable
  closed subgroup of the indicated tangent space, even without assuming it
  unipotent in advance.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (the node's mathlib_match also names
  AlgebraicClosure/IsAlgClosure, but this item needs only algebraic closedness).
- def-sc-group-scheme: `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, and
  morphisms of the latter, Mathlib.CategoryTheory.Monoidal.Grp.
- def-sc-group-scheme-subgroup: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, including its
  IsSubgroupScheme/IsMonHom extension and closed-immersion field.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-connected-scheme: `ConnectedSpace`, Mathlib.Topology.Connected.Basic;
  this includes nonemptiness and excludes empty schemes.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact.
- def-sc-gm-ga: `StandardGroupSchemes.multiplicative`, `multiplicativeGroup`,
  and the affine coordinate construction, Sheaf.AlgebraicGeometry.StandardGroupSchemes.
  The additive group is mentioned as terminology in the node but does not occur
  in its assertion, so no second additive-group construction is introduced.
- def-sfb-tori-multiplicative-type: `MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType.
- def-sfb-solvable-group-structure: `SolvableGroupStructure.IsUnipotent`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure.
- sk-d-tangent is closed upstream, with the declarations in its audit:
  `GrpObj.Lie`, `GrpObj.tangentPoint` and `GrpObj.differential`, in the Basic,
  Ring and Differential modules of
  WeilConjectures.AlgebraicGeometry.GroupScheme.Lie. Their full signatures and
  implementation docstrings were read. No replacement tangent space is defined.
- Mathlib `ModObj` and its action on morphisms in
  Mathlib.CategoryTheory.Monoidal.Cartesian.Mod give the existing internal action.

The declared proof dependencies that already have Mathlib interfaces are imported
for stage 3: Mathlib.LinearAlgebra.FreeModule.PID,
Mathlib.AlgebraicGeometry.Geometrically.Connected and (publicly through the
statement imports) Mathlib.AlgebraicGeometry.Morphisms.Smooth. The other proof
nodes have no recorded Lean interface in the current DAG and are not fabricated
as extra hypotheses. The complete accepted eight-step proof plan is transcribed
in the theorem docstring, with all node ids. They will be imported when stated.

Edge cases checked mathematically: r = 0 has only the trivial character, so the
nonzero-character premise has no instance in that case; r is not constrained
positive artificially. H may be the trivial group, and V_eta may be zero even
when eta is nonzero: U is then the trivial smooth connected subgroup. η need not
occur as a weight, and χ may be a positive fractional multiple of η in the lattice;
the positive-integer equation handles both. Negative multiples and the zero
character are excluded for nonzero η in the torsion-free lattice. Nonprimitive
η is allowed. In characteristic p, an action of weight p on G_a is detected by
χ(s)=s^p on actual torus points, not by its zero differential; hence it contributes
the full tangent line. Nonfaithful external actions and arbitrary nonreduced
subgroup test schemes are permitted. Smoothness and connectedness of K are
retained, so infinitesimal kernels and disconnected finite subgroups do not
spuriously enter the two comparisons.

Searches: msearch.py LeanFinder queried the full positive-ray subgroup assertion
(8 irrelevant topology/number-field hits); Loogle queried
`GrpObj.Lie, IsUnipotent, weightSpace` (0 hits; GrpObj.Lie is not in remote
Mathlib); Mathlib grep queried `positive.*ray|torus.*weight|IsUnipotent`
(3 LinearAlgebra.Ray comments, no group-scheme theorem). For the missing notion,
LeanSearch queried the character tangent weight description (8 manifold/LieModule
hits), LeanFinder queried character eigenspaces and positive rational rays
(8 LieModule/root-space hits), and Mathlib AlgebraicGeometry grep queried
`weightSpace|positiveRay|ActsByGroupAutomorphisms|InPositiveRay` (0 hits).
The new node preserves the raw results. Project rg searched WeilConjectures and
Sheaf for the same concepts and names: it found existing tangent, split-torus,
unipotence and internal-action interfaces, all reused, but no character-weight
or positive-ray space. DAG definition searches found no duplicate;
`tools/blueprint_refs.py search 'positive ray'` returned 0 matches.
The exact item id occurs only in its downstream root-subgroup proof and its
stage-1 Smith-basis leaf; it has no Lean declaration. The example compact-object
module has been withdrawn in the live source; the current module convention
from brief-stage2 §4 is followed instead.

Source read: the local Milne PDF, printed pp.346--349, especially formulas
(123)--(125), Proposition 16.64(a),(b), and the following uniqueness sentence.
The current latest blueprint direct-images proof (3) is the ancestor route named
in the accepted split; no unit statement or proof route is changed.

Validation: both delivered modules compile separately in dependency order through
scompile.py against the published live library, with no errors or warnings.
The helper defines all its data without sorry; only the main theorem is postponed.

## New nodes

`def-sfb-torus-character-tangent-weights` introduces internal-action group-law
compatibility, subfunctor stability, the character tangent weight space, the
positive rational ray and its sum of weight spaces. These five definitions
form the single missing notion interface used by the main statement. The source
is Milne Section 16i, (123)--(125), pp.348--349. Existing `ModObj`, group objects,
Lie/tangent-point constructions, multiplicative group and submodule spans are
reused. The three search kinds and project/DAG checks above found no equivalent
existing definition. Its data are explicit equations, spans and suprema.
The blueprint ancestor command reports the inherited null ancestor (also
retained by the accepted stage-1 review); the new node preserves that ancestor
and prepends the item to the inherited via route, with the full source place.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
