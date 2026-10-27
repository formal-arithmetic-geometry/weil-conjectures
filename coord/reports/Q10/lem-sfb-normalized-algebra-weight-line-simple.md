## Worker report

The module `Sheaf.RepresentationTheory.NormalizedAlgebraWeightLineSimple` states
`AlgebraicGeometry.normalized_algebra_weight_line_simple`, with its sole proof `sorry`.
The node's mathematical statement, five-step proof, and Lean signature are unchanged.
This repairs returned immutable head 51a28d545474 by recording the existing
natural-action and character-evaluation definitions on two definition nodes.
The two theorem statement dependencies are removed. No Lean definition is duplicated
and no mathematical statement correction is needed.

Read the assigned node, all three original statement dependencies and their records,
the four proof dependencies, and the full signatures/docstrings of the declarations
used. Read Milne, Algebraic Groups (2017), Exercise 4-2 on printed p.97 (PDF p.109):
it gives the normal-subgroup Clifford theorem. The present operator-algebra and
multiplicity-one extension is explicitly an agent lemma, as the node's source says.
Its accepted five-step argument is reproduced in the theorem docstring. The current
blueprint unit `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` concerns
preservation by the six functors; the assigned auxiliary is not that unit's statement.
The H2 return entry for immutable head 51a28d545474 is addressed below.

Clause-by-clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
  `Field` has the commutative ring and nonzero division-ring structure;
  `IsAlgClosed` means every polynomial splits, equivalently every nonconstant
  polynomial has a root. No algebraic extension is chosen or required.
- `G : Grp (Over (Spec (.of k)))` is exactly a group scheme over k, with its given
  structural morphism `G.X.hom`. `IsAffine G.X.left`, `Smooth G.X.hom`, and
  `ConnectedSpace G.X.left` render affine, smooth, and connected. The pair
  `LocallyOfFiniteType G.X.hom` and `QuasiCompact G.X.hom` renders finite type.
- `(V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]` is the
  finite-dimensional vector space. Its nonzero condition is included in
  `hsimple`, through `RationalHighestWeight.IsSimple`'s `Nontrivial V` conjunct.
- `ρ : RationalRepresentation.NaturalRepresentation ...` is the existing family
  of group homomorphisms on `R ⊗[k] V`, natural in commutative k-algebras R.
  `finite_dictionary` identifies these with rational group-scheme representations
  on finite-dimensional V. The reversed tensor order is the canonical symmetry
  with the node's `V ⊗[k] R`. No arbitrary action or comparison is postulated.
- `hsimple` applies `RationalHighestWeight.IsSimple (G := G)` to the actual
  `RationalRepresentation.genericCoaction ... ρ`. That predicate says nonzero
  and every subspace whose coaction lies in the image of `W ⊗ k[G]` is bottom
  or top, exactly the stated rational simplicity condition. `genericCoaction`
  evaluates the universal coordinate-valued point and uses tensor symmetry;
  the dictionary supplies its coassociativity and counit laws.
- `T : Grp ...`, `iT : T ⟶ G`, and
  `[IsClosedSubgroupScheme iT.hom.hom]` give the closed torus subgroup.
  `(r : ℕ)` and `hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus k r)`
  express an isomorphism of group schemes with the r-fold product of G_m.
  The definition includes rank zero. This is not an assumption on k-points alone.
- `A : Subalgebra k (Module.End k V)` is the unital k-subalgebra of operators.
- `hnormalized` quantifies over every commutative k-algebra R, including zero
  and nonreduced rings, and every `g : points G.X R`. The submodule
  `Submodule.span R {f | ∃ a : A, f = (a : Module.End k V).baseChange R}`
  is exactly the image of `R ⊗[k] A` in `End_R(R ⊗[k] V)`: its generators are
  `1 ⊗ a`, and arbitrary tensors are finite R-linear combinations of them.
  Finite dimension and flatness over the field identify this image with the
  stated scalar-extended operator algebra. `LinearEquiv.conj` sends f to
  `ρ_R(g) ∘ f ∘ ρ_R(g)⁻¹`. Equality of its submodule image with the same
  submodule says conjugation carries the operator algebra onto itself.
- `χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)` is the actual
  character, a group-scheme morphism. `Wχ : Submodule k V` is specified by
  `hWχ`, an iff for membership of every w with the full all-algebras weight
  identity, so it cannot be an arbitrary one-dimensional subspace.
  `CentralTorusWeightBlocks.characterScalar χ R t` evaluates χ(t) by pullback
  of the Laurent coordinate and the canonical global functions of Spec R.
  No centrality hypothesis from that helper's owning theorem is used.
- `hdim : Module.finrank k Wχ = 1`, `hvχ : v ∈ Wχ`, and `hv : v ≠ 0`
  render all three weight-vector hypotheses.
- `A.toSubmodule.map (LinearMap.applyₗ v)` is precisely the image of A under
  evaluation at v, namely `{a(v) | a ∈ A}`. The conclusion's first conjunct
  says this subspace is nonzero. Its second quantifies over every k-subspace
  W contained in that image, assumes closure under every a in A, and concludes
  W is zero or the entire image. Subspaces of Av are equivalently such ambient
  subspaces. Thus this is exactly simplicity as explicitly defined by the node;
  neither a semisimplicity assumption nor an extra conclusion is introduced.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (line 62).
  The original algebraic-closure node's match explicitly lists this predicate.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj` (line 43), `Grp` and its
  morphisms; read the group law and inverse diagrams. Read the original
  dependency's fuller interpretation in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, including
  `IsClosedSubgroupScheme` and its inherited homomorphism/injectivity fields.
- `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
  `AlgebraicGeometry.RationalRepresentation.NaturalRepresentation`,
  `genericCoaction`, and the explanatory `dictionary`/`finite_dictionary`.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`:
  `AlgebraicGeometry.RationalHighestWeight.IsSimple`, `IsStable`, and the
  existing group-object/coordinate instances. No private version is made.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks`:
  `AlgebraicGeometry.CentralTorusWeightBlocks.characterScalar`.
  The multiplicative group is the existing
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative`.
- Mathlib `Subalgebra`, `Submodule.map`, `Submodule.span`,
  `LinearMap.applyₗ`, `LinearMap.baseChange`, and `LinearEquiv.conj` provide
  the remaining canonical constructions. Read `applyₗ` in LinearMap/End,
  `baseChange` in TensorProduct/Tower, and `conj` and its application formula
  in Module/Equiv/Basic.
- Plain proof import `Mathlib.RingTheory.SimpleModule.Basic` supplies the
  exact leaf `IsSemisimpleModule.of_sSup_simples_eq_top` (lines 200--202).
  The other three proof prerequisites currently have no Lean record or
  Mathlib match and therefore have no importable module; their node IDs and
  precise uses remain in the proof docstring. They are not needed to type
  this statement and are not duplicated here.

Edge cases checked before writing: rank-zero T is allowed; its only weight
space is V, so multiplicity one forces dimension one and the conclusion holds.
V=0 is excluded exactly by rational simplicity and the given nonzero vector,
as the node requires. For A equal to scalar operators, Av is a line; for A
all operators, Av=V, again with the expected simplicity. No characteristic
restriction is imposed. The all-algebras conditions include dual numbers,
other nonreduced algebras and the zero ring. The zero candidate W is included
in the conclusion. Vector spaces, schemes and test algebras use one arbitrary
universe u, following the existing rational-representation interface; a finite
basis permits every finite-dimensional vector space to be realized in the
base field's universe without a dimension restriction. The test-algebra
universe is not smaller than the base field's, and contains the universal
coordinate algebras needed to detect every displayed identity.

Searches actually run:

- `msearch.py`, leanfinder, query "A multiplicity one torus weight vector
  generates a simple module for a normalized operator algebra in an
  irreducible rational algebraic group representation": eight hits, including
  `RootPairing.isSimpleModule_weylGroupRootRep`, finite-group character
  criteria and Lie generalized weight-space lemmas; no exact statement.
- `msearch.py`, loogle, query `IsSimpleModule, Subalgebra`: zero hits.
- `msearch.py`, grep, query `Clifford|normaliz|torus`, directory
  `RingTheory/SimpleModule`: zero hits.
- `msearch.py`, leansearch, query "A multiplicity one torus weight vector
  generates a simple module for a normalized operator algebra": eight hits,
  including `IsSimpleModule.finrank_eq_one_of_isMulCommutative`,
  `simple_of_finrank_eq_one` and Lie weight spaces; none gives the normalized
  operator algebra conclusion. Dimension one of the whole A-module is not
  the present multiplicity-one weight hypothesis.
- `rg` on `lean/WeilConjectures` for the exact node ID: no hits.
  Searches for `Clifford`, normalized algebra, torus, rational representation,
  coaction and weight-space names in both library roots found the reused
  rational, highest-weight, split-torus and character helpers above.
  The upstream monodromy module's Clifford references concern normal
  abstract subgroups, not this operator-algebra statement.
- `rg` on Mathlib and both library roots and `dag/lean_names_upstream.json`
  for the new declaration name: no collision. The existing
  `SplitTorus.weightSpace` takes a group-algebra coaction; the tangent-weight
  space is specific to Lie algebras. Neither was duplicated: Wχ is a quantified
  submodule uniquely specified by its original all-algebras condition.

Validation: `scompile.py Q10 lem-sfb-normalized-algebra-weight-line-simple`
compiled the sandbox and exact library module successfully, with no errors or
warnings. Theorem proof is solely `sorry`; no diagnostic declarations remain.

No STATEMENT-DISPUTED flag or mathematical node fault was found. The source's
agent-lemma qualification is retained explicitly. The initial delivery had an H2
definition-ownership fault, repaired as follows.


## Repair of H2

Compared the retained sandbox with the returned head described in the entry and
with the current main node. Main still has the original three statement dependencies
and no Lean record. The sandbox held the returned signature and theorem dependencies.
The theorem file is unchanged from the returned delivery; the new delivery rebases
its records on the current main through deliver2.py.

The rejected dependencies were `lem-sfb-rational-representation-comodule-dictionary`
and `lem-sfb-central-torus-faithful-weight-blocks`. Neither conclusion is a hypothesis
or premise in this statement. Both IDs are removed from `stmt_deps`. The imports
remain necessary because the plain real-data definitions are physically declared in
those modules; definition-node records now identify those exact declarations.

`def-sfb-natural-rational-representation-data` owns the existing structure
`AlgebraicGeometry.RationalRepresentation.NaturalRepresentation` and the existing
`genericPoint`, `coordinatePoint`, and `genericCoaction` in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`.
`def-sfb-character-scalar-evaluation` owns the existing
`AlgebraicGeometry.CentralTorusWeightBlocks.characterScalar` in
`Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks`.
Both records use `existing: true`; there is no new module or declaration.
Both definition IDs are cited from the item. No theorem conclusion is imported into
the DAG statement through these records.

The advisory citations are also added: `def-sc-gm-ga` supplies the multiplicative
group; `def-sc-group-scheme-subgroup` supplies the closed-subgroup predicate;
`def-sbc-smooth-morphisms` supplies Smooth; `def-weil-connected-scheme` supplies
ConnectedSpace; and `def-weil-finite-type-morphism` supplies LocallyOfFiniteType
and QuasiCompact. Their node statements and recorded signatures were read. These
notions already appeared in the checked Lean statement; these citations record them.

## New nodes

`def-sfb-natural-rational-representation-data` records, without redeclaring, the
existing natural algebra-point actions and their actual generic-element linear map.
Its statement introduces k, affine G, V, every test algebra, the action and its
naturality equation, the universal and coordinate-induced points, and the exact
symmetry formula for the generic coaction. These are precisely the fields/body of
NaturalRepresentation (lines 49--59), genericPoint (lines 63--64), coordinatePoint
(lines 69--71), and genericCoaction (lines 76--81) in the recorded module. The source
is Milne Chapter 4(a), pp.83--84, Remark 4.1 and equation (25). It does not assert the
comodule dictionary theorem, coassociativity, or a new classification. Its dependency
nodes supply fields, group objects, affine spectra and scalar extension. Edge cases:
arbitrary dimension and V=0 work in the structure; every test algebra, including
zero and nonreduced rings, is quantified; one arbitrary universe is shared as in
the existing interface. The definition-node ownership search found no record of
these four declarations. `def-wf-algebraic-representations` records finite-dimensional
matrix group-scheme morphisms, not the natural-family structure or these generic
maps. `blueprint_refs.py search 'rational representation'` found five matrix-group,
affine-geometry and Lie-comparison nodes; none states this definition interface.

`def-sfb-character-scalar-evaluation` records the exact existing characterScalar
(lines 57--64), which pulls the Laurent coordinate back along t followed by chi
and applies the canonical Spec/global-sections identification. Its statement gives
that formula for all commutative k-algebras and all algebra-valued points, without
assuming affineness, centrality or a torus. Its dependency nodes supply k, group
objects, G_m, Laurent polynomials and affine spectrum. Its source is Milne Chapter
12(a)--(d), pp.230--235. Edge cases include the trivial character, the trivial
group, the zero test ring, nonreduced test algebras and arbitrary characteristic.
`blueprint_refs.py search 'character scalar'` returned zero nodes. The exact
characterScalar declaration had no definition-node owner. The section-module node
`def-sfb-rho-section-module-data` has its own characterValue helper, but the repair
adds no equivalent implementation: it records the specific already existing helper
used in the reviewed signature, exactly as the return requested.

For each new node, the three search kinds were rerun with msearch.py under this
item. The literal queries and actual results are in that node's `mathlib_searches`:
LeanSearch and LeanFinder for natural rational test-algebra representations returned
affine-space/category and abstract representation constructions; neither supplied
this data. Both tools for character evaluation returned Laurent evaluation and
abstract multiplicative-character facts. Mathlib grep for
`NaturalRepresentation|genericCoaction|coordinatePoint` and for
`characterScalar|characterElement` returned zero hits. Direct rg of WeilConjectures
and Sheaf found the exact existing definitions named above. A scan of every DAG
definition node's `lean.declaration`/`lean.declarations` found no owner of them.
The inherited blueprint ancestor is null, as confirmed by blueprint_refs.py ancestor;
the new nodes preserve the item's inherited place and via, with this item prepended.
Neither node claims to be a same-statement blueprint node.

Compilation is rerun for the delivered theorem. The dry-run also checks all existing
names attached to the new nodes via server-side module-mode probes. Independent
review remains the maintainer's, as required by this dispatched repair brief.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
