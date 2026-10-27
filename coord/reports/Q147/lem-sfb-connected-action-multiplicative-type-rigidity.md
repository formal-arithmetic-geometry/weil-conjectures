## Worker report

The module `Sheaf.AlgebraicGeometry.ConnectedActionMultiplicativeTypeRigidity`
states `AlgebraicGeometry.connected_action_multiplicativeType_rigidity`, with
one `sorry` and no definitions or proved lemmas. The statement of the DAG node
is unchanged. Its `stmt_deps` additionally cites the already landed
`def-sfb-diagonalizable-group`, whose exact construction is used rather than
introducing another diagonalizable-group definition. There are no new nodes
or dependency repairs.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, printed
pp.243--244 (PDF pages 255--256), Theorem 12.36 and Corollary 12.37.
The corollary says that a connected algebraic group acting by homomorphisms
on a group of multiplicative type acts trivially. The Lean keeps all the
additional hypotheses that this DAG node explicitly includes. The docstring
reproduces its five-step coefficient proof, including the universal algebra
points and orthogonal idempotents, without replacing the nonreduced case by
a density argument.

Every hypothesis and clause is rendered as follows:

- Algebraically closed field F: `(F : Type u) [Field F] [IsAlgClosed F]`.
- F-group schemes G and D: `(G D : Grp (Over (Spec (.of F))))`.
  Each `Grp` carries its actual `GrpObj` structure on the underlying `Over`
  object. Thus the base and all group diagrams are built into the objects.
- Affineness of both schemes: `[IsAffine G.X.left] [IsAffine D.X.left]`.
- Finite type of both structure maps: `LocallyOfFiniteType` and
  `QuasiCompact` on each of `G.X.hom` and `D.X.hom`, the recorded convention
  for `def-weil-finite-type-morphism`. Although affineness supplies
  quasi-compactness and smoothness supplies local finite type on G, these
  binders spell out the node's stated finite-type requirements.
- Smooth G: `[Smooth G.X.hom]`.
- Connected G, including nonemptiness: `[ConnectedSpace G.X.left]`.
- D of multiplicative type in the node's explicit sense: `hD` existentially
  quantifies `M : Type u`, `AddCommGroup M`, `AddGroup.FG M`, and
  `Nonempty (D ≅ diagonalizableGroup F M)`. The isomorphism is in the
  category of group objects, not just the category of schemes.
  `diagonalizableGroup` is the existing spectrum of the additive group
  algebra with coproduct e_m ↦ e_m ⊗ e_m, counit 1 and antipode e_(-m).
  We do not replace this explicit hypothesis by the alternative definition
  involving a closed subgroup of a torus after another field extension.
- An action a: `(a : ModObj G.X D.X)` is Mathlib's internal action object;
  `a.smul` is the actual morphism G ×_F D → D. Its `one_smul` and
  `mul_smul` fields supply exactly the unit and composition laws of an action.
- Action by automorphisms: `hAut` quantifies over every `A : Type u` with
  `CommRing A` and `Algebra F A`, and each point
  `g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ G.X`.
  It requires a `MulEquiv` of the analogous D(A) group whose value at every
  d is `lift g d ≫ a.smul`. A multiplicative equivalence supplies both
  preservation of the group law and bijectivity; the induced maps are the
  given action, not independently chosen maps.
- Naturality under change of A is automatic from the fact that this formula
  evaluates a single morphism in `Over (Spec F)`: precomposition by Spec of
  an algebra map commutes with cartesian `lift` and composition. The action
  map, rather than a family of arbitrary set actions, is quantified.
- The conclusion is the literal morphism equality
  `a.smul = snd G.X D.X`. Evaluation after `lift g d` gives the node's
  equivalent formula a(g,d)=d, with the usual second-projection identity.
- There is no smoothness, connectedness or reducedness hypothesis on D,
  no torsion-freeness hypothesis on M, and no characteristic restriction.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: its `mathlib_match` explicitly includes
  `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic. No algebraic closure
  extension is needed because F itself is algebraically closed.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and bundled
  `CategoryTheory.Grp`, Mathlib.CategoryTheory.Monoidal.Grp; the interpretation
  over Spec F was also checked in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The group on T-points
  is the existing `CategoryTheory.GrpObj.Hom.group`, from
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, enabled by scoped `MonObj`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.
  FiniteType and QuasiCompact.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, as recorded on the node.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  Mathlib.Topology.Connected.Basic, whose nonempty field was checked.
- Added landed dependency `def-sfb-diagonalizable-group`:
  `AlgebraicGeometry.diagonalizableGroup`,
  Sheaf.AlgebraicGeometry.DiagonalizableGroup. Read its entire construction
  through `hopfSpec` and `CommHopfAlgCat.of F (AddMonoidAlgebra F M)`.
- Existing action API: `CategoryTheory.ModObj`,
  Mathlib.CategoryTheory.Monoidal.Mod; no new action notion is needed.
- Proof-only imports expose the existing spectrum/pullback, tensor-product
  and clopen-idempotent declarations: `AlgebraicGeometry.pullbackSpecIso`,
  `Algebra.TensorProduct.productMap`, `Algebra.TensorProduct.ext`, and
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`.
  These implement the node's proof dependencies; Spec itself is already
  publicly available through the statement imports. ConnectedSpace is a
  shared statement/proof dependency and is publicly imported.

Edge cases checked before writing:

- M=0 gives the trivial diagonalizable group; the statement still applies.
- Torsion M is allowed. In characteristic p, M=Z/p gives μ_p, including
  its nilpotents; no reducedness or smoothness of D enters the statement.
- In characteristic different from p, M=Z/p permits a disconnected finite
  diagonalizable group; no connectedness of D is imposed.
- G=Spec F with its trivial group structure is included. An empty G is
  excluded by ConnectedSpace and in any event has no identity section.
- The zero F-algebra is allowed as a test algebra; no `Nontrivial A`
  assumption was added. The group of points there is the singleton group.
- A nonconnected parameter can act nontrivially, for example inversion by
  a constant group of order two on G_m, so the connectedness requirement is
  meaningful. Multiplication by G_m on itself is an action but does not
  satisfy hAut, matching Milne Remark 12.39(b).
- The arbitrary universe u is explicit. Fields, schemes, group-algebra
  basis indices and test algebras all use u, so test algebras are never in
  a smaller universe than the base field. All algebra-valued universal
  points needed by the coordinate proof fit in this same universe.

Searches made with the prescribed msearch.py wrapper (Q147 and this item):

- LeanFinder: `Every action of a connected smooth affine algebraic group on
  a group scheme of multiplicative type by group automorphisms is trivial`.
  Eight hits, all unrelated Galois-category transitivity results; no match.
- Loogle: `"GrpObj", "MonoidAlgebra"`. Zero hits.
- Mathlib grep: `multiplicative.?[Tt]ype|[Dd]iagonaliz|[Dd]iagonalis`.
  Twenty-five hits, concerning matrix diagonalization and multiplicative
  type tags; no group-scheme rigidity statement.
- LeanSearch: `A connected algebraic group acting by automorphisms on a
  diagonalizable group scheme acts trivially`. Eight hits, concerning
  abstract actions, fixed fields and Galois categories; no exact match.
- `rg` in both lean/WeilConjectures and lean/Sheaf for multiplicative type,
  diagonalizable groups and rigidity. Found the usable existing
  DiagonalizableGroup and ToriMultiplicativeType modules. The latter's
  predicate has an alternative closed-subgroup definition, while the former
  directly gives the explicit Hopf spectrum required here. No theorem
  duplicating this item was found.
- Searched the item id in lean/WeilConjectures: no hit. Searched the proposed
  declaration name in Mathlib, WeilConjectures and Sheaf: no hit.
- Searched DAG nodes for diagonalizable groups, multiplicative type and
  group-scheme automorphisms. Found the landed definition node used above;
  the unstated torus-rigidity lemma is only the torus case and is not an
  existing statement of the present nonreduced multiplicative-type result.
- Checked dag/lean_names_upstream.json for the proposed name and rigidity
  entries; no upstream copy of this statement.

No statement dispute or correction was needed. The only node delta beyond
`lean` is addition of the existing landed definition to `stmt_deps`, as
allowed by brief-stage2 §5. There is no change to the source, proof or
proof dependencies.

Validation: the prescribed scompile.py compiled this file in module mode
both as a sandbox file (34.6 seconds) and at its intended library module
path (5.4 seconds), with no errors or unexpected warnings. No global or
local direct Lean build was run.

## Second reading by Q147

I reread the final file alongside the whole node and Milne pp.243--244.
This is a second pass by the same worker; the dispatcher's instruction
prohibits starting another agent, and the maintainer supplies the independent
review. No independent review is claimed here.

The rereading checked that `Grp` uses the F-base on both groups and the
isomorphism, that `hD` specifies the canonical group law rather than an
arbitrary group structure on Spec F[M], that finite generation is imposed
without excluding torsion, and that the topology hypothesis is only on G.
The action object retains both action laws, and hAut refers to exactly its
map on every algebra-valued point. The existential MulEquiv cannot change
that map because its values are specified for every d. Naturality follows
from this actual scheme morphism. The conclusion is the second projection
in the same cartesian over-category, hence exactly the node's conclusion.
All finite-type, affine, smooth, connected and algebraically closed clauses
are present. The nilpotent and disconnected target cases remain included.
No mismatch was found and no statement correction was made.
