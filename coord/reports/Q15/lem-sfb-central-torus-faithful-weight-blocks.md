## Worker report

The module `Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks` states
`AlgebraicGeometry.CentralTorusWeightBlocks.exists_faithful_weight_blocks` with `sorry`.
Its only other declarations are real-data evaluation helpers `pointAction` and
`characterScalar`; neither requires a postponed verification theorem. No definition
node or dependency repair is needed. The node statement and proof are unchanged.
Three already landed definition nodes are added to stmt_deps: def-sc-general-linear-group,
def-sc-gm-ga, def-sfb-tori-multiplicative-type, for the notions occurring in the statement.

The source was read directly from Milne, Algebraic Groups (2017), printed p.87
(Theorem 4.9 and Corollary 4.10), pp.234--235 (Theorem 12.12 and Remark 12.13),
and p.246 (proof of Proposition 12.46(a)). The last source displays the block
centralizer. The node's coefficient argument supplies its scheme-theoretic version
on arbitrary algebras, and its final coordinate factorization supplies the closed
immersion of the character tuple. Those five proof steps appear in the theorem docstring.

Hypothesis and conclusion correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Group schemes H,T: `H T : Grp (Over (Spec (.of F)))`, using the existing
  `GrpObj` group structures; `iT : T ⟶ H` is a bundled group homomorphism.
- Affine H: `[IsAffine H.X.left]`.
- Finite type over F: `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- Closed subgroup inclusion: `[IsClosedSubgroupScheme iT.hom.hom]`.
- Rank r >= 0 and split torus: `(r : ℕ)` and
  `Nonempty (T ≅ MultiplicativeType.splitTorus F r)` in the category of group schemes.
- Centrality after every scalar extension: `hcentral` quantifies over every
  commutative F-algebra A and all A-points t,h, and asserts
  `Commute (t ≫ iT.hom.hom) h` in the represented group H(A).
- Smoothness and connectedness are only terminology references in the node's opening
  sentence; it does not assume H smooth or connected. No such hypotheses are imposed.
- Finite-dimensional nonzero V: the existential N with `0 < N` and coordinate space
  `ULift.{u} (Fin N) → F`. Every finite-dimensional nonzero F-vector space admits a
  finite basis and is isomorphic to such a space; the existential form loses no case.
  ULift ensures the index has the same universe as the upstream GL construction.
- Closed-immersion homomorphism rho: the bundled group-scheme arrow
  `ρ : H ⟶ Grp.mk (GeneralLinearGroup (ULift.{u} (Fin N)) F)` and
  `IsClosedImmersion ρ.hom.hom.left`. Thus faithfulness is scheme-theoretic.
- Finite direct decomposition with nonzero blocks: `s : ℕ`, the family of submodules
  `V : Fin s → Submodule F (...)`, `DirectSum.IsInternal V`, and `∀ i, V i ≠ ⊥`.
  This is precisely the internal direct sum, not just spanning or independence.
- H-stability after base change: the first universally quantified conclusion states
  membership in `(V i).baseChange A` is preserved by `pointAction ... h`. Since h
  ranges over the group, this includes h inverse and gives an automorphism of the block.
- Characters chi_i: `χ : Fin s → (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`.
- Scalar action on every block over every A: the second universal clause equates
  `pointAction ... (t ≫ iT.hom.hom) v` with `characterScalar (χ i) A t • v`
  for every v in the actual scalar extension `(V i).baseChange A`.
- GL(V)(A) is implemented by the existing `GeneralLinearGroup.homMulEquiv`, followed
  by `Matrix.GeneralLinearGroup.toLin'` for the base-changed standard basis.
  `pointAction` therefore acts on `A ⊗[F] V`, canonically symmetric to `V ⊗[F] A`.
  `Submodule.baseChange` is the image of the actual tensor inclusion, not an arbitrary
  subspace. Over a field that inclusion is injective and represents the stated tensor block.
- `characterScalar` pulls back the Laurent coordinate T 1 along the actual character
  point and applies `Scheme.ΓSpecIso`; it is the underlying scalar of chi_i(t).
- Closed immersion of the tuple: `IsClosedImmersion (Pi.lift (fun i ↦
  (χ i).hom.hom)).left`. This is the canonical map to the finite product of G_m in
  schemes over Spec F; its components are the given group-scheme characters.
  For affine schemes Mathlib's `IsClosedImmersion` is the surjection-of-coordinates notion.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (line 180).
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (line 62), imported through
  the algebraic-closure import of ToriMultiplicativeType. No choice of algebraic closure
  is imposed on F; only algebraic closedness from def-weil-algebraic-closure is used.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and `Grp`;
  Mathlib.CategoryTheory.Monoidal.Mon: `CategoryTheory.IsMonHom` (line 213).
  Bundled Grp morphisms have exactly this homomorphism structure.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (line 98), inherited subgroup and
  homomorphism conditions; no private subgroup predicate is introduced.
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` (line 42), its Hom;
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType` (line 43);
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact` (line 43).
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` (line 62), and
  Mathlib.Topology.Connected.Basic: `ConnectedSpace` (line 705), read as terminology
  dependencies, with no additional hypothesis since the node imposes neither.
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear:
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv` (full signatures read).
  The recorded def-sc-general-linear-group module, Sheaf.AlgebraicGeometry.LinearGroupSchemes,
  uses this same upstream GL; it is publicly imported rather than defining GL again.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes:
  `StandardGroupSchemes.multiplicative` and `multiplicativeGroup` (full signatures read).
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType:
  `MultiplicativeType.splitTorus`, including its rank-zero clause (full definition read).
- Mathlib.LinearAlgebra.TensorProduct.Basis: `Module.Basis.baseChange`;
  Mathlib.LinearAlgebra.TensorProduct.Tower: `Submodule.baseChange` (line 831);
  Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs:
  `Matrix.GeneralLinearGroup.toLin'` (line 108).
- Mathlib.Algebra.DirectSum.Module: `DirectSum.IsInternal` and its internal-sum API.
  The proof imports include the landed HopfCoactionLinearization,
  GmRepresentationWeightBasis and the module/tensor/free-module prerequisites.
  lem-sfb-comodule-finite-subrepresentation has no Lean record at reading time,
  so no nonexistent module is imported for that proof dependency.

Edge cases checked before writing and on rereading:

- r = 0: splitTorus is the trivial group and the single block V, with trivial character,
  satisfies the assertion. The character tuple is the closed identity-point inclusion.
- Trivial H also admits a positive-dimensional trivial representation; no nontrivial-H
  hypothesis occurs. H empty is impossible for a group scheme over a field because
  the identity section exists.
- N = 0 is explicitly excluded as the node requires V nonzero. s = 0 is not separately
  excluded: internality would force V = 0, contrary to N > 0, so s >= 1 follows.
- A = 0: scalar extensions vanish and both action clauses remain correct.
- Nonreduced H and A, e.g. infinitesimal group schemes in positive characteristic:
  there is no smoothness, reducedness, connectedness or characteristic-zero restriction;
  all points, not only F-points, occur in both action clauses.
- Repeated characters are allowed, as the node does not require distinct chi_i.
- Fixed universe u for F, schemes, their coordinate algebras and test algebras is the
  existing group-scheme API convention. It contains the universal coordinate points,
  so these assertions detect the scheme-theoretic conditions and are not vacuous.

Searches actually run:

- msearch.py leanfinder, query `affine group scheme faithful finite dimensional representation
  central split torus stable weight decomposition`: 8 hits, Lie-module weight spaces and
  weights; none states this affine group-scheme theorem.
- msearch.py leansearch, query `affine group scheme has faithful finite dimensional
  representation central torus weight decomposition`: 8 hits, affine schemes,
  Lie-module weights, abstract representation/Tannaka declarations; no exact theorem.
- msearch.py loogle, query `"GroupScheme", "representation"`: 0 hits.
- msearch.py grep, query `central.*[Ww]eight|faithful.*[Rr]epresentation`, subdirectory
  AlgebraicGeometry: 0 hits.
- Direct rg in WeilConjectures and Sheaf for the item id and central/faithful weight-block
  names: no existing theorem. The narrower GeneralLinear files expose the GL scheme
  and its natural point equivalence; these are reused. Broader torus searches locate
  ToriMultiplicativeType, StandardGroupSchemes, TorusCharacterTangentWeights and
  RationalRepresentationComoduleDictionary. The tangent-weight API concerns a different
  vector space; the comodule dictionary is not the faithful-block existence theorem.
- Direct grep -rn of the item id in lean/WeilConjectures: no hits. Direct rg of
  dag/lean_names_upstream.json and both project libraries for the new names: no collisions.

Validation: scompile.py compiled both sandbox and library modes cleanly; only the theorem
proof is postponed. No STATEMENT-DISPUTED flag, correction or node fault is needed.

## Second reading by Q15

Self-rereading in this dispatcher worker, as the brief prohibits starting other agents;
the maintainer supplies the independent review. I reopened the node and module and
matched the hypotheses and conclusions above. In particular, H is not assumed smooth
or connected; iT is a closed subgroup morphism; splitting is a group-scheme isomorphism;
centrality and both action conclusions range over all commutative F-algebras; the
subspaces are an internal direct sum with every block nonzero; and the final morphism
is the canonical tuple of the same chi_i, asserted to be a closed immersion.
The evaluation helpers contain actual data only. The standard-basis identification
chooses a model for the existential V and imposes no additional representation condition.
I checked that the stability condition includes the inverse action, that rank zero and
zero test algebras are retained, and that no pairwise-distinct-weight condition was added.
The rereading promoted the GL definition-module import to public and added direct public
G_m and split-torus definition imports and their already landed DAG statement dependencies.
No mathematical statement changed.
