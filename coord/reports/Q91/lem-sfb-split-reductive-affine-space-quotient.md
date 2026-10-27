## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitReductiveAffineSpaceQuotient`
states `AlgebraicGeometry.exists_split_reductive_affine_space_quotient` with its
whole proof `sorry`. No definitions, new nodes, dependency repairs, or statement
changes are needed. The node is unchanged outside `lean`.

Source read: Brion, *On Linearization of Line Bundles* (2015), Remark 2.2(v),
printed p.117, and the proof of Lemma 2.3, printed p.118, in
https://www.ms.u-tokyo.ac.jp/journal/pdf/jms220104.pdf (the PDF is absent from the
local literature directory). The latter passage identifies the variety of the
unipotent radical with affine space and trivializes its torsor over H. Remark
2.2(v) supplies the algebraically closed specialization. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was also read; this
item is a supporting node, not that unit's own statement. The theorem docstring
carries all seven steps of the accepted DAG proof, including the geometric
connectedness argument inserted by its stage-1 reviewer.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is an algebraically closed field | `{k : Type u} [Field k] [IsAlgClosed k]` |
| G is a k-group scheme | `G : Grp (Over (Spec (.of k)))` |
| G is smooth | `[Smooth G.X.hom]` |
| G is connected, including nonemptiness | `[ConnectedSpace G.X.left]` |
| G is affine | `[IsAffine G.X.left]` |
| G is of finite type | `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` |
| There exist H and a k-group homomorphism q | `∃ (H : Grp (Over (Spec (.of k)))) (q : G ⟶ H)` |
| There exists an integer n at least zero | `(n : ℕ)` |
| a is an isomorphism of k-schemes G ≅ H ×_k A^n_k | `a : G.X ≅ H.X ⨯ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))).asOver (Spec (.of k))` |
| H is reductive with the node's geometric meaning | `ReductiveTorusCentralizer.IsReductive H` |
| H has a split maximal torus | `∃ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ H) (r : ℕ), ReductiveTorusCentralizer.IsMaximalTorus i ∧ Nonempty (T ≅ MultiplicativeType.splitTorus k r)` |
| First projection of a is q | `a.hom ≫ prod.fst = q.hom.hom` |
| Every field extension L/k, without algebraicity or separability restrictions | `∀ (L : Type u) [Field L] [Algebra k L]` |
| H_L is smooth and affine | `Smooth ((MultiplicativeType.baseChange (K := L)).obj H).X.hom` and `IsAffine ...X.left` |
| H_L is geometrically integral | `GeometricallyIntegral ((MultiplicativeType.baseChange (K := L)).obj H).X.hom` |
| H_L is of finite type | `LocallyOfFiniteType ...X.hom ∧ QuasiCompact ...X.hom` |
| a_L is an L-scheme isomorphism G_L ≅ H_L ×_L A^n_L | `∃ aL : ((MultiplicativeType.baseChange (K := L)).obj G).X ≅ ((MultiplicativeType.baseChange (K := L)).obj H).X ⨯ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of L))).asOver (Spec (.of L))` |
| a_L is over H_L with projection q_L | `aL.hom ≫ prod.fst = ((MultiplicativeType.baseChange (K := L)).map q).hom.hom` |
| a_L is the scalar extension of this very a | The final equation says its affine coordinate, followed by `AffineSpace.map` along `Spec.map (algebraMap k L)`, equals the original affine coordinate after the canonical `pullback.fst` from G_L. Together with the first-projection equations and the product universal property, this is exactly scalar extension of a. |
| G = 1, H = 1, n = 0 included | No positivity hypothesis on n or torus rank r; neither G nor H is required nontrivial. |

Here `⨯` is taken in `Over (Spec (.of k))`, so a is an isomorphism of
schemes over k, not a group isomorphism. The categorical product is the chosen
fibre product: Mathlib's `CategoryTheory.Over.prodLeftIsoPullback` and its two
projection equations, in `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`,
identify it with `pullback H.X.hom (AffineSpace ... ↘ Spec (.of k))`. Thus it
uses exactly the objects requested in the node. `ULift.{u} (Fin n)` is the
finite coordinate set in the scheme universe, including the empty coordinate
set for n = 0. The final equation does not add an arbitrary choice of a
trivialization after extension: its two coordinates characterize the base
change of a uniquely, using `AffineSpace.isPullback_map` for the second factor.

`GeometricallyIntegral` is read from
`Mathlib.AlgebraicGeometry.Geometrically.Integral`: it requires integral
pullbacks to every field. `IsIntegral` includes reducedness and irreducibility;
irreducibility includes nonemptiness. It is exactly the explicit definition in
the node, with no hypothesis that L is algebraically closed.

Dependency declarations read and reused (directly or through public imports):

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp` and their
  homomorphisms in `Mathlib.CategoryTheory.Monoidal.Grp`; the convention is
  documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, respectively in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`.
- `def-sfb-reductive-torus-centralizer-terminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`,
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`.
- `def-sfb-tori-multiplicative-type`:
  `AlgebraicGeometry.MultiplicativeType.baseChange`, `splitTorus`, `IsTorus`,
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`. All scalar extension is this
  recorded functor, including the map on q.
- `def-sfb-solvable-group-structure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsAlgebraic` and `IsUnipotent`,
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`; used inside reductivity.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme` and
  `IsNormalSubgroupScheme`, `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`;
  used inside the maximal-torus and reductivity predicates.
- `def-pc-field-extension`: `Algebra` and `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.fst`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, together with
  the Over-product construction above.
- `def-weil-algebraic-closure`: `IsAlgClosed`, `IsAlgClosure` and
  `AlgebraicClosure`, `Mathlib.FieldTheory.IsAlgClosed.Basic` and
  `...AlgebraicClosure`; the last occurs inside the recorded reductivity predicate.
- `def-sbc-affine-space`: `AlgebraicGeometry.AffineSpace` and its `over`
  instance, `Mathlib.AlgebraicGeometry.AffineSpace`. Its `map` and
  `isPullback_map` are the canonical coordinate-preserving base change.

The available proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`
(`affine_normal_quotient_geometry`),
`Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`
(`reductive_borel_pair_structure`),
`Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`
(`IsSplitSolvable`, `RepresentedRightTorsor`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`
(`GeometricallyConnected.of_connectedSpace_of_section`), and
`Mathlib.AlgebraicGeometry.Morphisms.Proper` (the recorded proper-base-change
node; its smooth clause is already publicly available). The other five proof
nodes have no recorded Lean declarations, so there is no module of theirs to
import. No missing statement dependency was found.

Edge cases checked mathematically before finalizing the signature:

- The trivial group has H trivial, n = 0 and torus rank 0. Affine zero-space
  is canonically the base scheme, so both product and extension equations apply.
- For a reductive G, choose H = G, q the identity and n = 0. No requirement that
  q have positive-dimensional fibres occurs in the Lean statement.
- For connected smooth unipotent G, H can be trivial, with n the affine-space
  dimension; maximal torus rank zero is admitted.
- Characteristic zero and positive characteristic are both allowed. There is
  no Levi-subgroup or group-product conclusion, which would be an unjustified
  strengthening in positive characteristic.
- L = k and arbitrary transcendental extensions are admitted. The field,
  schemes and scalar-extension functor use the same arbitrary ambient universe
  u, as their recorded interfaces do; no independent smaller test universe is
  quantified over. No finite-dimensionality assumption on L occurs.
- Empty schemes cannot be group schemes over a field; connectedness also
  includes nonemptiness. Geometric integrality does not accidentally treat the
  empty scheme as integral.

Searches actually run using `msearch.py Q91
lem-sfb-split-reductive-affine-space-quotient`:

- LeanFinder: `A smooth connected affine algebraic group over an algebraically
  closed field is isomorphic as a variety to the product of a reductive group
  and affine space`. Eight hits, including `AffineSpace.instIsAffine`,
  `AffineSpace.isoOfIsAffine`, semisimple-ring, Lie-module and Galois-category
  facts. No matching algebraic-group quotient theorem.
- Loogle: `AlgebraicGeometry.AffineSpace, AlgebraicGeometry.Reductive`.
  Zero hits; it reports unknown identifier `AlgebraicGeometry.Reductive`.
- Mathlib grep, subdirectory `AlgebraicGeometry`:
  `split_reductive|affine_space_quotient|IsReductive`. Zero hits.
- LeanSearch: `A connected affine algebraic group over an algebraically closed
  field is a product of affine space and a reductive group`. Eight hits:
  `AffineSpace`, continuous affine equivalences, connected topological products,
  geometrically reduced algebras and affine/coproduct facts. No matching theorem.
- Local `rg -n 'split_reductive|affine_space_quotient|IsReductive'` of both
  `lean/WeilConjectures` and `lean/Sheaf`: the existing reductivity definition,
  Borel-pair theorem and other reductive structure theorems, no instance of this
  affine-space quotient statement. `grep -rn` for the full item id in
  `lean/WeilConjectures` found no declaration. The searches are logged in
  sandbox `searches.jsonl`.

Verification: the final file was checked with the required `scompile.py`, in
module mode and with `autoImplicit false`; exit code zero, no errors or warnings.
All binders and the universe are explicit. The single postponed theorem is
exactly the theorem matching this node. No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q91

This is the solo worker's separate rereading; the dispatcher brief prohibits
starting other agents, and the maintainer supplies the independent review.
I reopened the node and the final signature and checked the table above against
both. In particular, `Grp (Over ...)` supplies exactly the group-scheme datum;
a and aL live in Over, so both are scheme isomorphisms over the stated field,
while only q is required to respect group laws. The split torus is the dependency's
actual `splitTorus`, with a group-scheme isomorphism and a maximal inclusion.
The first projections give exactly q and its scalar extension. The final
affine-coordinate equation pins aL to the base change of the original a;
otherwise existence of an unrelated aL would not explicitly render the node's
scalar-extension clause. The structural conjunction includes smoothness,
affineness, geometric integrality and both components of finite type.
No assumptions on L beyond a field extension, and no positivity restrictions,
were introduced. No mismatch or correction was found in this reading.
