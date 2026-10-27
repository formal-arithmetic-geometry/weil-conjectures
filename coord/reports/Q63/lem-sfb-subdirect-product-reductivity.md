## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.SubdirectProductReductivity states
AlgebraicGeometry.isReductive_of_smooth_connected_subdirect_product, with sorry as
its entire proof. No definitions, helper theorems, new nodes, dependency repairs,
or changes to the informal statement are needed. The item changes only in lean.

Hypothesis and conclusion correspondence:

- F is an algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- G₁, G₀ and H are F-group schemes: `(G₁ G₀ H : Grp (Over (Spec (.of F))))`.
  Bundling supplies the actual group structures and group homomorphisms, using
  the recorded CategoryTheory.Grp and GrpObj of def-sc-group-scheme.
- G₁ and G₀ are reductive: `hG₁` and `hG₀` use
  `ReductiveTorusCentralizer.IsReductive`. This already includes affineness,
  finite type and smoothness of each factor. The predicate is the one used by
  lem-sfb-reductive-borel-pair-structure, not a new definition.
- H is affine of finite type: `[IsAffine H.X.left]`,
  `[LocallyOfFiniteType H.X.hom]` and `[QuasiCompact H.X.hom]`.
- H is smooth and connected: `[Smooth H.X.hom]` and
  `[ConnectedSpace H.X.left]`. The latter includes nonemptiness as required by
  def-weil-connected-scheme.
- The closed subgroup inclusion into the fibre product over F is
  `(i : H ⟶ G₁ ⊗ G₀)` with `IsClosedSubgroupScheme i.hom.hom`.
  Here the monoidal product in Grp(Over(Spec F)) is the group-scheme product.
  The explicit @ application supplies H.grp and (G₁ ⊗ G₀).grp, retaining the
  product's bundled group structure without relying on a competing inferred one.
- Surjectivity of each coordinate projection on underlying spaces is exactly
  `Surjective (i ≫ fst G₁ G₀).hom.hom.left` and the corresponding `snd` condition.
  Mathlib's AlgebraicGeometry.Surjective is Function.Surjective on the scheme's
  underlying continuous map, not surjectivity on every algebra-valued point.
- Conclusion: `ReductiveTorusCentralizer.IsReductive H`.
- No finiteness, separability, centrality or smoothness of either kernel is assumed.
  The node's tori/root conventions are contextual: no torus, root or positive
  system occurs in its hypotheses or conclusion, so none is added to the signature.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field (def-weil-field).
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed, via the algebraic-closure
  Mathlib match of def-weil-algebraic-closure.
- Mathlib.CategoryTheory.Monoidal.Grp: Grp, GrpObj and bundled homomorphisms,
  over Spec F (def-sc-group-scheme).
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  IsSubgroupScheme, IsClosedSubgroupScheme and IsNormalSubgroupScheme
  (def-sc-group-scheme-subgroup). Closedness includes algebra-point injectivity.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth
  (def-sbc-smooth-morphisms).
- Mathlib.Topology.Connected.Basic: ConnectedSpace (def-weil-connected-scheme).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  LocallyOfFiniteType and QuasiCompact (def-weil-finite-type-morphism).
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  reductive_borel_pair_structure and semisimpleGroupScheme_isReductive, including
  the full signature/docstrings, and its public predicate in
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  ReductiveTorusCentralizer.IsReductive. Also read
  Sheaf.AlgebraicGeometry.SolvableGroupStructure: IsAlgebraic and IsUnipotent.
  The latter includes smoothness, a faithful closed representation and nilpotence
  of every geometric matrix point. IsReductive tests after AlgebraicClosure F;
  over algebraically closed F this is equivalent to the stated convention,
  since that algebraic closure is isomorphic to F as an F-algebra. Its unipotent
  test groups are smooth by IsUnipotent itself.

The single public import provides these statement dependencies. Plain proof
imports are WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
(Smooth.geometricallyReduced),
Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
(affineGroupHom_exists_faithfullyFlat_closedImmersion), and
Mathlib.RingTheory.Spectrum.Prime.Topology (PrimeSpectrum.zeroLocus_eq_iff).
The other already-stated proof notions (IsReduced, IsClosedImmersion,
IsClosedSubgroupScheme, Spec) are also available through the public dependency.
lem-sfb-unipotent-normal-quotient-image has no recorded Lean declaration in the
read clone, so has no module to import; it is only a proof dependency, not an
object needed to state this item. Its exact role remains in the proof docstring.

Source and proof: opened Milne iAG2017 at Assertion 23.20, printed p.491,
including 23.19. The proof maps a normal unipotent subgroup into both reductive
factors and concludes that it is trivial. The five DAG steps are reproduced in
the theorem docstring: smooth implies reduced; topological surjectivity plus
flat-image factorization forces faithful flatness; normal unipotent images;
triviality on all R-points; then the universal coordinate-ring point proves
scheme-theoretic triviality. No radical-existence theorem is assumed.

Edge cases checked before writing:

- Both factors trivial, one factor trivial, H the product, and H the diagonal.
- A graph of Frobenius in positive characteristic: a projection may have an
  infinitesimal, nonsmooth kernel. Neither projection is required to be smooth
  or pointwise surjective on every F-algebra, so this is included.
- A product with a positive-dimensional reductive projection kernel is allowed.
- A Borel subgroup of SL₂ embedded as a graph with nonsurjective projection is
  excluded by the surjectivity assumption; it does not contradict the result.
- Empty schemes are excluded by the group unit and by ConnectedSpace, not by
  an added hypothesis. There is no characteristic or rank restriction.
- The universe u is explicit and autoImplicit is false. All schemes, fields and
  test algebras in the reused predicates have the established size convention.

Searches (2026-10-24; prescribed msearch.py, group Q63, item id):

- leanfinder: "A smooth connected closed subgroup of a product of two reductive
  algebraic groups surjective onto each factor is reductive" returned eight
  hits, including solvable_prod, Prod.instLieGroup, Geck-construction Lie-algebra
  semisimplicity and connectedComponentOfOne. None is a group-scheme statement.
- loogle: `"IsReductive"` returned zero hits.
- grep: `subdirect|unipotent.*radical|IsReductive` in Mathlib/AlgebraicGeometry
  returned zero hits.
- leansearch: "A smooth connected subdirect product of reductive algebraic
  groups is reductive" returned eight hits on abstract groups, smooth algebras
  and analytic Lie groups. No match.
- rg in lean/WeilConjectures for the item id, subdirect and IsReductive returned
  no matching theorem. rg in lean/Sheaf found the existing reductivity predicate
  and the compatible-rank-one-graph proof's informal use of this item, but no
  statement of the subdirect-product result. Checked the proposed full name
  in both roots and Mathlib: no duplicate.

Validation: scompile.py checked both its sandbox probe and the actual library
module successfully; no errors or unexpected warnings.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q63

A separate second pass through the node, the full dependency predicate bodies
and the completed signature found no hypothesis or clause mismatch. This is a
worker self-check; the maintainer supplies the independent delivery review.
In particular, the first and second projections use G₁ and G₀ in that order,
closedness is scheme-theoretic, and Surjective refers only to underlying spaces.
Smoothness is imposed on H, not on its projection kernels. The geometric
reductivity predicate is equivalent over this algebraically closed base, and
smoothness of its unipotent test groups is built into IsUnipotent. Affine finite
type conditions on the two factors are in hG₁ and hG₀; the same conditions on H
are explicit. No torus data or kernel restrictions have slipped into the statement.
No changes were needed after this pass.
