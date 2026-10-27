## Worker report

The module `Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension` states
`AlgebraicGeometry.commutative_multiplicativeType_extension`. Its only theorem proof
is `sorry`; there is no definition and nothing is proved. The mathematical statement
is unchanged. The existing, landed definition node `def-sfb-diagonalizable-group` is
added to `stmt_deps`, as permitted by brief-stage2 §5, to record the construction used
in the node's own definition of multiplicative type. There are no new nodes or
repaired dependency modules, and no disputed statement or statement correction.

Clause-by-clause correspondence:

- The algebraically closed field F is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group schemes E and Q are `E Q : Over (Spec (.of F))`, with `[GrpObj E]`
  and `[GrpObj Q]`. These use the recorded group-scheme interface rather than a
  private group-scheme structure.
- Affineness of E and Q is `[IsAffine E.left] [IsAffine Q.left]`.
- Finite type of E and Q is the pair `[LocallyOfFiniteType ...hom]` and
  `[QuasiCompact ...hom]` for each structure morphism, exactly as recorded by
  `def-weil-finite-type-morphism`.
- The homomorphism q is `(q : E ⟶ Q) [IsMonHom q]`; being in the over category
  includes compatibility with the structure maps to Spec F.
- The coordinate-ring map q* is `q.left.appTop.hom`, and the stipulated exactness
  and detection of zero modules is its `.FaithfullyFlat` property, hypothesis `hq`.
  This is faithful flatness of the coordinate-ring map, not injectivity alone or
  surjectivity on F-valued points.
- N is not an independent variable: it is `GrpObj.ker q`, the actual pullback of q
  along the identity section, with its canonical kernel group structure. Thus the
  kernel identification is imposed by the term itself, without an extra hypothesis.
- Multiplicative type of N is `hN`: there exist `M : Type u`, an `AddCommGroup M`
  and `AddGroup.FG M`, with `Nonempty (Grp.mk (GrpObj.ker q) ≅ diagonalizableGroup F M)`.
- Multiplicative type of Q is `hQ`, the same existential presentation with `Grp.mk Q`.
  The isomorphisms are in `Grp (Over (Spec (.of F)))`, not merely isomorphisms of
  underlying schemes or groups of rational points.
- The supplied `diagonalizableGroup` is the actual Hopf spectrum of
  `AddMonoidAlgebra F M`, with basis product e_m e_n = e_(m+n), coproduct
  e_m ↦ e_m ⊗ e_m, counit e_m ↦ 1 and antipode e_m ↦ e_(-m).
- Affineness and finite type of N are retained by hN: a finitely generated abelian
  group gives a finitely generated group algebra, and its spectrum is affine. Thus
  no additional kernel affineness or finite-type assumption is needed to encode
  the opening convention that all three groups are affine of finite type.
- Commutativity of E is `[IsCommMonObj E]`, the symmetry invariance of multiplication.
- The conclusion is precisely the same finitely generated diagonalizable presentation
  for `Grp.mk E`. No smoothness, reducedness or connectedness is assumed anywhere.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, for the algebraically closed
  clause of def-weil-algebraic-closure (whose Mathlib match explicitly includes it).
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, Mathlib.CategoryTheory.Monoidal.Grp;
  `CategoryTheory.IsMonHom`, `CategoryTheory.IsCommMonObj`,
  Mathlib.CategoryTheory.Monoidal.Mon; and `CategoryTheory.GrpObj.ker` with its
  canonical group structure,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. The recorded
  documentation and interface are imported through
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, as specified by
  def-sc-group-scheme. The kernel declaration is a pullback, so retains nilpotents.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact,
  for def-weil-finite-type-morphism.
- `AlgebraicGeometry.diagonalizableGroup`, Sheaf.AlgebraicGeometry.DiagonalizableGroup,
  the recorded declaration of def-sfb-diagonalizable-group.
- `AddGroup.FG`, Mathlib.GroupTheory.Finiteness, for finite generation of the abelian group.
- `RingHom.FaithfullyFlat`, Mathlib.RingTheory.RingHom.FaithfullyFlat, using the algebra
  induced by the ring map and `Module.FaithfullyFlat`. This is the usual flat and
  faithful tensor functor condition.

The recorded proof dependency def-sc-gm-ga is imported privately through
Sheaf.AlgebraicGeometry.StandardGroupSchemes. The other two proof dependencies,
lem-sfb-multiplicative-additive-vanishing-criterion and
lem-sfb-faithfully-flat-group-quotient-universal, currently have neither a Lean
record nor a Mathlib match, so there is no module to import for them. They are
proof inputs only, not missing notions in this statement. The theorem docstring
reproduces all three proof steps and names both inputs explicitly.

Source grounding: read Milne's PDF, Corollary 12.22, printed p.239 and the neighboring
Theorem 12.18. The proof uses vanishing of Hom(N,G_a) and Hom(Q,G_a), descent along
q to obtain vanishing of Hom(E,G_a), and then the commutative criterion for E.
The node supplies the faithfully flat quotient explicitly. The current blueprint
ancestor proof was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; this item is a
supporting algebraic-group lemma, not the unit statement.

Edge cases checked before writing: the trivial group is D(0), allowed because no
nonzero, nonempty-generator or positive-rank condition is imposed on M. The identity
quotient has trivial kernel and reproduces the presentation of Q. The quotient E → 1
has kernel E and the claimed conclusion is already its hN presentation. In positive
characteristic, M = Z/p gives the nonreduced group mu_p; no smoothness or reducedness
binder rules it out. Finite groups and disconnected groups remain allowed; FG does
not require M to be torsion-free. The kernel is computed as a scheme, so replacing
mu_p by its rational points never occurs. Alpha_p does not satisfy a diagonalizable
presentation and is not inadvertently covered by hN. Commutativity is substantive:
a general affine group can have no additive characters while being noncommutative.
All universes and variables are explicit, with autoImplicit disabled. The common
universe u is the scheme/coordinate-ring universe of the existing Hopf-spectrum
interface; any finitely generated abelian group can be represented in Type u.

Searches made using the prescribed msearch.py:

- leanfinder: "A commutative extension of diagonalizable affine group schemes of finite
  type over an algebraically closed field is diagonalizable": eight hits about
  diagonal scheme-morphism properties; none is this group-scheme extension theorem.
- leansearch: "An exact sequence of affine group schemes with diagonalizable kernel
  and quotient has diagonalizable middle group if it is commutative": eight hits
  about ordinary additive group extensions, exact complexes and the five lemma;
  no group-scheme extension theorem.
- loogle: "GrpObj, IsCommMonObj": no hits, with unknown identifier GrpObj reported.
- grep on Mathlib/AlgebraicGeometry: "diagonaliz|diagonalis|multiplicative.?type": no hits.
- rg on lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry for
  multiplicativeType, IsMultiplicativeType and diagonalizable terminology found the
  canonical D_F(M) construction and geometric multiplicative-type terminology, but
  not this theorem. The exact node-id search in lean/WeilConjectures found no match.
  The proposed theorem name was checked across Mathlib and both project roots and
  found absent. DAG search for D(M), D_F and multiplicative type found the existing
  def-sfb-diagonalizable-group, which is reused.

The geometric predicate MultiplicativeType.IsMultiplicativeType describes a closed
subgroup of a split torus after base change to AlgebraicClosure F. The present node
instead explicitly specifies an isomorphism over F to D_F(M). Its literal presentation
is written directly in the hypotheses and conclusion using the existing D_F(M);
no second predicate or construction is defined.

Validation: scompile.py compiled this single delivered module on the server, against
the live published library, in both sandbox and library modes, with no errors or
warnings (7.0 s and 2.1 s). No local or global build was run.

## Second reading by Q45

This is the dispatch worker's own second pass, not a claim of a separate agent review;
the brief forbids starting other agents, and the maintainer supplies independent review.
I reread the node and completed file together. The field and algebraic-closure binders,
affine and finite-type hypotheses, actual coordinate map, canonical pullback kernel,
finitely generated abelian character groups, group-scheme isomorphisms, commutativity
and conclusion each match the clauses listed above. There is no hypothesis on
smoothness or connectedness, no substitution of F-points for schemes, and no new
notion hidden in a private or hollow definition. The additional existing statement
dependency records the D_F(M) construction actually used. No mismatch requiring a
mathematical statement change was found; no second-reading code repair was needed.
