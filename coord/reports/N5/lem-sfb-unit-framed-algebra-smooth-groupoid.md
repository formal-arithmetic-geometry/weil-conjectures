## Worker report

The module `Sheaf.AlgebraicGeometry.UnitFramedAlgebraGroupoid` states
`AlgebraicGeometry.UnitFramedAlgebra.smooth_groupoid`. Its conclusion is
`Nonempty (Presentation S n)`, an explicit record of the coordinate bijections,
scheme maps, pointwise formulas, group/groupoid laws and smoothness asserted by
this node. All helper constructions belong to this node's own coordinate
construction. Every definition has real data. The only postponed proof is the
named theorem `smooth_groupoid`, whose docstring gives all nine DAG proof steps.
No new nodes, dependency replacements, or statement correction were needed.

Source read: `literature/stacks-project/criteria.tex`, lines 2115–2264, section
`section-hilbert-point`, equations `equation-objects` and `equation-FAd`, and
`lemma-represent-FAd` (Tag 05YP), including the following smoothness paragraph.
The source starts over Spec Z and explicitly gives arbitrary bases by base
change. The node spells out the coherent composition order; the source's printed
composition formula in the enumerated lemma has the opposite order to its
conjugation formula. The Lean follows the node: first g, then h, has label gh.

Hypotheses and clauses, matched individually:

- Any base scheme: the only base binder is `S : Scheme.{u}`. No affineness,
  Noetherian, characteristic, reducedness, or nonemptiness assumption is imposed.
- Size convention: `u` and `v` are explicit universes; schemes, coordinate rings
  and global sections have universe u. The auxiliary law/frame definitions work
  over a ring in arbitrary universe v. Integer coefficient rings are `ULift.{u} Z`;
  no independent smaller universe is used for test schemes or test rings.
- Positive degree d: write d = n + 1 for `n : Nat`. This parametrizes precisely
  all positive degrees; the distinguished index is `0 : Fin (n+1)`, i.e. e_1.
- R_T is exactly `Γ(T.left, top)` for arbitrary `T : Over S`, without requiring
  T affine. The finite free module is `Fin (n+1) → R_T`.
- `Law.mul` is a curried R_T-linear map in both variables. `Law.assoc`,
  `Law.comm`, `Law.unit_left` and `Law.unit_right` are exactly the associativity,
  commutativity and specified-unit conditions. `basisVector` uses `Pi.single`.
- `Frame` is the subtype of actual linear equivalences fixing e_1; hence it
  parametrizes exactly invertible linear maps with that property.
- The polynomial ring B_d is `LawRing`. `lawIdeal` is `Ideal.span` of the union
  of the three displayed families, with all indices ranging over `Fin (n+1)`.
  The associativity generator has precisely the order
  sum_l a_ij^l a_lk^q - sum_l a_il^q a_jk^l. The other two generators are
  a_ij^k - a_ji^k and a_i0^j - delta_ij. `LawRing` is the actual ideal quotient;
  `lawCoordinate` applies `Ideal.Quotient.mk` to each polynomial variable.
- X is `objects S n = model S (LawRing n)`. `model` is the scheme pullback of S
  and Spec of the displayed ring over `Spec (ULift Z)`, with first projection
  as its structure morphism. The arrows to Spec Z are its unique terminal arrows,
  supplied by Mathlib's `specULiftZIsTerminal`.
- The matrix b is `universalFrame`. `frameMatrix` supplies first column e_1
  using `Fin.cases`; its remaining columns are exactly the independent variables
  indexed by `Fin (n+1) × Fin n`. These are d(d-1) coordinates.
- `FrameRing` is literally `Localization.Away (universalFrame n).det`, and
  `frames S n` is its spectrum base-changed to S, namely the node's G.
- The ambient affine space is Mathlib `AffineSpace` on
  `ULift (Fin (n+1) × Fin n)`. `ambientDet` is the determinant of its coordinate
  matrix. `ambientMap`, `ambient_coeff`, `ambient_open`, and `ambient_range`
  specify the canonical coefficient map G → A, its being an open immersion,
  and its image being exactly the determinant basic open. This specifies the
  asserted open subscheme, rather than just an unspecified isomorphic open.
- `frameEquiv T` identifies G(T) with invertible linear maps fixing e_1.
  `frame_coeff` says its matrix entries are the localized coordinate values.
  `groupMul`, `groupOne`, `groupInv` are morphisms over S, and their three
  formula fields specify ordinary matrix multiplication, identity and inverse.
  The five `group_*` law fields explicitly assert associativity, both identity
  laws and both inverse laws on every T. Morphisms supply naturality.
- The arrow scheme is `prod (frames S n) (objects S n)` in `Over S`, i.e.
  the scheme fibre product G ×_S X. Its source is exactly `prod.snd`.
  `target` is a scheme morphism over S, and `action_formula` specifies
  m'(x,y) = g.symm (m (g x) (g y)). Thus the label g is the algebra
  isomorphism from m' to m in the usual direction, exactly as in the node.
- `identity`, `inverse`, `composition` are scheme morphisms over S.
  `identity_frame` specifies label 1 and `inverse_frame` label g inverse.
  The source/target components come from the recorded `IsPresheafGroupoid`
  laws, so identity is (1,m) and inverse is (g inverse,a(g,m)).
- `composition` has domain the pullback of source against target, with first
  point the later arrow (h,m') and second point the earlier arrow (g,m).
  `composition_frame` gives g applied after h, hence the matrix gh. The
  groupoid source law makes its object component m; its target law gives
  a(h,m'). The pullback condition is precisely m'=a(g,m).
- `groupoid` uses the dependency's exact `AlgebraicSpace.IsPresheafGroupoid`,
  on the Yoneda images of these scheme maps. Its composition is transported
  through `PreservesPullback.iso yoneda ...`, the canonical Yoneda pullback
  comparison. Thus no arbitrary presheaf or comparison replaces the scheme
  groupoid. The field includes every identity, inverse and associativity law.
- Both smoothness clauses are explicit: `source_smooth` and `target_smooth`
  use Mathlib `Smooth` on the underlying scheme maps. No smoothness of X/S
  is assumed.
- The coefficient rule identifying objects is `objectEquiv` together with
  `object_coeff`: multiplication on e_i,e_j has kth coordinate equal to the
  pulled-back residue class a_ij^k. A finite free vector equals the sum of
  its coordinates times standard vectors, giving the node's displayed rule.
- Arrows are exactly frames and a source law, with target determined by
  `action_formula`. The frame bijection and the object bijection therefore
  identify the whole groupoid of T-points with FA_d(T); identity, inverse
  and composition are preserved by the three frame formula fields and the
  groupoid source/target equations. This is an isomorphism of groupoids,
  not only an equivalence on isomorphism classes or an object bijection.
- Pullback applies coefficients along `f.left.appTop`. This is asserted for
  every `f : T' → T` by `object_natural` and `frame_natural`; it is the
  base-change rule for laws and linear maps, and makes the groupoid
  identification natural for every base morphism.
- Rank one: n=0 gives no variables `Fin 1 × Fin 0`, and `frameMatrix` is
  (1). `rank_one_det` explicitly says its determinant is 1; `rank_one_frames`
  says the structure map G → S is an isomorphism, the meaning of G=S here.

Dependency declarations read and used (full definitions/docstrings, not only names):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme` and `Scheme.Hom`.
- `def-weil-size-convention`: its recorded metatheoretic convention, rendered
  by the explicit universes above; it intentionally has no declaration.
- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free`; the actual standard free module and basis use Mathlib's Pi
  module/linear maps and `Pi.single`, not a replacement freeness predicate.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `algHom_ext`; `MvPolynomial.aeval` from Eval is the
  polynomial evaluation used in the proof plan.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `Spec`,
  `Spec.map` and `Scheme.ΓSpecIso` for evaluating functions on spectrum points.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`. The products in
  Over S are Mathlib's scheme fibre products (`Limits.Constructions.Over.Products`).
- `def-sfb-algebraic-space-groupoid`: the imported
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`,
  `AlgebraicGeometry.AlgebraicSpace.IsPresheafGroupoid`, with exactly its
  source-first pullback convention and c(a,b)=a after b.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, exactly the recorded predicate.
- `def-weil-pbc-matrix-determinant`: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
  `Matrix.det`, whose Leibniz formula is `Matrix.det_apply`.
- `def-sbc-affine-space` (Mathlib match): `Mathlib.AlgebraicGeometry.AffineSpace`,
  `AffineSpace`, `over`, and `coord`. The coordinate type is explicitly ULift
  to the scheme universe, as its recorded match requires.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away`,
  `Localization.Away`, with the commutative ring construction/algebraMap from
  `Mathlib.RingTheory.Localization.Away.Basic`.

The stated proof dependencies are imported, publicly where their notions occur
in the statement and otherwise as proof imports: free modules, multivariate
polynomials, GammaSpecAdjunction, scheme pullbacks, Localization.Away.Basic,
Matrix.Adjugate (including the Cramer identities), AffineSpace, the basic-open
and open-immersion API, Yoneda, AlgebraicSpaceGroupoid, the upstream smooth
AffineSpace theorem in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
Smooth, and Proper (the recorded proper/smooth base-change lemma's module).

Edge cases checked before writing: n=0/d=1 as above; the empty scheme S and
empty test scheme T (global sections the zero ring) are permitted; zero rings
are permitted for Law and Frame; the first standard vector then equals zero,
which is correctly the unit in the zero algebra. There are no characteristic
restrictions or hypotheses that require a nontrivial coefficient ring. The
bilinear-law and matrix descriptions still have exactly one rank-one object
and arrow over all rings, including the zero ring. The indexing of the two
associativity sums and the order of composition were checked on arbitrary
vectors: a(h,a(g,m))(x,y)=h^-1 g^-1 m(ghx,ghy), hence the label gh.

Searches actually run with the prescribed msearch wrapper, group N5 and this item:

1. leanfinder: "Scheme representing commutative associative algebra laws with
   fixed first basis vector as unit and smooth change of basis groupoid".
   Eight hits: AffineSpace, standard smooth algebras, AffineSpace.coord/over,
   and related notation. None is a construction of this algebra-law groupoid.
2. loogle: `"AlgebraicGeometry", "Groupoid"`. Successful search, zero hits.
3. grep: `unitFramed|UnitFramed|representFAd|multiplicationTable|algebraStructureScheme`.
   Successful Mathlib search, zero hits.
4. leansearch: "Parameter scheme for unital commutative algebra structures
   and unit preserving invertible matrices". Eight hits: Unitization and
   Matrix inverse/determinant declarations, none this parameter scheme/groupoid.
5. rg in both `lean/WeilConjectures` and `lean/Sheaf` for
   `unitFramed|UnitFramed|representFAd|algebraStructureScheme|multiplicationTable`:
   no hits. The prescribed node-id grep in `lean/WeilConjectures` also found none.
   A further name-conflict search in `dag/lean_names_upstream.json` and both
   source trees found no `AlgebraicGeometry.UnitFramedAlgebra` namespace.

The module compiled cleanly with the required scompile.py server confirmation.
The wrapper's initial local attempt reported disk exhaustion, then its normal
server fallback succeeded; no tool or live source was modified.
No STATEMENT-DISPUTED flag or node fault is reported.

## Second reading by N5

This is the worker's separate source-and-signature audit; no independent reader
is claimed. The dispatch brief requires self-delivery and reserves independent
review to the maintainer after delivery.

Reopened the node, criteria.tex Tag 05YP, and the final module. Checked all three
families of ideal generators term by term, checked that Frame means an actual
linear equivalence fixing e_1, and checked all matrix columns against the
localized coordinates. The initial ambient coordinate call omitted the explicit
base scheme argument; the compile diagnosed this, and it now passes S explicitly.
The integral model now uses Spec (ULift Z) explicitly rather than an abstract
chosen terminal scheme. Added the five group laws and the two rank-one clauses
so these parts can be read directly in the conclusion record.

Checked the arrow pullback order: its first projection is the later arrow h,
its second is the earlier arrow g. The composition frame formula is g(h(x)),
so its label is gh. The source/target equations of the exact recorded groupoid
predicate supply the rest of the arrow formulas. The coefficient equivalences
and their naturality fields account for arbitrary nonaffine test schemes and
all pullbacks; no affine-only substitution, arbitrary map, or uncharacterized
Nonempty choice is used. All construction data precede the sole sorry theorem,
and all universes and variables are explicitly bound.
