## Worker report

The module `Sheaf.AlgebraicGeometry.GenusOneAbelGroupIdentification` states
`AlgebraicGeometry.exists_genus_one_abel_group_identification`. Its only new
declaration is this theorem, with proof `sorry`. No definitions, axioms, helper
theorems, new nodes, dependency repairs, or statement corrections are supplied.
The item copy changes only `lean`.

Source read: `literature/stacks-project/moduli-curves.tex`, example-pos-dim,
Tag 0DSV, lines 607–635. Its genus-one paragraph identifies Hilb^1 with Pic^1
and translates Pic^1 to Pic^0 to give the abelian-variety structure on the
curve. The five proof steps in the DAG are reproduced in the theorem docstring,
including the rank-one algebra argument on arbitrary bases, the closed Abel
embedding with whole scheme-theoretic image, and transport of the group law.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Y/k with its specified structure morphism | `{Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))` |
| Connected curve, including dimension one and nonemptiness | `[IsConnectedCurve f]`, which extends `IsCurve f` with connectedness and Krull dimension exactly one |
| Smooth | `[Smooth f]` |
| Projective in the blueprint's finite projective-space convention | `[IsHProjective f]` |
| Genus one | `(hg : f.genus = 1)` using the recorded genus declaration |
| Origin O in Y(k) | `(O : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk f)`; its `Over` compatibility is exactly the section identity |
| k-morphisms m and i making Y a group scheme | `∃ (_ : GrpObj (Over.mk f)), ...`; `MonObj.mul` is the product-over-k morphism and `GrpObj.inv` is the inverse morphism, with the associativity, unit and inverse identities as structure fields |
| Commutative group scheme | `IsCommMonObj (Over.mk f)` states commutation of multiplication with the cartesian braiding |
| Identity is the given O | `CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (.of k)))) ≫ η[Over.mk f] = O`; the map through the chosen tensor unit is the identity point on the actual Spec k test scheme |
| Pic^0 is precisely the degree-zero classes, with tensor product | `∃ G : Subgroup Y.Pic, (G : Set Y.Pic) = f.picZero`; `Y.Pic` already has its tensor-product group operation and G inherits it |
| Bijective group homomorphism alpha | `∃ α : (Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk f) ≃* G, ...`; `MulEquiv` supplies both bijectivity and the homomorphism identity |
| alpha(P) is the class of O_Y(P-O) | For every P, the witnesses `p o : closedPoints Y` have values `P.left.base s` and `O.left.base s` for every `s : Spec (.of k)`; the representative of `(α P).val` is isomorphic to `Scheme.Divisor.moduleOfSmoothConnectedCurve k Y f (Finsupp.single p (1 : ℤ) - Finsupp.single o (1 : ℤ))` |
| alpha(P+Q) = alpha(P)+alpha(Q) | `α.map_mul P Q`, with the same operation written multiplicatively on rational points and as tensor product on Picard classes |
| alpha(O) = 0 | The explicit conjunct `α O = 1`; 1 is the trivial line-bundle class |

The existential subgroup is an encoding of the already recorded subset
`f.picZero` as a group; equality of its carrier prevents substituting a smaller
subgroup. It adds no assumption. The representative isomorphism fixes the Abel
map at every point, so this is not an arbitrary abstract group identification.
Since Spec k is nonempty and has one point, quantifying over all of its points
specifies the closed support of each rational section without a choice of a
point or an extra inhabited hypothesis. Closed-point witnesses carry no
additional data, because their property fields are propositions.

Statement dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, line 180: commutative division ring.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, lines 58–63: splitting
  of every polynomial, equivalent to the root formulation in the dependency.
- `AlgebraicGeometry.IsCurve`, `IsConnectedCurve`, and
  `AlgebraicGeometry.Scheme.Hom.genus`,
  WeilConjectures.AlgebraicGeometry.Curve: the exact curve class and recorded
  genus, including its documented smooth-proper comparison with H^1(O).
- `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective, lines 30–38:
  factorization through a finite-coordinate projective space.
- `AlgebraicGeometry.Scheme.Hom.picZero`,
  WeilConjectures.AlgebraicGeometry.Curve, lines 168 onward: the subset of Pic
  whose `picDegree` is zero, not a replacement Picard functor.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible, lines 55–59:
  local triviality with rank one.
- `AlgebraicGeometry.Scheme.Divisor.moduleOfSmoothConnectedCurve`,
  Sheaf.AlgebraicGeometry.DivisorModule, lines 287–300: the explicit rational
  function module associated to a divisor, with all regularity, integrality,
  and Noetherian instances obtained from the curve hypotheses. Divisors are
  the existing finitely supported integer functions on closed points.
- `AlgebraicGeometry.Scheme.exists_divisorClassGroup_addEquiv_pic_associatedModule`,
  Sheaf.AlgebraicGeometry.DivisorClassCurve: the isomorphism of divisor classes
  with the Picard group, characterized by precisely that explicit module.
  The signature and full proof docstring were read; the module is imported
  publicly as the item's recorded statement dependency.

Additional existing APIs: `CategoryTheory.GrpObj`, `IsCommMonObj`, and the scoped
`CategoryTheory.Hom.group` from Mathlib.CategoryTheory.Monoidal.Cartesian.Grp;
`Over`'s cartesian structure and product description from
Mathlib.CategoryTheory.Monoidal.Cartesian.Over. No second group-scheme notion
is introduced. This agrees with the existing record of def-sc-group-scheme.

Every recorded proof-dependency module is also imported, using plain imports
when it is only needed for the proof. These include SymmetricAbelImageGeometry,
HilbertToPicardMorphism, CurveBaseChangeRelativeDimensionOne,
FiniteLocallyFreeStructureSheaf, SmoothConnectedCurveLocalRings, the upstream
Jacobian/Picard and Hilbert modules, ProjectiveSpace, Curve.RiemannRoch, and
Mathlib's scheme-theoretic image, closed immersion, properness, separatedness,
fully faithful functors, and Yoneda. The proof-only Mathlib matches for
representable uniqueness, Yoneda, proper base change, and closed sections
require no replacement interfaces.

Edge cases checked before finalizing:

- P=O: the divisor is zero, its module is the structure sheaf, and alpha(O)=1.
- Repeated or coincident rational points: the support witnesses are forced by
  the rational section; subtraction in the free abelian divisor group handles
  cancellation without a distinctness assumption.
- All characteristics, including 2 and 3: no division, Weierstrass equation,
  characteristic restriction, or prime-to-characteristic condition is imposed.
- The empty scheme and dimension-zero schemes are excluded exactly by the
  node's connected-curve/genus hypotheses; no extra nonemptiness is assumed.
- Nonreduced test schemes: the group object identities are scheme identities,
  hence apply to all test schemes, not only rational points. Only the Abel-map
  identification is restricted to the k-points, as in the node.
- The field and schemes use arbitrary universe u. No universe equality beyond
  the library's field/curve convention or small independent test universe is
  imposed. There is no choice of an unrelated map or group law in a hypothesis.

Searches actually run on 2026-10-24:

- msearch.py leanfinder: "A smooth projective genus one curve with an origin is
  isomorphic to its degree zero Picard group via the divisor P minus O".
  Eight hits, including WeierstrassCurve.Affine.Point.toClass and coordinate
  point conversions, not the theorem for arbitrary smooth projective curves.
- msearch.py loogle: `WeierstrassCurve.Affine.Point.toClass`. Six hits: the
  affine Weierstrass class-group injection and its formulas, not the required
  Picard-zero bijection or scheme group structure.
- msearch.py grep: `genus|picard|Picard|toClass` in
  AlgebraicGeometry/EllipticCurve. Eight hits in Weierstrass.lean and
  Affine/Point.lean; none is the required statement.
- msearch.py leansearch: "A smooth projective genus one curve with a rational
  point is isomorphic to its degree zero Picard group scheme". Eight hits,
  including CommRing.Pic.mk_eq_one_iff and Weierstrass coordinate models;
  none concerns the arbitrary pointed curve of this item.
- rg in lean/WeilConjectures and lean/Sheaf for genus-one, Abel identification,
  picZero, and elliptic-related names. The Jacobian and divisor/Picard
  interfaces are already available; no matching theorem was found. The
  existing SymmetricAbelImageGeometry module supplies a proof dependency,
  with a closed pointed Abel embedding and full image in genus one, but
  does not state the transported group law and pointwise Picard equivalence.
- rg for the exact item id in lean/WeilConjectures returned no declaration.
- Read the dependency node JSON records and searched the relevant Mathlib
  monoidal/cartesian modules for the existing group and commutative structures.

No mathematical dispute or node fault was found. Initial elaboration probes
needed an explicit integer annotation on divisor coefficients and a fully
qualified canonical map to the tensor unit. The final support characterization
uses all points of Spec k and avoids relying on an unavailable Inhabited instance.

## Second reading by Q74

A separate pass through the node and the completed module checked every row
above. This is the dispatcher's sole worker's second pass; no independent
reviewer or subagent was started, as the assignment forbids that. The
maintainer's independent delivery review remains separate.

The pass specifically checked that projective means IsHProjective, that genus
and picZero use the dependency records, that O is a section over k, that
commutativity is asserted for scheme multiplication, and that the identity
point equals O. The subgroup has exactly the degree-zero carrier. The
MulEquiv uses the group law of the existential scheme group object and the
inherited tensor law of Pic. Its values are fixed by the recorded divisor
module on the actual two rational supports, rather than only by an abstract
bijection. The sign is P minus O. No geometric-integrality hypothesis,
Weierstrass model, characteristic restriction, or extra rational base point
has been added. The only revisions were the elaboration fixes described above;
the DAG statement and dependencies are unchanged.
