## Worker report

The module `Sheaf.AlgebraicGeometry.PrimitiveWeightLogarithmicRigidity` states
`AlgebraicGeometry.primitiveWeight_logarithmic_rigidity`. Its proof is `sorry`.
The four preceding definitions construct the polynomial evaluation points, monomial
character evaluations, fixed ordered multiplication chart, and right logarithmic
derivatives needed to state this node. They are canonical helpers of this item,
listed in `lean.declarations`; all have real bodies and source/blueprint docstrings.
No independent mathematical notion or extra theorem has been introduced.
The node's statement, dependencies, and proof are unchanged; only `lean` changes.

Clause-by-clause correspondence:

- Nonzero commutative base ring: `(A : Type u) [CommRing A] [Nontrivial A]`.
  There are no field, characteristic, reducedness, domain, or torsion hypotheses.
- Finite-rank free abelian group: `(M : Type u) [AddCommGroup M]`,
  `[Module.Free ℤ M] [Module.Finite ℤ M]`, using the canonical integer-module
  structure on an additive abelian group.
- Split torus: the exact dependency `ringDiagonalizableGroup A M`.
  Its group scheme is `Spec (AddMonoidAlgebra A M)` with the canonical Hopf structure.
- Rational independence of `r,s`: `hrs` says every integer relation
  `a • r + b • s = 0` has `a = b = 0`. This is equivalent to independence in
  `M ⊗ ℚ`: clear the denominators of a rational relation, and use that a free
  abelian group is torsion-free; conversely tensor an integer relation.
- Finite set J: `(J : Type u) [Fintype J]` without a nonemptiness assumption.
- Nonnegative integers: `i k : J → ℕ`.
- Primitive exponent pairs: `hprimitive : ∀ j, Nat.Coprime (i j) (k j)`.
- Pairwise distinct weights: `hdistinct` is injectivity of
  `j ↦ i j • r + k j • s`.
- Group scheme with the full group diagrams: `H : Grp (Over (Spec (.of A)))`.
  This is precisely the categorical group-object encoding used by the torus node.
- Smooth and affine over A: `[Smooth H.X.hom] [IsAffineHom H.X.hom]`,
  applied to its structure morphism, not to an unrelated morphism.
- Scheme action of the torus: `[ModObj (ringDiagonalizableGroup A M).X H.X]`.
  Mathlib's `ModObj` supplies the actual action morphism and its unit and
  associativity laws. `hautomorphisms` requires that action to preserve group
  multiplication on every test scheme U and every U-valued torus point.
  For each t, the inverse action is that of t⁻¹ by the action laws, so this is
  exactly action by group automorphisms (unit and inverse preservation follow).
  No embedding of the torus into H is assumed.
- Each p_j is an A-scheme morphism from the additive affine line, represented
  by `algSpec` of `MvPolynomial PUnit A`; `PUnit.{u+1}` is a singleton index.
  `hclosed` asserts `IsClosedImmersion (p j).left`.
  `hadditive` is the group-homomorphism identity
  `p_j(a+b)=p_j(a)*p_j(b)` for every commutative A-algebra R and a,b in R.
  Since all p_j are actual scheme morphisms, their point functions are natural.
  This universal identity is equivalent to the addition diagram by affine Yoneda;
  it also implies p_j(0)=1 and p_j(-a)=p_j(a)⁻¹ by group cancellation. Thus it
  states exactly closed group homomorphisms, without assuming a field to use the
  existing field-only StandardGroupSchemes.additive API.
- Fixed enumeration: `e : Fin (Fintype.card J) ≃ J`.
  `primitiveWeightOrderedProduct` pulls back the singleton variable to `X (e q)`,
  composes with `p (e q)`, and takes `List.ofFn ... |>.prod` in that order.
  The domain is literally `algSpec` of `MvPolynomial J A`.
  `hchart : IsIso ...` states the required scheme isomorphism: an isomorphism in
  `Over (Spec A)` is the same as an underlying scheme isomorphism over the base.
- Weight formula: `hweight` says, on every A-algebra R,
  `t • p_j(z) = p_j(primitiveWeightCharacter ... t (i j • r + k j • s) * z)`.
  `primitiveWeightCharacter` recovers t's unique algebra map by full faithfulness
  of `algSpec`, then evaluates the actual group-algebra basis element `single m 1`.
  This is the monomial character, not an arbitrary supplied character. The formula
  is imposed on all test algebras, rather than only on A-valued points.
- F0,F1: actual morphisms in `Over (Spec A)` from `Spec A[x,y]` to H.
  The variable index `ULift.{u} (Fin 2)` has two elements, with x corresponding to
  down-value 0 and y to down-value 1; this handles the full site universe.
- Origin to identity: `horigin0` and `horigin1` use the coefficient-fixing
  evaluation at both variables zero and the identity element of the group of
  morphisms `Spec A ⟶ H`.
- Equivariance of both morphisms: `hequivariant` quantifies over an F satisfying
  `F = F0 ∨ F = F1` and over every commutative A-algebra R, torus R-point t and
  coordinate pair z; it expresses the weighted action with r on x and s on y.
  This universal point identity is exactly the scheme equivariance diagram.
- B and its dual numbers: `MvPolynomial (ULift (Fin 2)) A` and `DualNumber B`.
  Mathlib's dual numbers are `TrivSqZeroExt B B`, so every element is a unique
  pair (constant coefficient, epsilon coefficient), epsilon squared is zero,
  and this is the canonical model of `B[epsilon]/(epsilon^2)`.
- Right logarithmic derivatives: `primitiveWeightLogDerivative ... d` uses
  `MvPolynomial.aeval` to send each variable to its actual constant inclusion
  plus epsilon in direction d, composes with F, and multiplies by the inverse
  of the constant extension of F. This is the specified right order.
  Reduction along `TrivSqZeroExt.fstHom` sends the product to F*F⁻¹=1, so these
  are tangent points at identity. They are written as their underlying H(DualNumber B)
  points: equality in the kernel subtype is equivalent to equality of these
  underlying points. No tangent-module operation or Lie-algebra comparison is
  assumed or needed for the two equalities in the statement; coefficients of
  epsilon are supplied by the actual dual-number construction.
- Equal x and y logarithmic derivatives: `hx` and `hy`, with directions 0 and 1.
- Conclusion: `F0 = F1`, equality of the actual scheme morphisms over A, hence
  also equality of their underlying scheme morphisms.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`:
  `AlgebraicGeometry.ringDiagonalizableGroup` (its full signature, body, and
  Hopf-structure docstring were read), with `ringDiagonalizableGroupMap` also read.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, the
  affine-local smooth ring-map definition; the recorded dependency explicitly
  identifies it with the formally smooth, locally finitely presented notion.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, the finitely supported
  monoid algebra; `MvPolynomial.algHom_ext` for its uniqueness clause, and
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval`, used in the helpers.
- `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv` and its monomial
  formula, imported for the stated proof plan of the polynomial partial-derivative
  dependency. The theorem itself uses the node's direct dual-number formulation.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding and surjectivity on stalks.
- Proof dependency `lem-a1-locally-ringed-space-affine-adjunction` is a Mathlib
  leaf: `AlgebraicGeometry.ΓSpec.locallyRingedSpaceAdjunction`, whose hom-equivalence
  is the stated natural bijection. Its module `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
  is imported privately for the proof plan.
- Additional Mathlib machinery: `algSpec` and `algSpec.fullyFaithful` from
  `Mathlib.AlgebraicGeometry.Group.Affine`; `ModObj` and its pointwise action from
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`; `Module.Free`, `Module.Finite`,
  and the real dual-number algebra and inclusion from `Mathlib.Algebra.DualNumber`.

Edge cases checked before and after writing:

- Empty J: the list product is the identity morphism; `hchart` identifies H with
  the base, and no variable or nonempty-set requirement is imposed.
- Primitive axial pairs (1,0), (0,1) are allowed; (0,0) is excluded by coprimality.
- In characteristic p the nonprimitive pair (p,0) would allow a nonzero x^p with
  zero partial derivatives, confirming why primitivity matters. For (2,1) over
  F₂, the y derivative detects the coefficient, so the statement retains that case.
- For (3,2) over Z/6, simultaneous annihilation by 3 and 2 forces the coefficient
  to vanish by Bezout; nilpotent coefficients cause no change to that argument.
- Noncommutative H: list multiplication preserves the chosen enumeration;
  the proof uses (d*u)⁻¹*(d*v)=u⁻¹*v with no commutation.
- Base change to nonreduced or zero test algebras is allowed; all test-algebra
  binders are in the base universe and carry no Nontrivial restriction. This is
  not a vacuous test-universe condition: A, its polynomial rings, group algebra,
  tensor products and dual numbers all occur in that universe.
- Lifts on the singleton and pair index types avoid forcing u=0; general J and
  M remain unrestricted in the common ambient universe of the recorded torus.

Searches (all msearch calls used group Q15 and this item):

1. `leanfinder`, query "Equivariant maps from affine plane to a group scheme with
   primitive torus coordinate weights are determined by their logarithmic derivatives":
   eight hits, chiefly `AlgebraicGeometry.AffineSpace.hom_ext`, `hom_ext_iff`,
   `homOverEquiv`, and ordinary affine-map extensionality. None states the theorem.
2. `loogle`, query `MvPolynomial.pderiv, DualNumber`: zero hits.
3. `grep`, query `logarithmic.*deriv|pderiv.*inject|primitive.*weight`, subdirectory
   `Algebra`: two hits, a Lie-theoretic primitive-vector argument and
   `MvPolynomial.pderiv_rename`; neither is this theorem.
4. `leansearch`, query "Equivariant morphisms from affine plane to a smooth affine
   group scheme with primitive coprime torus weights are equal if both right
   logarithmic derivatives agree": eight hits, affine-map/equivalence extensionality,
   smooth-manifold `LeftInvariantDerivation.ext`, and `Action.HomSubtype`. No match.
5. Searches for an existing action/additive affine-space interface: `leansearch`
   query "An action of a group object on another group object by group automorphisms"
   returned categorical actions by abstract groups, ConjAct, and MulAut; `leanfinder`
   query "Affine space over a commutative ring and additive group scheme over a ring"
   returned AffineSpace. Reading the categorical APIs gave the usable `ModObj`.
6. `rg` over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf`, with logarithmic,
   primitive-weight, group-scheme, additive-group and torus-action patterns:
   no existing arbitrary-ring primitive-weight rigidity statement. Project hits
   are power-series logarithmic derivatives and unrelated logarithmic geometry.
   The StandardGroupSchemes additive interface is field-only; we use actual
   polynomial spectra and the universal addition identity instead of copying it.
   `rg` on the item id in `lean/WeilConjectures` has no hits. A final name search
   for all five new declaration names across those three trees and
   `dag/lean_names_upstream.json` has no hits.

Source checks: read the node's complete six-step agent proof, the current blueprint
unit `sk-thm-sf-ctf-stability` and its direct-images statement and proof, and Conrad
online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Proposition
5.1.16 and Section 6.2 Step 3. As the node explicitly says, this is an agent
auxiliary lemma in that coordinate setting, not a theorem quoted from Conrad.
The unchanged item has no blueprint id of its own (`blueprint_refs.py ancestor`
returns None). No statement correction, disputed assertion, dependency repair,
or new node is needed. The requested CompactObject example has been withdrawn
in the current read clone (its module contains only a withdrawal notice); the
current RingDiagonalizableGroup module supplies the applicable module conventions.

Validation: scompile.py compiled this file cleanly on the server, both as a sandbox
module and with its library module name. All universes and variables are explicitly
bound (`set_option autoImplicit false`). No diagnostic commands remain. The main
statement docstring contains every step of the supplied proof and names its dependencies.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
