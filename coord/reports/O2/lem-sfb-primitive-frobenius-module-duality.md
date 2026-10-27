## Worker report

The item is stated, with no change to its natural-language statement, in
`Sheaf.AlgebraicGeometry.PrimitiveFrobeniusModuleDuality`, declaration
`AlgebraicGeometry.primitive_frobenius_module_duality`. All theorem proofs are `sorry`.
The new definition interface is in `Sheaf.AlgebraicGeometry.FrobeniusPrimitiveModuleData`.
Source read: Milne, Algebraic Groups (2017), Section 14(e), equations (96)--(98),
Proposition 14.41, Remark 14.42, Lemmas 14.43--14.44 and Theorem 14.46,
printed pp.292--295. The construction follows the accepted eight-step node proof,
which is included in the theorem's docstring with every dependency named.

Clause-by-clause rendering:

- A field of positive characteristic is `{k : Type u} [Field k] (p : ℕ)
  [Fact p.Prime] [CharP k p]`. Primality is equivalent to positive characteristic
  for a field, not a perfection or finiteness condition. The binder excludes
  characteristic zero exactly as the node does.
- `FrobeniusPrimitive.coefficientAction k p` is composition of Mathlib's
  `powersHom` of the actual `frobenius k p` with `MulSemiringAction.compHom`.
  `SkewRing k p` has Mathlib's `SkewPolynomial k` finite-sum carrier, and
  `skewRing` instantiates its multiplication with precisely that action.
  `SkewPolynomial.monomial_mul_monomial` gives the displayed multiplication
  c*b^(p^i), not b*c^(p^j). There is no inverse Frobenius assumption.
- `actionValue` is the finite sum of `algebraMap k R c * x ^ (p ^ i)`.
  `algebraModule_existsUnique` specifies exactly this scalar multiplication;
  `algebraModule` selects its uniquely specified structure. In particular
  constants act by ordinary multiplication and F acts by the p-th power.
  The zero test algebra is included: no `Nontrivial R` or `CharP R p` is imposed.
- `M : Type v`, `[AddCommGroup M]`, `[Module (SkewRing k p) M]`, and
  `[Module.Finite (SkewRing k p) M]` express a finitely generated left module.
  `M →ₗ[SkewRing k p] R` is exactly the additive maps respecting its actions.
- `Representation k p M` includes a group scheme `group`, commutativity
  `IsCommMonObj group.X`, additive bijections `points R` from its R-points
  to `M →ₗ[SkewRing k p] R`, and the naturality equation for every algebra
  homomorphism R →ₐ[k] S. The functor is specified on objects and arrows by
  these equations; no arbitrary map stands in for its canonical action.
- The first conjunct asserts existence of that representing data for every
  finite M, with `IsAffine U.group.X.left`, `LocallyOfFiniteType` and
  `QuasiCompact` of its structure morphism, and a closed embedding into
  the product indexed by `Fin n` of the existing additive group. The embedding
  is a morphism in `Grp`, and `IsClosedSubgroupScheme i.hom.hom` is the
  dependency's existing closed-subgroup predicate.
- In the second conjunct, G is an actual `Grp (Over (Spec (.of k)))`, affine,
  of finite type, and admitting the same finite-power closed embedding.
  No commutativity hypothesis is added: it follows from that embedding.
- `PrimitiveFunctions k G` is literally `Additive (G ⟶ Grp.mk (additive k))`.
  The existing categorical Hom group supplies pointwise addition. The
  `additive_commutative` helper asserts commutativity of the existing fixed
  additive law, rather than introducing another Ga. `primitiveValue` composes
  g with the actual group homomorphism f and reads the polynomial coordinate
  using `Spec.preimage`. Thus it is exactly f_R(g).
- `primitiveModule_existsUnique` specifies its A-action by the displayed
  evaluation equation at every R-point. This uniquely fixes c*f and F*f,
  rather than choosing unspecified module data. `primitiveModule` selects
  that uniquely characterized structure.
- `Module.Finite ... (PrimitiveFunctions k G)` states finite generation of
  P(G). For every representing datum U of P(G), the theorem gives a group
  scheme isomorphism `e : G ≅ U.group` and the equation
  `U.points R (Additive.ofMul (g ≫ e.hom.hom.hom)) f = primitiveValue ... f g`.
  This is precisely the evaluation reconstruction with its value on every
  commutative test algebra. Existence of a representer of P(G) follows by
  applying the first conjunct to this finite module. Quantifying over all
  representers is the usual choice-independent meaning of representability:
  they are uniquely isomorphic by their specified natural bijections.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group-scheme morphisms.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.Hom.commGroup`
  and the pointwise Hom group, through the imported group-scheme framework.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive`
  and its uniquely specified `additiveGroup` instance. Their full definitions
  and group-law docstrings were read.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme` (the existing closed immersion
  and injective-on-points predicate, not a replacement).
- New interface uses `SkewPolynomial`, `SkewPolynomial.sum`,
  `SkewPolynomial.instRing`, `MulSemiringAction.compHom`, `powersHom`,
  `frobenius`, `Spec.preimage`, `LinearMap`, `AlgHom`, and the same affine
  spectrum and Ga objects as its definition dependencies.
- All currently stated proof-dependency modules are imported privately in
  the item's module. In particular it imports
  `Sheaf.RingTheory.ConnectedFilteredCoalgebraKernelPrimitive` and its
  `Coalgebra.exists_primitive_mem_ker_of_not_injective` statement. The basis
  node `lem-sfb-semilinear-restricted-symmetric-basis` has no declaration or
  match at the read snapshot and is not imported; no part of its proof is
  used to manufacture data in these definitions.

Edge cases checked before and after writing: M=0 gives the terminal group and
n=0 is permitted; empty finite products are the categorical terminal group.
The zero algebra R is allowed by all evaluation/module binders. Nonreduced
R, alpha_p, constant additive polynomial relations, and p=2 are included.
The base field may be imperfect, so coefficient Frobenius is never inverted.
Neither M nor P(G) is assumed finite-dimensional over k. Schemes and test algebras are in the ambient universe u of the existing
scheme/group-scheme framework; u is arbitrary. The input module has its own
independent universe v, so no size restriction is imposed on a finite module.
No independent smaller test universe makes the scheme-point tests vacuous. `autoImplicit false` is set
explicitly in both delivered modules. No statement dispute or correction.

Searches actually run (also recorded by the prescribed wrapper): LeanFinder
"Closed subgroup schemes of additive vector groups are reconstructed from modules over
the Frobenius skew polynomial ring" found eight unrelated affine-space,
profinite-group and Galois results; Loogle "SkewPolynomial, MulSemiringAction,
frobenius" found zero hits. Mathlib grep "frobenius|Frobenius" under
Algebra/SkewPolynomial found only the generic example at Basic.lean:70.
LeanSearch "Action of natural numbers by iterating a ring endomorphism
MulSemiringAction" found `MulSemiringAction.compHom`'s surrounding API and
RingHom iteration. The further LeanSearch/LeanFinder searches in the new
node found `SkewPolynomial`, `LinearMap.frobenius`, and generic coefficient
module instances, none of which is the needed specialized action or
primitive-function reconstruction. Project rg searches for the node id and
Frobenius/skew/module primitive names found no existing statement. Existing
`ZetaLinearAlgebra.FrobeniusModule` has linear invertible Frobenius and is a
different notion. Blueprint searches for "Frobenius skew polynomial" and
"primitive functions" each returned zero nodes. Definition-node grep found
only unrelated uses, no interface owning these notions.

Validation: both files compiled separately, in dependency order, via the required
scompile.py server workflow. The final compile has no warnings or errors.
The first compile caught a class-definition reducibility warning (fixed with
`@[instance_reducible]`) and a docstring ending warning (fixed in the docstring).

## New nodes

`def-sfb-frobenius-primitive-module-data` registers the explicit Frobenius
specialization of Mathlib's skew polynomial ring, its canonical module actions,
the literal primitive-function Hom, coordinate evaluation, and representing data
with natural additive bijections. Its source is Milne 14(e), (96)--(98),
Proposition 14.41 and Remark 14.42, pp.292--294. No representer is chosen from
an existence theorem: the main theorem asserts existence of that data. The
only choices in definitions are from unique-existence theorems specifying all
module scalar multiplications. Those supporting theorems and the additive
commutativity statement have the matching defining node, source, and complete
natural-language proof docstrings, and are listed in lean.declarations.
The three search kinds and project/DAG searches are recorded on this node;
they locate the reused generic primitives but no existing specialized interface.
The original item gains only this statement dependency and its Lean record.

## Second reading by O2

This is a worker self-check; no second agent was started, as the dispatcher brief
forbids it. The maintainer's independent delivery review is still required.
I reread the item, new node and both modules after the server compile. The
finite-module quantifier is unrestricted over left modules; the Hom has the
correct left A-linearity. The ring carrier explicitly takes p, preventing a
consumer from losing the chosen characteristic in its type. The polynomial
action uses p^i, and composition has the correct skew order. The primitive
Hom consists of group homomorphisms, not all scheme maps. Evaluation uses the
actual coordinate, and the reconstruction equality mentions every f and g.
Representing bijections are additive and natural, and all finite-type,
affine, commutative and embedding clauses have counterparts as listed above.
No input assumption or conclusion clause was omitted. The zero ring is
retained, and the actions are uniquely determined rather than arbitrary
structures supplied as assumptions. No statement change was needed.
