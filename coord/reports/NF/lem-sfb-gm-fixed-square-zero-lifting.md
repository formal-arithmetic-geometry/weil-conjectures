## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.GmFixedSquareZeroLifting` states
`AlgebraicGeometry.exists_gm_fixed_lift_of_square_zero`, with one `sorry` and no definitions
or proved helper statements. The node's mathematical statement and proof plan are unchanged.
The already landed `def-sfb-split-torus-over-ring` is added to `stmt_deps` to cite the actual
multiplicative group scheme used by the statement. There are no new definition nodes and no
dependency repairs. Fixedness is written inline rather than introducing another predicate.

Hypothesis and clause correspondence:

- The arbitrary commutative base ring is `(R : Type u) [CommRing R]`.
- The coordinate ring is `(C : Type u) [CommRing C] [Algebra R C]`. The scheme is exactly
  `Spec (.of C)`, represented in the slice by
  `(algSpec (.of R)).obj (op (CommAlgCat.of R C))`. Its structural map is
  `Spec.map (CommRingCat.ofHom (algebraMap R C))`, by `algSpec_obj_hom`.
- Smoothness is the recorded `[Smooth (Spec.map ...)]`, with no affine-local substitute,
  extra presentation, dimension, finite-type, nonemptiness or field assumptions.
- The specified multiplicative group with its standard unit multiplication is
  `(RingGroupSchemes.multiplicative R).X`. Its definition is precisely the Laurent Hopf
  spectrum `Spec (.of (LaurentPolynomial R))` over `Spec R`.
- The action is the instance binder `[ModObj (RingGroupSchemes.multiplicative R).X ...]`.
  Mathlib's `ModObj.smul` is a morphism in `Over (Spec R)` from the product to X;
  `ModObj.one_smul` and `ModObj.mul_smul` are precisely the identity and associativity
  equations. This is an actual scheme action, not just an action of R-valued units.
- For any test algebra B, the point is a genuine `C →ₐ[R] B`. The expression
  `(algSpec (.of R)).map (CommAlgCat.ofHom x).op` is its corresponding slice morphism.
- The two commutative R-algebras are `B₁ B₀` with their `CommRing` and `Algebra R` binders.
  The map is `p : B₁ →ₐ[R] B₀`; `hp : Function.Surjective p` is surjectivity.
  Its kernel is not independent data: `hJ : RingHom.ker p.toRingHom ^ 2 = ⊥` says exactly
  that J = ker p has square zero.
- The prescribed point is `x₀ : C →ₐ[R] B₀`. The hypothesis `hx₀` tests every commutative
  R-algebra B and every `q : B₀ →ₐ[R] B`. Giving this q is equivalent to giving B a
  B₀-algebra structure with its induced R-algebra structure. Thus every algebra extension
  in the node is included, without an extra injectivity or flatness condition on q.
- The variable t ranges over slice morphisms `Spec B → G_m,R`. By the Laurent polynomial
  universal property these are exactly units of B, including over nonreduced rings.
  Mathlib's cartesian `CategoryTheory.Hom.smul` composes the product point (t,x) with the
  given action. Therefore the displayed equality is exactly `a(t,x_B)=x_B`.
- The conclusion chooses `x₁ : C →ₐ[R] B₁`, requires `p.comp x₁ = x₀`, and repeats the
  same universal fixedness condition for every `q : B₁ →ₐ[R] B` and every t. It does not
  assert uniqueness, equivariance of p beyond its algebra-map meaning, or a chosen lift.
- The sole universe u is arbitrary; it can be enlarged to contain R, C, B₀, B₁ and any
  test algebra simultaneously. The test algebra universe is the same as the base universe,
  never an independent smaller universe. Laurent test extensions and tensor products live
  there. No residue-characteristic, reductivity, connectedness, Noetherian or field binder
  is present, and zero rings are allowed.

Dependency declarations read in full and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`, implementing
  `def-weil-affine-spectrum`; `Mathlib.AlgebraicGeometry.Group.Affine`: `algSpec`,
  `algSpec_obj_hom`, `algSpec.map`, and its full/faithful affine correspondence.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, the exact
  recorded `def-sbc-smooth-morphisms` notion. The current blueprint definition under
  `literature/blueprint/latest/blueprint/sec-proper-base-change/sk-thm-p1/` was read too.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`:
  `AlgebraicGeometry.RingGroupSchemes.multiplicative`, recorded among the declarations
  of `def-sfb-split-torus-over-ring`. Its group data comes from Mathlib's Laurent Hopf
  algebra, with z sent to z tensor z, 1, and z inverse. No private copy is introduced.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.ModObj`, including the complete
  action-map and action-law signature; `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`:
  `CategoryTheory.Hom.smul` and `Hom.mulAction`, whose underlying action is
  `lift t x` followed by the internal action morphism.
- Proof-only imports are `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  (`IsClosedImmersion`, node `def-weil-closed-immersion`) and
  `WeilConjectures.AlgebraicGeometry.Thickening` (`IsFirstOrderThickening`, node
  `def-sbc-first-order-thickening`). The grading proof dependency
  `lem-sfb-gm-affine-action-grading` has no recorded declaration yet, so no import is
  available for it; its five-step use is preserved in the theorem's proof docstring.

Source and edge-case reading:

Read Stacks `groupoids.tex`, Example `example-multiplicative-group` (022U),
Example `example-Gm-on-affine` (0EKJ) and Lemma `lemma-complete-reducibility-Gm` (0EKK).
Read Milne's printed pp.254--256: Theorem 13.1 and Lemma 13.6 assume a field, as the
node explicitly acknowledges; they motivate rather than assert the relative theorem.
The relative proof in the node works over an arbitrary base: project an ordinary smooth
lift to weight zero, and use J squared zero for products of opposite nonzero weights.

Checked J=0 (the lift is transported across an algebra isomorphism); trivial action
(all points are fixed and ordinary smooth lifting applies); empty affine X/zero C
(the point hypothesis enforces the relevant zero-ring case); R or B₀ equal to the zero
ring; arbitrary characteristic; and the action with weights +1,-1 on R[u,v]. In the
last case an ordinary lift can send u and v into J, and the only potentially troublesome
weight-zero product uv vanishes because J²=0. Fixedness is genuinely universal: checking
only units in B₀ would fail to detect weights over small fields, whereas q includes
B₀ → B₀[z,z⁻¹] and t includes the universal Laurent unit. No node fault or
STATEMENT-DISPUTED flag remains.

Searches (all before writing the statement):

- `msearch.py ... leanfinder "Fixed points of a multiplicative group action on a smooth
  affine scheme lift across square zero extensions"`: eight unrelated ordinary
  infinitesimal/unramified/affine-space results; no fixed-point lifting theorem.
- `msearch.py ... loogle "Algebra.FormallySmooth, Units, MulAction"`: no hits.
- `msearch.py ... grep "GmAction|gmAction|fixed.*lift|lift.*fixed"`: nine unrelated hits
  on Galois fixed fields, categorical lifting properties, and tensor-product maps.
- `msearch.py ... leansearch "Natural action of multiplicative group functor units on
  functor of points of an affine scheme"`: general units actions and finite Galois
  natural actions, not this lifting assertion.
- `msearch.py ... leanfinder "A multiplicative group scheme action on an affine scheme
  is a natural family of actions of units on algebra homomorphisms"`: general action
  maps and affine-space results. Direct Mathlib source search then found the reusable
  internal-action API `ModObj` and its cartesian Hom action.
- `rg` of the same action/fixed-lifting patterns in `lean/WeilConjectures` and
  `lean/Sheaf`: no exact theorem. The discrete-module fixed-lift statements concern
  finite-index subgroup arithmetic, and the adic fixed-residue statements concern a
  different notion. The literal item-id search in `lean/WeilConjectures` has no hits.
- `rg` for multiplicative-group constructions found `StandardGroupSchemes.multiplicative`
  (field-only) and then `RingGroupSchemes.multiplicative` (arbitrary rings, the one used).
  `rg` of `dag/lean_names_upstream.json` for the proposed theorem name and Gm fixed-point
  names found none. DAG searches found the existing ring-base torus definition, so no
  new notion or definition node is needed. `blueprint_refs.py search "multiplicative
  group action"` found no blueprint nodes.

Validation: the module compiled cleanly through the prescribed server `scompile.py`.
The delivery dry run and push are recorded by the required `deliver2.py` wrapper.

## Second reading by NF

A separate self-review pass read the node and final Lean signature side by side; the
worker brief prohibits starting another agent, and the maintainer supplies independent
review after delivery. This paragraph does not claim an independent second worker.

Verified the structural map is the algebra-map spectrum, and the action is in the
slice over that very Spec R. Verified that both universal fixedness clauses test the
same base-change point q composed with x, that the conclusion reduces the chosen lift
to the particular prescribed x₀, and that the kernel ideal is exactly ker p. Rechecked
the `ModObj` signature and the cartesian Hom action: the unit law and multiplication
law are carried by the actual action instance, not assumed as unrelated equalities.
Rechecked Laurent units via affine Spec, including small finite residue fields and
nonreduced test algebras. No mismatch was found. The landed ring-base torus node was
added to statement dependencies; no mathematical statement or proof was changed.
