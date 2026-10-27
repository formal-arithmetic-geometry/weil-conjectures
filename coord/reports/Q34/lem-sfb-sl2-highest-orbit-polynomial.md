## Worker report

The delivery states `AlgebraicGeometry.SL2HighestOrbit.existsUnique_orbit_coefficients`
in `Sheaf.AlgebraicGeometry.SL2HighestOrbitPolynomial`. Its sole postponed proof is `sorry`.
All helpers have real data. The original mathematical statement and proof are unchanged.
This repair removes the unusable theorem dependency
`lem-sfb-rational-representation-comodule-dictionary`. The coaction subtype is written
inline, and `stmt_deps` cites its actual owners `def-sfb-hopf-action-module-data` and
`def-sfb-affine-coordinate-hopf-algebra`, together with `def-sc-general-linear-group`.
No new definition node is needed.

Source checked: Milne, Algebraic Groups (2017), printed pp.466--467, preliminary polynomial
expansion and Propositions 22.14--22.17, and Example 22.33 on printed p.472. The node's
explicit big-cell matrix identity supplies the degree bound without assuming simplicity.
The coaction subtype is rendered inline from the two cited Hopf-definition nodes.

Hypotheses and objects, clause by clause:

- `k : Type u`, `[Field k]`, `[IsAlgClosed k]` give the algebraically closed field.
  There is no characteristic restriction on the principal result.
- `LinearGroupSchemes.specialLinear k 2` is the existing Spec of the determinant-one
  coordinate quotient. Its `Index 2 = ULift (Fin 2)` only relabels the two matrix indices.
  `underlyingGroup` is exactly `LinearGroupSchemes.specialGroup k 2`, and
  `underlyingAffine` is the existing affine-Spec instance. These expose the same
  structures to the unbundled coordinate-comodule interface; neither is a hypothesis.
- `upper a` and `lower a` are Mathlib's actual `SpecialLinearGroup.transvection`, at
  indices (0,1) and (1,0), hence I+aE12 and I+aE21. `torus t` is exactly diag(t,t^-1),
  constructed as upper(t) lower(-t^-1) upper(t) upper(-1) lower(1) upper(-1).
  Multiplying the first three gives rows (0,t),(-t^-1,0), and the final three gives
  rows (0,-1),(1,0). This works in every commutative algebra, including characteristic 2.
- `M : Type u`, `[AddCommGroup M]`, `[Module k M]`, `[FiniteDimensional k M]` give M.
  `c` is written inline as the subtype
  `{c : M →ₗ[k] M ⊗[k] Γ(SL2, ⊤) // Coassociative c ∧ Counital c}`.
  Thus the module is specified by precisely the actual linear coaction and its two Hopf
  laws, rather than by an abstract action on just the k-points.
- `act c R g` is the linear map `(1 tensor ev_g) c`, valued in M tensor R.
  `specialPoints.symm` produces the actual scheme point, composition with isoSpec gives
  its coordinate-Spec point, and `Spec.mapMulEquiv.symm ... .ofConv` is its canonical
  coordinate algebra map. No arbitrary point, evaluation, representation, or coaction
  is chosen. This also avoids confusing the two existing global-section algebra
  structures (`Scheme.Hom.ΓAlgebra` and the canonical Hopf algebra's underlying algebra).
- `(m : ℕ)` means the nonnegative integer m, and `(v : M) (hv : v ≠ 0)` means the
  nonzero vector. `hupper` renders upper-root invariance for every algebra R and a.
  `htorus` renders weight m for every algebra R and every unit t. These families include
  universal polynomial, Laurent and nonreduced algebras, not merely field extensions.
- `f : Module.End k M` and `hf : ∀ z : M, ...` state the defining differential identity
  over `DualNumber k`: lower(epsilon) on z tensor 1 equals z tensor 1 plus f(z) tensor
  epsilon. Quantifying over all z gives the full operator identity, not just its value
  on v. Extending R-linearly is determined by these pure tensors.

Conclusions, clause by clause:

- `∃! w : Fin (m + 1) → M` says there is one unique list w_0,...,w_m.
- The first conjunct quantifies over every algebra R and every a and equates the lower
  orbit with `∑ j, w j ⊗ₜ[k] (a ^ j.val)`. This is exactly the polynomial orbit formula
  in the node's M tensor R order: scalar multiplication by a^j on w_j tensor 1.
- `w 0 = v` is the constant coefficient clause.
- `∀ j : Fin (m+1), (f ^ j.val) v = (j.val.factorial : k) • w j` is every factorial
  identity for 0 ≤ j ≤ m, with the endomorphism power denoting repeated composition.
- `∀ p [CharP k p], 0 < p → m < p → ...` gives precisely the positive-characteristic
  special case. Its first conjunct asserts each factorial is a unit in k; the second
  again quantifies over every R,a and gives the sum with coefficient
  `a ^ j.val * algebraMap k R (j.val.factorial : k)⁻¹` multiplying `(f ^ j.val) v`.
  Primality need not be assumed separately: positive characteristic of a field is prime.
- There is no simplicity, irreducibility, cyclicity, or nonzero-coefficient hypothesis.
  Uniqueness is over the lists satisfying all stated properties; polynomial evaluation
  at k[T],T already uniquely fixes that list, so adjoining its factorial consequences
  does not change what the unique list means.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, extending the
  commutative-ring and division-ring structures.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, with its polynomial-splitting/root equivalence.
  The node only needs the algebraically closed predicate, not a choice of closure.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  `Mathlib.CategoryTheory.Monoidal.Grp`; its group multiplication/unit/inverse diagrams
  are those already used by `specialGroup`.
- `def-sc-general-linear-group`: `Sheaf.AlgebraicGeometry.LinearGroupSchemes`,
  `Index`, `SpecialAlgebra`, `specialLinear`, `specialGroup`, `specialPoints`.
  Read the determinant quotient, structure-map specifications and uniquely pinned natural
  matrix-point equivalence. The latter includes zero and nonreduced test algebras.
- `def-sfb-hopf-action-module-data`: `Sheaf.RingTheory.HopfActionModuleData`,
  specifically `HopfAction.Coassociative` and `HopfAction.Counital`. These are the exact
  right-comodule laws used in the inline subtype; no theorem about a representation/
  comodule bijection is used.
- `def-sfb-affine-coordinate-hopf-algebra`: `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`,
  specifically the canonical `HopfAction.coordinateHopfAlgebra` instance on
  `Γ(SL2, ⊤)`. This supplies the coefficient Hopf algebra in those two predicates.
- Additional Mathlib APIs read: `Matrix.SpecialLinearGroup.transvection`,
  `AlgebraicGeometry.Spec.mapMulEquiv`, `DualNumber` and `DualNumber.eps`, and the
  canonical coordinate-Hopf instances from `HopfCoactionLinearization`.

Edge cases checked before drafting:

- m=0 uses `Fin 1`, w_0=v, factorial 0!=1 and f^0=id; no positive-weight condition was
  silently introduced. The lower orbit must be constant by the same big-cell argument.
- The zero module cannot have the required nonzero v, as the node stipulates.
- Characteristic 0 is allowed in the main theorem. Characteristic 2 is allowed too;
  the six-transvection diagonal identity uses only the unit inverse law and signs.
- m≥p still has the orbit coefficients and factorial identities, even though j! can
  vanish; division is confined to the conclusion under m<p. Frobenius twists explain
  why a characteristic-zero Lie algebra theorem cannot replace this statement.
- a=0, nonunits, nilpotent a and the zero test algebra are included. The latter has
  a subsingleton tensor target, so all identities are well-typed and hold there.
- The upper-end coefficients may be zero; uniqueness does not force exact degree m.
  Every coefficient remains detectable by the universal algebra k[T].

Searches (2026-10-24):

- `msearch.py ... leanfinder "A highest weight vector in a rational SL2 module has lower
  unipotent polynomial orbit of degree at most its weight with factorial coefficients"`:
  eight hits, headed by `IsSl2Triple.HasPrimitiveVectorWith.exists_nat` and
  `pow_toEnd_f_eq_zero_of_eq_nat`. Read their signatures in Mathlib/Algebra/Lie/Sl2.lean:
  they require CharZero and are Lie-module results, not this arbitrary-characteristic
  rational group-scheme statement. Other hits concern weight chains.
- `msearch.py ... loogle "SpecialLinearGroup, Representation"`: zero hits.
- `msearch.py ... grep "Comodule|SL2|SpecialLinearGroup" RepresentationTheory`: zero hits.
- `msearch.py ... leansearch "rational representations of SL2 highest weight vector
  unipotent orbit polynomial factorial coefficients"`: eight hits concerning binomial
  factorial identities, multinomials, polynomial coefficients, Hilbert polynomials,
  hypergeometric series and Hermite polynomials; none state the requested orbit theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Comodule, SL2, SpecialLinearGroup,
  rational representation and highest-orbit terms found the existing special-linear and
  Hopf coaction framework above, and no theorem matching the item. Searching the exact
  item id in WeilConjectures found no attachment. Searching the final declaration names in
  both trees and Mathlib found no clash. The DAG search found the existing owners above;
  no new definition node is warranted.

Repair validation: scompile.py compiled the actual module in sandbox and library forms
cleanly (51.3 s and 9.3 s respectively). No errors or warnings remained. The returned H2
is repaired by replacing the theorem dependency with the two definition dependencies and
rendering the coaction subtype inline. No source library was edited. No statement fault or
STATEMENT-DISPUTED remains.

## Second reading by Q34

Self-reread against the original node and the complete file: the binders retain the
algebraically closed field in arbitrary characteristic, actual finite-dimensional M, the inline coordinate coaction subtype with both Hopf laws,
nonnegative m, nonzero v, both universal highest-vector identities and the full dual-number
differential identity. The conclusion retains uniqueness, every
coefficient including j=0 and j=m, the all-algebra orbit, constant coefficient, factorial
powers, and conditional invertibility and exponential formula. I checked the order of
the six root matrices defining the diagonal by direct multiplication and checked that
`act` evaluates c itself, so the hypotheses cannot refer to an unrelated representation.
No claim of an independent review is made; the maintainer's reviewer supplies that.
