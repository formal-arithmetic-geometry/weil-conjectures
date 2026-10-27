## Worker report

The module `Sheaf.AlgebraicGeometry.FixedPointHomogeneousCotangentLifts` states
`AlgebraicGeometry.exists_homogeneous_cotangent_basis`, with one `sorry` and two canonical real-data helpers: evaluation at the point and
restriction of scalars on the cotangent quotient. The node is unchanged except for its `lean` attachment.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The affine F-scheme is `Z : Over (Spec (.of F))` with `[IsAffine Z.left]`.
  The structure map is `Z.hom`; its finite-type hypothesis is precisely
  `[LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]`.
- The specified G_m is `StandardGroupSchemes.multiplicative F`, with the recorded
  Laurent Hopf group law. The F-morphism giving the action is
  `act : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z` in the over category.
  `hidentity` is the unit-action diagram; `hassoc` is the associativity diagram,
  with the canonical associator between the two parenthesizations.
- The rational point is `z : 𝟙_ (Over (Spec (.of F))) ⟶ Z`. The tensor unit is
  Spec F over itself. `hfixed` equates its orbit map with the constant map z,
  so fixedness is scheme-theoretic. Over an algebraically closed field, this
  agrees with fixedness of the rational point under all F-valued units:
  F is infinite, and Laurent coefficients are detected by such evaluations.
- The ring A is literally the global-section ring `Γ(Z.left, ⊤)`, inferred as
  the domain of `z.left.appTop`. The evaluation A → F is the composite
  `(Scheme.ΓSpecIso (.of F)).hom.hom.comp z.left.appTop.hom`, using the canonical
  identification of global sections on Spec F with F. Thus `a i` belongs to
  exactly the specified kernel, not a stalk maximal ideal or an arbitrary ideal.
- `d : ℕ` gives the nonnegative integer, and `Fin d` indexes the lifts and weights.
  Each `a i` is an element of that kernel, and `n i : ℤ` is an integer weight.
- `b : Module.Basis (Fin d) F (...).Cotangent` is an F-basis of m/m², and
  the first conjunct identifies each basis vector with the class of its lift.
  Mathlib's `Ideal.Cotangent` is m modulo m times m, not A modulo m²;
  `Ideal.toCotangent_eq_zero` identifies its kernel exactly with m².
  The scalar action is supplied explicitly by `cotangentLiftModule Z z`, using
  Mathlib's `Module.compHom` and the actual structure ring map
  `((Scheme.ΓSpecIso (.of F)).inv ≫ Z.hom.appTop).hom`. It is therefore the
  canonical F-action, without a second choice of algebra structure.
- The last clause is `act.left.appTop (a i).val = ... * ...` in the global-section
  ring of G_m ×_F Z. The first factor is pullback along the first projection of
  the Laurent monomial `LaurentPolynomial.T (n i)`, viewed as a global section
  via `Scheme.ΓSpecIso.inv`. The second factor is pullback of a_i along the
  second projection. This is precisely a_i(tu) = t^(n_i)a_i(u).
  Being a global-section equality, it remains true on every R-point for every
  commutative F-algebra R, in any universe: pull back the equality and use the
  canonical Γ(Spec R) ≅ R. No restriction to F-points or reduced R is made.
- There is no smoothness, connectedness, reducedness or characteristic assumption.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (the match for def-weil-algebraic-closure
  expressly includes this predicate).
- `AlgebraicGeometry.Scheme` and `Scheme.Hom`, Mathlib.AlgebraicGeometry.Scheme;
  `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `StandardGroupSchemes.multiplicative` and its `multiplicativeGroup` instance,
  Sheaf.AlgebraicGeometry.StandardGroupSchemes; `MonObj.one`, `MonObj.mul`,
  and the existing Cartesian monoidal structure on schemes over Spec F.
- `Module.Basis`, Mathlib.LinearAlgebra.Basis.Defs, supplied through the recorded
  Mathlib.LinearAlgebra.FreeModule.Basic module; `Ideal.Cotangent` and
  `Ideal.toCotangent`, Mathlib.RingTheory.Ideal.Cotangent; `RingHom.ker`, the
  existing ideal operations and quotient machinery from the quotient-algebra leaf.
- Proof-only imports: Sheaf.RingTheory.FiniteSubcomodule
  (`Coalgebra.exists_finiteDimensional_subcomodule`) and
  Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis
  (`GmRepresentation.weightDecomposition_and_basis`). Their full signatures and
  docstrings were read. The affine-Spec, tensor-product, Laurent-polynomial,
  affine-product and locally-finite-type Mathlib leaves are already available
  through the statement imports. The theorem docstring gives all six proof steps.

Sources checked: Milne Algebraic Groups (2017), Lemma 13.36 and the proof on
printed pp.267--268, and its following multiplicative-type remark. Smoothness
there is needed for the additional étaleness conclusion, not the invariant
complement used here. Also read the current latest blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), locating the
inherited supporting chain. No statement correction is necessary.

Edge cases checked mathematically before writing:

- Z = Spec F: m/m² = 0, d = 0 and the empty basis satisfy the conclusion.
- Trivial action: weights zero give the identity with T^0 = 1.
- A¹ with negative weight: integer Laurent monomials retain negative weights.
- Spec F[x,y]/(xy) with weights 1 and -1: singularity is allowed; x,y lift the
  cotangent basis. Smoothness has not accidentally entered the signature.
- Spec F[ε]/(ε²) with weight p in characteristic p: the weight is the character
  integer p, not its derivative. The formula works on nonreduced test algebras.
- The empty scheme has no F-rational point, so is correctly excluded by the
  point datum rather than by an unrelated nonemptiness hypothesis.
- Evaluation on the zero F-algebra is also valid: both sides are zero.

Searches actually run (2026-10-24):

- msearch LeanFinder: “At a fixed point of a multiplicative group action on an
  affine scheme of finite type there exists a basis of the cotangent space
  lifted to homogeneous regular functions”. Eight hits concerned presentation
  cotangent bases, including Algebra.Generators.exists_presentation_of_basis_cotangent
  and Algebra.SubmersivePresentation.basisCotangent; none states homogeneous
  fixed-point lifts for a scheme action.
- msearch Loogle: `Ideal.Cotangent, Module.Basis`: zero hits.
- msearch grep: `homogeneous.*cotangent|cotangent.*homogeneous|fixedPoint.*basis`:
  zero hits.
- msearch LeanSearch: “At a fixed point of a multiplicative group action homogeneous
  functions lift a basis of the cotangent space”. Eight hits on projectivization,
  actions on bases and fixed points of abstract group actions; no matching theorem.
- rg in both lean/WeilConjectures and lean/Sheaf for homogeneous cotangent lifts,
  G_m actions, Luna maps and fixed-point bases, plus the required node-id grep in
  WeilConjectures: no existing statement. The useful existing weight-basis and
  finite-subcomodule statements were imported for the proof plan.
- Read the Mathlib Ideal.Cotangent API and the canonical affine global-section
  algebra instance rather than introducing copies of either notion.

No STATEMENT-DISPUTED flag, node fault, new node, or dependency repair.

## Second reading by NO

This is the dispatch worker's own second reading, not a claim of independent
review; the dispatch brief forbids starting another agent and assigns independent
review to the maintainer. Reopened the node and the entire module and checked each
correspondence above. In particular, checked that hfixed has domain G_m (the orbit
map), that the action laws have domains Z and (G_m ⊗ G_m) ⊗ Z, that evaluation uses
ΓSpecIso.hom for evaluation and ΓSpecIso.inv for Laurent sections, and that the homogeneous identity uses T^n
rather than T^(-n). The basis is on the kernel's cotangent quotient, not on the
kernel itself or on A/m². The statement keeps all integer weights and d = 0.
The initial elaboration probe reached a heartbeat limit at an underspecified
`Ideal.toCotangent _`; the ideal was made explicit without altering the statement.

Further elaboration repair: the explicit evaluation helper exposed a reversed
ΓSpecIso direction, now corrected to `.hom` for Γ(Spec F) → F. The coordinate
section correctly retains `.inv` for F[t,t⁻¹] → Γ(G_m). The scalar structure is
explicitly `Module.compHom` along the structure ring map, so no typeclass search
has to guess the over-scheme or a field action. Both helpers have real data and
source/blueprint docstrings; neither postpones a property or introduces a new notion.

Validation: the final module compiled cleanly in both sandbox mode and its actual
library module path through `scompile.py`; no non-sorry warnings remained.
The only changed node key is `lean`; all original statement and proof text remains intact.
