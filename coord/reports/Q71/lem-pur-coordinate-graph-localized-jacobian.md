## Worker report

Q71 states `Algebra.coordinateGraph_localized_jacobian` in
`Sheaf.RingTheory.CoordinateGraphLocalizedJacobian`. Its proof is `sorry`, as required
for stage 2. Every other declaration is an explicit construction or abbreviation
for an object already specified by this node; no definition obtains data from a
postponed theorem. No node statement or dependency list changes.

Sources read: Stacks `algebra.tex`, `lemma-standard-smooth` (00T7), including (2)
and its proof by the leading projection of the naive cotangent complex;
`morphisms.tex`, `lemma-etale-at-point` (02GU), particularly (8); and the current
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-regular-immersion-linearization.proof.md`,
second paragraph, where the prescribed differentials give the coordinate map.
The graph, Schur and inverse-determinant calculations are the item's explicit
seven-step expansion of that source argument.

Hypotheses and fixed objects, clause by clause:

- Field `k`: `{k : Type u} [Field k]`. The explicitly bound naturals are
  `{r d : ℕ}`. The ordered index set `Fin r ⊕ Fin d` has size `n=r+d` and is
  identified with `Fin (r+d)` by `finSumFinEquiv`. Its left and right parts are
  exactly the first `r` and last `d` coordinates. This changes only indexing.
- `P=k[y_1,...,y_n]`: `MvPolynomial (Fin r ⊕ Fin d) k`. The binder `F` gives the
  `r` specified relations. `CoordinateGraphAlgebra F` is literally the quotient
  `P ⧸ Ideal.span (Set.range F)`, not an unspecified isomorphic algebra.
- Images `a_b`: `coordinateGraphImage F (MvPolynomial.X b)`, where
  `coordinateGraphImage` is Mathlib's `Ideal.Quotient.mkₐ`.
- This particular presentation is standard smooth: `hstandard` is `IsUnit` of
  the quotient image of the leading `r` by `r` determinant. In this block the
  rows of `coordinateGraphJacobian F H` come only from `F`, so this hypothesis
  does not depend on `H`. This is the data-level condition of the recorded
  standard-smooth definition; imposing only an abstract `IsStandardSmooth`
  instance would not assert that this specified leading minor is invertible.
- Prime `q` and its residue field: `(q : Ideal (CoordinateGraphAlgebra F))`
  and `[q.IsPrime]`, with `q.ResidueField` throughout. No rationality or
  closed-point condition is added.
- The polynomials `H_j` are the binder `H`. Their images are
  `coordinateGraphImage F (H j)`. The vector `dh_j ⊗ 1` is
  `coordinateGraphFibreDifferential F q (H j)`.
- `hind` states linear independence over `q.ResidueField`; `hspan` states
  that the span of the same range is top. Together they assert exactly the
  assumed basis, with no auxiliary chosen basis as a hypothesis.
- Module base change uses the dependency's canonical tensor order
  `q.ResidueField ⊗[A] KaehlerDifferential k A`. Thus `dh_j ⊗ 1` in the node
  is `1 ⊗ dh_j` here, under Mathlib's canonical `TensorProduct.comm`.
- `R=k[T_1,...,T_d]`: `MvPolynomial (Fin d) k`.
  `coordinateGraphLocalizedAlgebra F H` constructs its specified action on
  the localization by evaluating each `T_j` at `h_j/1`. The instance binder
  `[aR : Algebra R (CoordinateGraphLocalization F H)]` together with
  `haR : aR = coordinateGraphLocalizedAlgebra F H` names exactly that action.
  This is structure bookkeeping, not an additional hypothesis: the displayed
  construction always supplies the instance and `haR` is reflexivity when
  it is installed. Equality prevents an arbitrary alternative action.
- `J`: `coordinateGraphJacobian F H`, with derivative rows `F` followed by
  `H`. Since the `T_j` are coefficients over `R`, differentiating `H_j-T_j`
  in a `y` direction is exactly differentiating `H_j`. Entries are in `P`.
- `Delta`: `coordinateGraphDelta F H = J.det`; `delta` is its quotient
  image under `coordinateGraphImage F`.

Conclusion clauses, in their Lean conjunction order:

1. `coordinateGraphImage F (coordinateGraphDelta F H) ∉ q` is `delta ∉ q`.
2. `IsUnit (coordinateGraphResidueJacobian F H q).toBlocks₁₁` asserts
   invertibility of the reduced leading block `Bbar` as a square matrix.
3. The existential `b : Module.Basis (Fin d) K (K ⊗[A] Ω[A/k])`, together
   with its first equality, is precisely the complementary coordinate basis
   `da_{r+1},...,da_n` in the fibre. The equality for every `j i` of
   `b.repr (coordinateGraphFibreDifferential F q (H j)) i` with
   `coordinateGraphSchur F H q j i` says its coefficient rows are exactly
   `S=Ebar-Dbar*Bbar⁻¹*Cbar`. The definition of `coordinateGraphSchur` uses
   `toBlocks₂₂`, `toBlocks₂₁`, `toBlocks₁₁⁻¹`, `toBlocks₁₂` in that order.
4. `IsUnit (coordinateGraphSchur F H q)` asserts invertibility of `S`.
5. The next equality is literally `det Jbar = det Bbar * det S`.
6. The following inequality states `det Jbar ≠ 0`.
7. The existential square presentation uses the recorded upstream
   `Algebra.SquareJacobianPresentation` with index `(Fin r ⊕ Fin d) ⊕ Unit`.
   Its generator values and relations are required to equal the specified
   `coordinateGraphLocalizedValues` and `coordinateGraphRelations`.
   Thus the conclusion is about the displayed presentation, not mere
   existence of some square presentation.
8. The existential `e` is the explicitly displayed quotient isomorphism of
   `R`-algebras. Its source is literally the polynomial ring over `R` modulo
   the span of the specified graph equations, and its generator equality
   sends each `y_b` to `a_b/1` and the last variable to `delta^{-1}`.
   `R`-linearity also specifies the coefficient map. The generator formulas
   determine this isomorphism, so it agrees with the preceding presentation.
9. `coordinateGraphAugmentedDeterminant F H =
   coordinateGraphLift (coordinateGraphDelta F H) ^ 2` computes the actual
   Jacobian of those `n+1` relations in those `n+1` variables over `R`.
10. Evaluating that determinant at `coordinateGraphLocalizedValues` is
    explicitly asserted to give the localization image of `delta`, squared.
11. The final `IsUnit` says that same image `delta^2` is a unit.

The construction helpers belong to the particular objects fixed by this lemma;
they do not introduce another general definition of polynomial algebra, tensor
base change, standard smoothness, differential, localization or square presentation.
All helpers and the theorem are listed in `lean.declarations`.

Dependency declarations used (including their supplying modules):

- `Field`: `Mathlib.Algebra.Field.Defs`.
- `MvPolynomial`, `MvPolynomial.algHom_ext`:
  `Mathlib.Algebra.MvPolynomial.Basic`; evaluation `MvPolynomial.aeval` and
  `MvPolynomial.eval₂Hom`: `Mathlib.Algebra.MvPolynomial.Eval`.
- The recorded `Algebra.IsStandardSmooth` in
  `Mathlib.RingTheory.Smooth.StandardSmooth` and `Algebra.SubmersivePresentation`
  in `Mathlib.RingTheory.Extension.Presentation.Submersive` fix the standard
  smooth presentation convention. The explicit `F`, quotient, ordered
  inclusion and `hstandard` render its specified presentation data; no second
  standard-smooth predicate is defined.
- `Localization.AtPrime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`;
  `Ideal.ResidueField`: `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
- `KaehlerDifferential`, `KaehlerDifferential.D` and its universal-property
  interface `KaehlerDifferential.linearMapEquivDerivation`:
  `Mathlib.RingTheory.Kaehler.Basic`.
- `TensorProduct`, `TensorProduct.tmul`, and the left scalar extension used by
  `LinearMap.baseChange`: `Mathlib.LinearAlgebra.TensorProduct.Tower` and its
  imported tensor-product definitions.
- `Matrix`: `Mathlib.LinearAlgebra.Matrix.Defs`; the four block restrictions
  are `Mathlib.Data.Matrix.Block`; matrix inverse is supplied by
  `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
- `MvPolynomial.pderiv`: `Mathlib.Algebra.MvPolynomial.PDeriv`.
- `Matrix.det`, including its empty convention:
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
- `Localization.Away`: `Mathlib.GroupTheory.MonoidLocalization.Away`, with
  its ring instance and canonical inverse `IsLocalization.Away.invSelf` from
  `Mathlib.RingTheory.Localization.Away.Basic`.
- `Algebra.SquareJacobianPresentation`:
  `WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`.
- `Ideal.Quotient.mkₐ` and the quotient algebra structure:
  `Mathlib.RingTheory.Ideal.Quotient.Operations`.

The module publicly imports the modules exposing the signature and explicit
constructions; their public import closure supplies the dependencies above.
Proof-only imports are `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`
(`Algebra.SubmersivePresentation.basisKaehler`),
`Mathlib.RingTheory.Kaehler.Polynomial`
(`KaehlerDifferential.mvPolynomialBasis`), and
`Mathlib.LinearAlgebra.Matrix.Adjugate` (`Matrix.adjugate_mul`,
`Matrix.mul_adjugate`, the Cramer identities). The determinant multiplication,
block-triangular determinant and localization universal-property modules are
already public statement imports or in their public closure. Full signatures
and relevant docstrings of the recorded dependencies were read in the pinned
source tree. No dependency module is needed.

Edge cases checked mathematically before writing and on rereading:

- `r=0`: the leading block is empty, its determinant is one and its unique
  inverse is the empty identity. The Schur matrix is the full `H` Jacobian.
- `d=0`: both differential bases and the Schur matrix are empty; `det S=1`.
  The coefficient algebra is the zero-variable polynomial ring over `k`.
- `r=d=0`: `A=k`, the graph determinant is one, and the augmented quotient
  is `k[t]/(t-1)` with derivative and determinant one.
- A zero quotient has no prime ideal, so no artificial nontriviality
  hypothesis on `A` is needed. Arbitrary residue field extensions are allowed.
- In characteristic `p`, `H=y^p` fails the required basis at every prime for
  a one-variable polynomial algebra, whereas `H=y+y^p` has derivative one.
  No characteristic-zero or separability assumption has been inserted.
- For `F=y_1`, `H=y_2^2`, `r=d=1` and a prime with `2*y_2` nonzero, the
  Schur matrix and determinant are `2*y_2`; the augmentation determinant is
  its square. This checks the Schur sign and the inverse-determinant factor.

Searches actually run:

- `msearch.py ... leanfinder` with query
  `A prescribed residue field basis of differentials of a standard smooth algebra makes its graph Jacobian nonzero and adjoining inverse determinant gives a square Jacobian presentation`:
  eight hits, including `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential`,
  `Algebra.SubmersivePresentation.isStandardSmooth`, `jacobianRelations_spec`,
  `jacobianOfHasCoeffs`, `Algebra.PreSubmersivePresentation.jacobian`, and
  inverse-Jacobian relations. None states the prescribed residue-field,
  Schur-matrix and augmented-equation conclusion together.
- `msearch.py ... loogle` with query
  `Algebra.PreSubmersivePresentation.localizationAway_jacobian, Matrix.det_fromBlocks₁₁`:
  zero hits for that combined query.
- `msearch.py ... grep` with expression
  `localizationAway_jacobian|of_basis_kaehlerDifferential|det_fromBlocks`
  in `RingTheory`: nine hits in `Smooth/StandardSmoothOfFree.lean`,
  `Extension/Cotangent/Free.lean`, and `Extension/Presentation/Submersive.lean`.
  They cover individual ingredients, not this statement.
- `msearch.py ... leansearch` with query
  `standard smooth algebra residue field differential basis graph Jacobian determinant localization inverse determinant square presentation`:
  eight hits including `basisDeriv`, `jacobian`, `localizationAway_jacobian`,
  `jacobian_isUnit`, `Smooth.exists_span_eq_top_isStandardSmooth`, and
  `invJacobianOfHasCoeffs`. None is the complete statement.
- `rg` of `graph.*[Jj]acobian|coordinateGraph|localized.*[Jj]acobian|[Jj]acobian.*graph`
  in both `lean/WeilConjectures` and `lean/Sheaf` located related conormal and
  smooth-fibre Jacobian modules; their statements were opened and are different.
  The former gives a localized left inverse and ideal membership; the latter
  gives a minor avoiding a prime. Neither prescribes `H`, its Schur matrix, or
  the graph quotient and squared determinant.
- `rg -n 'lem-pur-coordinate-graph-localized-jacobian' lean/WeilConjectures`:
  no existing declaration for this node.
- `rg` of `CoordinateGraphAlgebra|coordinateGraphLocalizedAlgebra|coordinateGraph_localized_jacobian`
  in Mathlib and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q71 lem-pur-coordinate-graph-localized-jacobian <module>`
compiled both the module-mode sandbox probe (4.3 seconds) and the intended
library module (5.1 seconds) without errors or warnings. The main theorem is
the only postponed proof. No statement dispute or source correction was found.

## Second reading by Q71

The dispatcher explicitly forbids starting other agents and assigns the independent
review to the maintainer. This section records the worker's second pass, not a claim
that a separate worker reviewed the delivery.

I reopened the whole node and the final module together. The fixed quotient really
is `P/(F)`; the leading block uses `F` only; derivative rows, rather than columns,
match the stated Schur convention; the fibre uses the dependency's commuted tensor
order; the complementary basis is asserted rather than assumed. The graph equations
subtract `C (X j)`, so `T_j` is a coefficient and is not accidentally differentiated.
The coefficient action is constructed by evaluation and is fixed by `haR`, rather
than replaced by an arbitrary action. The isomorphism is separately present with
all generator formulas, and the square presentation fixes the same generators and
relations. Both the polynomial determinant-square identity and its evaluated unit
image are explicit. The empty index cases remain admitted by every binder.

During the implementation pass, the compiler required the explicit noncomputable
markers for polynomial quotient/evaluation data, an explicit target for `invSelf`,
and an instance-reducible marker on the constructed algebra structure. The final
statement names that structure through the instance binder and its equality, so all
square-presentation and algebra-equivalence projections elaborate under precisely
the specified action. These changes corrected elaboration only; no mathematical
hypothesis or conclusion was changed. Independent review remains the maintainer's
normal delivery review.
