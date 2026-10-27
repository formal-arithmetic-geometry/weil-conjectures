## Worker report

The module `Sheaf.RingTheory.FlatFpPresentationNoetherianModel` states
`Algebra.exists_flat_fp_presentation_noetherian_model`, with a single `sorry` proof.
It retains the prescribed polynomial surjection, and introduces no definitions or new nodes.
The item differs from the repository node only in `lean`. No statement correction or
STATEMENT-DISPUTED flag is needed.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Commutative rings R and A, and R -> A | `{R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]` |
| Flat R -> A | `[Module.Flat R A]`, equivalent to `(algebraMap R A).Flat` by `RingHom.flat_algebraMap_iff` |
| Finitely presented R -> A | `[Algebra.FinitePresentation R A]` |
| n >= 0 and the prescribed polynomial map pi | `(n : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] A)` |
| Surjectivity of that map | `(hπ : Function.Surjective π)` |
| A subring R_0 contained in R, finitely generated over Z | `R₀ : Subalgebra ℤ R` and `R₀.FG`; `R₀.val` is the actual inclusion |
| A commutative R_0-algebra A_0 | Existentials `(A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀)` |
| A_0 flat and finitely presented over R_0 | `Module.Flat R₀ A₀ ∧ Algebra.FinitePresentation R₀ A₀` |
| R_0, P_0 and A_0 Noetherian | `IsNoetherianRing R₀ ∧ IsNoetherianRing (MvPolynomial (Fin n) R₀) ∧ IsNoetherianRing A₀` |
| Surjective polynomial presentation pi_0 with the SAME n | `π₀ : MvPolynomial (Fin n) R₀ →ₐ[R₀] A₀` and `Function.Surjective π₀` |
| R-algebra isomorphism A_0 tensor R -> A | `α : @AlgEquiv R (A₀ ⊗[R₀] R) A _ _ _ Algebra.TensorProduct.rightAlgebra _` |
| Compatibility with the prescribed pi | `∀ p r, α (π₀ p ⊗ₜ[R₀] r) = r • π (MvPolynomial.map R₀.val.toRingHom p)` |
| No extra flatness or injectivity assertions | There is no assumption that the coefficient inclusion is flat or that the map from A_0 to A is injective |

The last equation says exactly that alpha composed with pi_0 tensor 1 is pi under
the canonical polynomial scalar-extension comparison: p tensor r corresponds to
`r • MvPolynomial.map R₀.val.toRingHom p`. Pure tensors generate, so specifying this
on every p and r is equivalent to equality of the full maps. `rightAlgebra` is
Mathlib's actual R-algebra structure with r mapping to `1 ⊗ₜ r`, supplied explicitly
rather than through a local instance. R_0 as an integer subalgebra is equivalent to
a unital subring; its underlying integer algebra is canonical.

Universes u and v are independent and explicitly declared; `autoImplicit false`
is set. A_0 lives in Type u because it is a quotient of a finite polynomial ring
on the subtype R_0 of R. This does not restrict the size of A: the hypothesis
already makes A a quotient of the corresponding polynomial ring over R. There
are no quantified test objects in a smaller unrelated universe.

Dependency declarations used (source signatures and docstrings read locally):

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `RingHom.flat_algebraMap_iff`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat` and its injectivity interpretation.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `MvPolynomial.aeval` (the latter two describe
  the recorded polynomial universal property; no substitute is defined).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`,
  `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`; ideal products/powers use the existing ideal semiring.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, `TensorProduct.tmul`,
  `TensorProduct.mk`; `Mathlib.LinearAlgebra.TensorProduct.Basic`:
  `TensorProduct.lift`, `TensorProduct.ext'`;
  `Mathlib.RingTheory.TensorProduct.Basic`: `Algebra.TensorProduct.rightAlgebra`.

Every stated proof prerequisite is imported, with plain rather than public imports:
`Algebra.FinitePresentation.ker_fg_of_mvPolynomial` (FinitePresentation is already
public); `CommRingCat.isColimitFgSubalgebraCocone` in
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`;
`MvPolynomial.algebraTensorAlgEquiv` in `Mathlib.RingTheory.TensorProduct.MvPolynomial`;
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot` in
`Mathlib.RingTheory.TensorProduct.Quotient`;
`RingHom.exists_eventually_flat_of_colimit_flat` in
`WeilConjectures.RingTheory.ColimitFlatRingMap`; and
`Algebra.FiniteType.isNoetherianRing` in `Mathlib.RingTheory.FiniteType`.
The theorem docstring carries all six DAG proof steps and their node identifiers.
Source read: local Stacks algebra.tex, Tag 02JO (3), around lines 47331--47440,
and Tag 00FN, around lines 5991--6025.

Edge cases checked before writing and again against the final signature:

- n = 0 uses `Fin 0`; there is no positive-variable assumption. Surjectivity can
  describe the structure-map quotient in that case.
- The empty relation list remains available (the model can be a polynomial ring).
- A = 0 is allowed, with quotient relation 1 where needed; the comparison can be
  an isomorphism of zero rings. R = 0 is also allowed, and its subalgebra is zero.
- No characteristic or Nontrivial assumption is introduced.
- Non-flat coefficient inclusions such as Z -> Z[t]/(2t) are not excluded.
- The induced A_0 -> A is not required to be injective.

Searches made with `/home/ubuntu/weil-launcher-all/batch2/msearch.py NK
lem-sfb-flat-fp-presentation-noetherian-model`:

1. leanfinder query: "A flat finitely presented algebra with a prescribed polynomial
   surjection descends to a flat finitely presented algebra over a finitely generated
   integer subalgebra preserving the presentation". Eight hits, including
   `Algebra.Presentation.instFinitePresentationModelOfHasCoeffsOfFinite`,
   `Algebra.Smooth.exists_subalgebra_fg`,
   `Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg`,
   `Algebra.Presentation.exists_presentation_fin`, and finite-presentation permanence.
   No hit combines flat descent with retention of an arbitrary prescribed surjection.
2. loogle query: `Algebra.FinitePresentation, Subalgebra`. Zero hits.
3. grep query: `flat.*model|flat.*descen|exists_fg_subalgebra|ker_fg_of_mvPolynomial`.
   Twenty-five hits: flat descent, faithfully flat descent and kernel finite generation;
   no exact statement.
4. leansearch query: "Flat finitely presented algebra has a Noetherian model over a
   finitely generated subring preserving a given polynomial presentation". Eight hits:
   module finite presentation, `RingHom.FinitePresentation`, presentation existence,
   finite-presentation base change, `RingHom.Flat`, `AlgHom.FinitePresentation`.
   No exact statement.
5. `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id found no declaration.
   Concept searches for Noetherian models, flat models and `exists_fg_subalgebra`
   found existing local/fibre models and the abstract
   `RingHom.exists_flat_finitePresentation_model` in
   `WeilConjectures.RingTheory.FlatFinitePresentationModel` (read in full).
   Its conclusion does not retain the prescribed pi or use an actual subring, so
   cannot serve as an existing match. Search of `dag/lean_names_upstream.json` and
   both RingTheory trees found no `FlatFpPresentation`, `flat_fp_presentation`,
   or theorem matching `flat.*presentation.*model` beyond that abstract model.

Validation: scompile.py compiled this file in sandbox and library module modes
against the server's live build, with exit 0, no errors and no warnings (4.4 s and
3.1 s respectively). No other build command was run.

## Second reading by NK

Performed a separate in-thread rereading of the node and final Lean signature;
no additional agent was started, as the dispatch brief forbids other agents.
This is a self-review; the maintainer's independent review remains the independent
check. The table above was checked against the final file rather than inferred
from the declaration name. Checked the `@AlgEquiv` parameters against its actual
signature: the explicit penultimate argument is precisely the canonical right
R-algebra on A_0 tensor R, and the last is the given R-algebra on A. The pure-tensor
equation uses the actual coefficient inclusion R_0 -> R and the original pi, not
an independently chosen presentation. The order of Noetherian conjuncts covers
all three stated rings. The two independent input universes and Type u quotient
model include zero rings, n = 0 and the size of all finite-presentation quotients.
No mathematical mismatch or node correction was found; no extra nodes or
unusable-dependency repairs were needed. All theorem proofs remain `sorry`.
