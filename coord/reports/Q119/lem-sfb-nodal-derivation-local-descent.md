## Worker report

The module `Sheaf.RingTheory.NodalDerivationLocalDescent` states
`RingTheory.nodal_derivation_local_descent`, with its entire proof `sorry`.
The source read was Stacks Project `curves.tex`, Tag 0E68,
`lemma-nodal-vector-fields`, lines 6698–6745, together with
`more-algebra.tex`, Tag 07PE, `lemma-derivation-extends`, lines 11753–11804.
The local node deliberately uses completed rings to avoid treating the semilocal
normalization as the product of its two localizations. Its nine-step argument
is reproduced in the theorem docstring, including the two membership descents.
No statement correction or dependency repair is needed. The original node is
changed only in `lean`.

The module has three helper definitions owned by this same node and listed in
`lean.declarations`: `nodalAxes` evaluates a two-variable series at `(u,0)` and
`(0,v)` by its actual coefficients; `nodalAxisAction` is the explicitly displayed
pair of formal differential operators, using Mathlib's derivative; and
`branchPreservingDerivations` is the actual additive subgroup of derivations
preserving the two given ideals. Their data contains no `sorry`, no choice of
an unspecified object, and no additional postponed theorem. They merely name
expressions already in this node, rather than introducing independent notions.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| Local k-algebra A | `{A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A]` |
| Reduced and Noetherian | `[IsReduced A] [IsNoetherianRing A]` |
| m is the maximal ideal | `IsLocalRing.maximalIdeal A` everywhere |
| Residue field k as a k-algebra | `ρA : (A ⧸ IsLocalRing.maximalIdeal A) ≃ₐ[k] k` |
| Q(A) is total fractions | Mathlib `FractionRing A`, definitionally `Localization (nonZeroDivisors A)`; no domain assumption |
| B is its integral closure | `B : Subalgebra A (FractionRing A)` and `hB : B = integralClosure A (FractionRing A)` |
| B finite over A | `[Module.Finite A B]` |
| Exactly two distinct maximal ideals | `n₀`, `n₁`, `hn₀`, `hn₁`, `hne` and `hmax` |
| Both branch residue fields are k | `ρ₀ : (B ⧸ n₀) ≃ₐ[k] k` and `ρ₁ : (B ⧸ n₁) ≃ₐ[k] k` |
| Completed nodal presentation of A | `eA`, an equivalence with `MvPowerSeries (Fin 2) k ⧸ Ideal.span {X 0 * X 1}` |
| m-adic completion of B is P | `eB`, using the extended ideal `m.map (algebraMap A B)` |
| B tensor completed A is P | `eT : (B ⊗[A] AdicCompletion m A) ≃ₐ[k] (PowerSeries k × PowerSeries k)` |
| The completion and tensor identifications agree | `hBT` fixes their agreement on each `b : B`; the canonical finite-module completion comparison has this same value on B |
| Completed A inclusion is the two-axis map | `haxes` on every two-variable series representative, using `eA.symm` and `eT (1 ⊗ₜ[A] r)` |
| Branch residues are constant terms | `hρ₀` and `hρ₁` on every `b : B` |
| Derivations are k-linear Leibniz maps | Mathlib `Derivation k A A` and `Derivation k B B` |

The parameter `B` with its equality `hB` names precisely the integral closure,
not an arbitrary finite algebra. It avoids an abbreviation or a second
normalization construction. The existing project `NodalLocal.Normalization`
first reduces A and is not needed here: the node specifies the integral closure
of the already reduced A in its own total fraction ring. Residue fields are
written as the actual ideal quotients: the recorded `Scheme.residueField`
definition itself unfolds to `IsLocalRing.ResidueField` of a local ring, and
that definition unfolds to the same quotient. No distinct residue-field
construction or assumption is introduced.

Clause-by-clause correspondence:

| Node conclusion | Lean rendering |
| --- | --- |
| Every derivation extends preserving both ideals | `F : Derivation k A A ≃+ branchPreservingDerivations ... n₀ n₁`; first conjunct states its value on every `a : A` |
| Every extension has both residue composites zero | Second value conjunct, quantified over every D and every b, states both `ρᵢ (mk nᵢ ((F D).val b)) = 0` |
| Extension is unique among all B-derivations extending D | Conjunct quantified over `d : Derivation k B B`, with only its equality on A as hypothesis, gives `d = (F D).val` |
| Every branch-preserving derivation restricts to A | The explicit `F.symm` equation says `algebraMap A B (F.symm d a) = d.val (algebraMap A B a)` |
| Extension and restriction are inverse additive maps | The additive equivalence `F`, its inverse, and the two displayed restriction equations |
| Agree with extension to total fractions | `DQ`, its equation on every `b : B`, and its quotient rule on every `a` and regular denominator `s` |
| Localization compatibility wherever defined | For all submonoids S of A and T of B, `DS` and `DT` have the quotient formulas, and commute with every k-algebra map `ℓ` that extends the original inclusion |
| Completed extension is a pair `(uf∂u,vg∂v)` | Existence of `f g`, an actual derivation `δ` of the product, and `∀ p, δ p = nodalAxisAction f g p` |
| This is the completion of the B derivation | Equation involving `δ`, `eB`, and every `b : B` |
| It restricts to the completion of the A derivation | Existence of `δA`, its equation on every a, and the equation with `eT (1 ⊗ₜ[A] r)` for every completed r |
| It preserves the equal-constant subring | Explicit implication from equality of the constant coefficients of p to equality for `δ p` |
| The completed pair is continuous | Finite-coefficient criterion `∀ N, ∃ M, ...`; this is continuity for the product of the two power-series adic topologies, without imposing an unrelated topology on k |
| Formula for the formal derivative | Mathlib `PowerSeries.derivative k`; its `coeff_derivative` is coefficient n equal to `(n+1)` times coefficient `n+1` of the input |
| Completion detects q belonging to B | First final equivalence: q belongs to B iff `q ⊗ 1` lies in the image of `TensorProduct.map B.val.toLinearMap LinearMap.id` |
| Completion detects b belonging to A | Second final equivalence: `eT (b ⊗ 1)` belongs to the image of completed A iff b equals `algebraMap A B a` for some a |

Since F is onto the subgroup, its universally quantified completion,
localization and zero-residue assertions apply to every reverse input as well.
The quotient-rule statements uniquely determine the localization derivations,
so they also determine the same maps under successive localization. The
localization clause does not assume the existence of maps into total fractions
when the chosen denominators are zero divisors: its commuting equation is
quantified over exactly the maps ℓ that extend the inclusion.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the dependency's
  `AlgebraicClosure` and `IsAlgClosure` signatures were also read, but this node
  assumes algebraic closedness rather than choosing an algebraic closure.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange` and the
  tensor-product base-change construction; the statement uses the tensor
  product itself and the inclusion's `TensorProduct.map`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its ring/algebra structures and canonical `algebraMap`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `coeff`, `X`;
  the one-variable form is Mathlib `PowerSeries`, as the node's record permits.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` were read; the relevant affine local quotient
  is `IsLocalRing.ResidueField`, read in
  `Mathlib.RingTheory.LocalRing.ResidueField.Defs` and unfolded in the signature.
- `Mathlib.RingTheory.Localization.FractionRing`: `FractionRing`.
- `Mathlib.RingTheory.Derivation.Basic`: `Derivation`.
- `Mathlib.RingTheory.PowerSeries.Derivative`: `PowerSeries.derivative` and
  `PowerSeries.coeff_derivative`.
- Proof dependency `WeilConjectures.RingTheory.Derivation.CompletionAndLocalization`:
  `Derivation.exists_completion_and_unique_localization`; imported without public.
- Proof dependencies in `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`,
  `.LocalRing` and `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`: completion
  flatness/locality and `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `Module.FaithfullyFlat.tensorProduct_mk_injective`. The quotient-kernel
  declaration `AdicCompletion.pow_smul_top_eq_ker_eval` and flat exactness
  declarations `Module.Flat.lTensor_exact`, `Module.Flat.rTensor_exact` were
  read in their recorded source modules.

Edge cases checked before and after writing: arbitrary characteristic, including
2, uses no division by integers; the idempotent argument in the proof docstring
works in characteristic 2. The zero derivation is included. Constants are
k-linear constants, not an arbitrary field embedding into a completion. Reduced
A may have multiple components; no `IsDomain A`, product decomposition of B,
excellence, finite type, or characteristic-zero assumption is added. The two
branches are distinct and exhaustive, while a branch-preserving derivation need
not be zero. Continuity at N=0 is vacuous as required. A localization set may
contain zero, giving the zero ring and still satisfying the quotient formulas.
An impossible zero local k-algebra is already excluded by its stated residue
field identification. Universes u (k) and v (A) remain independent; there is no
quantification over test rings in a smaller independent universe.

Searches actually run through `msearch.py Q119 lem-sfb-nodal-derivation-local-descent`:

- Lean Finder: "Derivations of a nodal local ring extend uniquely to its
  normalization and descend when preserving both branches"; eight results,
  including `Scheme.Hom.normalizationDesc`, `normalization.hom_ext`, unramified
  localization statements and square-zero lifting; no match for the node.
- Loogle: `Derivation, AdicCompletion`; zero hits.
- Mathlib grep: `derivation.*(normaliz|integralClosure)|nodal|Derivation.*completion`;
  five Lagrange interpolation hits, no match.
- LeanSearch: "Derivations of a node correspond to derivations of its
  normalization preserving the two branch ideals"; eight results consisting
  of abstract derivation extensionality, additive structure and polynomial
  derivation extensionality, no nodal normalization statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for nodal derivation,
  equal-constant, normalization/derivation and candidate helper names, plus
  `grep -rn` of the item id in `lean/WeilConjectures`: no existing local
  extension/descent declaration. `MarkedNodalInfinitesimalFields` contains a
  sheaf/global correspondence and a prose use of this local argument, not this
  local theorem. `NodalLocalTangentData` defines normalization tangent and
  branch comparison objects, not the pair of differential operators or subgroup
  in this delivery. Mathlib derivation Basic/Lie searches found no ideal-stabilizing
  subgroup interface. DAG definition searches likewise found the scheme-level
  `def-sfb-curve-vector-fields-fixing-points`, not this local two-ideal subgroup.

Validation: scompile.py compiled the sandbox and the intended library module
cleanly, first in 4.5/4.4 seconds and then, after the explicit restriction
clause was added, in 4.9/4.7 seconds. All compiles use the prescribed wrapper.
The final import/options edits are checked again by the delivery dry run.

## Second reading by Q119

A separate final pass by this worker reread the node and the complete signature;
no additional agent was started, as the dispatch brief forbids that. Independent
review is performed by the maintainer after delivery. This pass checked the
hypothesis and conclusion tables above against the actual code. In particular,
it added the explicit equation for `F.symm`, checked that uniqueness quantifies
over all extensions rather than only stable ones, and checked that the two
membership assertions use the canonical tensor inclusion and the actual image
of A. It also checked that the continuity clause refers to both branch
coefficients, and that the quotient formula uses regular denominators in total
fractions but arbitrary submonoids for further localization. No mathematical
mismatch or disputed statement was found; no new node or dependency module is
part of this delivery.
