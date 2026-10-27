## Worker report

The delivery states `Algebra.StandardCotangentBoundary.boundary_cokernel_equiv` in
`Sheaf.RingTheory.StandardCotangentBoundaryCokernel`. It uses the explicit polynomial rings,
Mathlib Kähler differentials, their actual tensor base changes, the basis-defined boundary,
and the actual quotient by its image. Every theorem has proof `sorry`. All definition data
are explicit; the proof obligations for the augmentation sections and face-difference
membership are named theorems belonging to this node's constructions.

Hypothesis and clause correspondence, with the node and module open:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary commutative ring map A → B | `A : Type u`, `B : Type v`, `[CommRing A]`, `[CommRing B]`, `[Algebra A B]`; the last is the usual encoding of the specified ring map. The universes are independent. |
| R = A[B], Q₁ = A[R], Q₂ = A[Q₁], and their variables | `MvPolynomial B A`, `MvPolynomial (MvPolynomial B A) A`, `MvPolynomial (MvPolynomial (MvPolynomial B A) A) A`, with `MvPolynomial.X` at each level. No finite index restriction. |
| ε is evaluation and I = ker ε | `epsilon A B = MvPolynomial.aeval id`; `augmentationIdeal A B = (Generators.self A B).toExtension.ker`. Mathlib's self generator augmentation is precisely `aeval id`. |
| d₀(Y_p) = p | `faceZero A B = MvPolynomial.aeval id`, with the polynomial index type R. |
| d₁(Y_p) = X_{ε(p)} | `faceOne A B = MvPolynomial.aeval (fun p ↦ MvPolynomial.X (epsilon A B p))`. |
| Common augmentation Q₁ → B | `generatorsOne.val = epsilon A B`; its polynomial evaluation sends Y_p to ε(p), which equals both ε ∘ d₀ and ε ∘ d₁ by `MvPolynomial.algHom_ext`. `faceDifference_mem` states the resulting difference belongs to I. |
| M₁ and M₂ are the augmented differential tensors | `ModuleOne` and `ModuleTwo` are `generatorsOne.toExtension.CotangentSpace` and `generatorsTwo.toExtension.CotangentSpace`. Mathlib defines this as `B ⊗[Qᵢ] Ω[Qᵢ/A]`; symmetry of tensor factors identifies this with the node's `Ω ⊗ B`. |
| Q₂ augmentation Z_f ↦ ε(d₀f) | `generatorsTwo.val f = epsilon A B (faceZero A B f)`. Explicit section b ↦ Z_{Y_{X_b}}; no arbitrary choice. |
| Second boundary on dZ_f ⊗ 1 | `boundary` is `generatorsTwo.cotangentSpaceBasis.constr B` of `differentialTensor 1 f - generatorsOne.cotangentSpaceBasis (faceZero f) + generatorsOne.cotangentSpaceBasis (faceOne f)`. The Mathlib basis lemma identifies each basis vector with `1 ⊗ dX`. Thus the formula defines the actual B-linear map on the full M₂, not an assumed map. |
| ρ is B-linear and sends df ⊗ b to b[d₀f-d₁f] | Binder `rho : ModuleOne A B →ₗ[B] (Generators.self A B).toExtension.Cotangent` and `rho_formula`, quantified over every polynomial f and every b. `differenceClass` is the actual `Extension.Cotangent.mk` of the face difference. |
| ρ∂₂ = 0 | `rho_boundary : rho.comp (boundary A B) = 0`. |
| E = M₁ / im ∂₂ | `Cokernel := ModuleOne A B ⧸ LinearMap.range (boundary A B)`. |
| t_p is the quotient of dY_p ⊗ 1 | `symbol p := (LinearMap.range boundary).mkQ (generatorsOne.cotangentSpaceBasis p)`. |
| The induced map is a B-linear isomorphism | `∃ e : Cokernel A B ≃ₗ[B] (Generators.self A B).toExtension.Cotangent` with `e.toLinearMap.comp ...mkQ = rho`. This pins e to the unique induced map, rather than asserting an unrelated equivalence. |
| Inverse [h] ↦ t_h-t₀ for every h ∈ I | `∀ h : augmentationIdeal A B, e.symm (Extension.Cotangent.mk h) = inverseRule A B h`; `inverseRule h = symbol h.val - symbol 0`. Every conormal class has such a representative. |
| Inverse rule additive | Explicit conjunct `∀ h k, inverseRule (h+k) = inverseRule h + inverseRule k`. |
| R-linear through ε | Explicit conjunct `∀ r h, inverseRule (r • h) = epsilon r • inverseRule h`. The left is multiplication of the ideal element by r, and the right is the B-action on E. |
| Annihilates I² | Explicit conjunct `∀ h : augmentationIdeal A B, h.val ∈ augmentationIdeal A B ^ 2 → inverseRule h = 0`. |
| No finiteness or regularity hypothesis | The complete binder list contains only rings, their algebra structure, and exactly the two assumptions on rho in the node. |

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`,
  `MvPolynomial.aeval`, `aeval_X`, and `aeval_unique`. Read their definitions/signatures
  and docstrings at Basic lines 78–83, 430–439 and Eval lines 587–625.
- `def-weil-pbc-kahler-differentials`: `Mathlib.RingTheory.Kaehler.Basic`,
  `KaehlerDifferential`, `KaehlerDifferential.D`, and
  `KaehlerDifferential.linearMapEquivDerivation`. Read their definitions and docstrings
  at lines 145–157, 196–210 and 323–334.
- Additional Mathlib APIs, not replacement notions: `Algebra.Generators.self` and
  `toExtension` (Extension/Generators.lean lines 167–182),
  `Algebra.Extension.Cotangent` and `Extension.Cotangent.mk`
  (Extension/Basic.lean lines 321–427), `Extension.CotangentSpace` and
  `Generators.cotangentSpaceBasis` with its tensor formula
  (Extension/Cotangent/Basic.lean lines 59–65 and 438–462),
  `KaehlerDifferential.mvPolynomialBasis` (Kaehler/Polynomial.lean lines 59–64),
  `Module.Basis.constr`, `LinearMap.range`, `Submodule.mkQ`.

The three direct public imports include both dependency modules; the extension-cotangent
import provides the polynomial differential basis and tensor-basis API. The statement
and proof dependency lists are the same two Mathlib nodes, so no extra project proof
imports are required.

Source read: `literature/stacks-project/cotangent.tex`, lines 1936–2017,
Tags 08RB and 08UP, including the explicit comparison and alternating face differential.
The six elementary proof steps in the DAG are reproduced individually in the main
statement's docstring. The section lemmas have evaluation proofs in their docstrings;
`faceDifference_mem` has the common-augmentation proof in its docstring.

Edge cases checked mathematically before writing:

- B the zero ring: both tensors and the conormal are zero; the formulas still type,
  and there is no `Nontrivial` assumption.
- A → A the identity: this still uses the large free polynomial resolution, without
  replacing the augmentation ideal by zero.
- h = 0: `symbol 0 - symbol 0` is zero; the index zero is the zero polynomial of R,
  not the separate variable `X (0 : B)`.
- k = -h and characteristic 2: the sum calculation uses subtraction identities,
  without division by 2 or any assumption on characteristic.
- r ∈ I: the scalar formula has ε(r) = 0 and yields the vanishing on products
  used to descend through I².
- Infinite underlying sets and u ≠ v: the polynomial rings and tensors are in
  `Type (max u v)` as needed, with no finiteness or universe equality restriction.

Searches actually run (via the prescribed `msearch.py`, except direct source searches):

1. LeanFinder, `cokernel of second standard simplicial polynomial differential boundary is
   conormal module ideal modulo square`: eight hits, including normalized Moore complexes,
   `Algebra.PreSubmersivePresentation.cotangentComplexAux`, and
   `Algebra.Presentation.differentials.hom₁`; no specific boundary cokernel or inverse.
2. LeanSearch, `standard cotangent boundary cokernel ideal modulo square`: eight hits on
   `Ideal.cotangentIdeal`, its square, `Extension.Cotangent.ker_mk`, and related quotient
   lemmas. These give the conormal module, not the theorem.
3. Loogle, `Ideal.Cotangent, KaehlerDifferential.basisMvPolynomial`: zero hits, unknown
   second identifier. This was an incorrect guessed name, not evidence of no match.
4. Loogle, `Ideal.Cotangent`: twelve hits, supplying the existing conormal construction.
5. Loogle, `KaehlerDifferential.mvPolynomialBasis`: seven hits, supplying the existing
   polynomial differential basis and its generator identities, used in the construction.
6. Mathlib grep, `cokernel|cotangentEquiv|H1Cotangent`, subdirectory RingTheory/Extension:
   twenty-five returned hits on conormal equivalences and naive H₁. Read the cotangent
   and extension source; none is the specific alternating-boundary theorem.
7. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for standard cotangent/resolution,
   boundary-cokernel names, and the node id; rg of `dag/lean_names_upstream.json`.
   Existing standard-resolution and naive-comparison modules were inspected, especially
   `NaiveCotangentComparison.lean` and `PolynomialAugmentationCotangent.lean`.
   They do not supply this explicit polynomial-boundary cokernel statement.

No statement correction, node fault, or STATEMENT-DISPUTED issue was found.
The existing node is copied with only `lean` changed. No new node or dependency repair
is needed: all helpers specialize the constructions already introduced by this item.

Validation: prescribed `scompile.py` compiled the module in sandbox mode and at its
actual library path cleanly. Only stage-2 sorry proofs remain.

## Second reading by Q22

A separate second pass by this dispatcher worker reopened the node, the Mathlib
signatures and the complete module; no second agent was started, as the task forbids it.
The table above records the comparison hypothesis by hypothesis and clause by clause.

The checks focused on the common Q₁ augmentation, the Q₂ augmentation, all three boundary
signs, the canonical B-action on the actual conormal, and whether the equivalence really
is the descended rho. The generator equations give the required augmentations; the
boundary is constructed with the full M₂ basis; and `e.toLinearMap.comp mkQ = rho`
identifies the induced map. The universal quantification over ideal elements gives the
inverse on every class, and the final three conjuncts preserve each explicit inverse-rule
clause of the node. Tensor symmetry changes only the writing order of the factors.

The second pass replaced inline section proof terms in the two generator structures
with named section theorems, each proved by `sorry` and with its own complete evaluation
proof docstring. The resulting two standalone evaluation signatures needed explicit
`(R := A)` annotations, which were added after the server reported stuck coefficient
ring metavariables. All polynomial data, including both sections, remain explicit.
The node statement and dependencies are unchanged. No additional hypothesis or omitted
clause was found; the zero ring, characteristic 2 and independent universes remain covered.
