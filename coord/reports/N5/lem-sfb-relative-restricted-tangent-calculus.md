## Worker report

The module `Sheaf.RingTheory.RelativeRestrictedTangentCalculus` states
`RelativeBialgebra.relative_restricted_tangent_calculus`. Its only theorem proof is
`sorry`. The two helper definitions have real data: `tangentFunctionals` is the
intersection of kernels of the augmentation-rule equations, and `contraction` is
the tensor-map composite followed by the right unitor. No statement was corrected.
No new node or dependency repair is needed. The landed definition node
`def-sfb-restricted-enveloping-algebra` is added to `stmt_deps` for its canonical
`LieAlgebra.restrictedJacobsonTerm`. The theorem node
`lem-sfb-associative-jacobson-identities` is only a proof dependency.

Read the item and all ten proof steps, both original statement dependencies, all
three further proof dependencies, and the full source signatures/docstrings of
their recorded declarations. Read Milne, *Algebraic Groups* (2017), printed
pp.195--196 (PDF pp.207--208), and printed p.223 (PDF p.235). The arbitrary
commutative-base bialgebra generality is explicitly agent-supplied in this node;
it does not add field, flatness, smoothness, finite-type, or cocommutativity
conditions on the base or coordinate algebra. Read the current `latest` blueprint
unit `_section.md` and direct-images proof (3); this is the inherited supporting
input below that unit, not the unit's own statement.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Field `k` of prime characteristic `p > 0` | `(k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]`; prime implies positive. |
| Any commutative `k`-algebra `R` | `(R : Type v) [CommRing R] [Algebra k R]`; no `Nontrivial R` instance. |
| Commutative unital `R`-bialgebra `C` with both counit and coassociativity identities | `(C : Type w) [CommRing C] [Bialgebra R C]`; Mathlib's class extends `Algebra R C` and `Coalgebra R C`, and requires the two structure maps to preserve products and units. |
| `L_C` consists of augmentation-rule linear functionals | `tangentFunctionals R C (Bialgebra.counitAlgHom R C)` is an actual `Submodule R (C →ₗ[R] R)`. Its definition intersects kernels of `eval (xy) - ε(x) eval y - ε(y) eval x`; the first conjunct states precisely `a (x*y) = ε(x)*a y + a x*ε(y)`. Commutativity of `R` puts the last product in the node's order. |
| `I = ker ε`, restriction is an `R`-linear isomorphism to `Hom_R(I/I²,R)` | The second conjunct supplies `e : L_C ≃ₗ[R] Module.Dual R (RingHom.ker ...).Cotangent`. `Ideal.Cotangent` is Mathlib's quotient of `I` by `I·I`. Its evaluation equation `e a (I.toCotangent x) = a.1 x.1` requires restriction, rather than an arbitrary isomorphism. |
| Invariant derivations and their exact equation | The third conjunct supplies `M : Submodule R (Derivation R C C)` with membership equivalent to `comul.comp D.toLinearMap = (TensorProduct.map id D.toLinearMap).comp comul`. `Derivation` imposes the ordinary `R`-linear product rule. |
| Contraction and counit composition are inverse `R`-linear bijections | `e : L_C ≃ₗ[R] M`, with `(e a).1.toLinearMap = contraction R C a.1` and `(e.symm D).1 = counit.comp D.1.toLinearMap`. `contraction` is `(TensorProduct.rid R C) ∘ (id ⊗ a) ∘ comul`. The equations specify both maps of the equivalence. |
| Convolution `a*b` and `D_(a*b) = D_a D_b` for arbitrary functionals | Mathlib's `WithConv (C →ₗ[R] R)` has exactly the tensor-contraction convolution product (`LinearMap.convMul_def`). The fourth conjunct quantifies over all `a b : C →ₗ[R] R`, not only tangent ones; multiplication in `Module.End R C` is composition in the stated order. |
| Closure under commutator and convolution pth power | The fifth conjunct supplies `B : L_C →ₗ[R] L_C →ₗ[R] L_C` and `P : L_C → L_C`. Their equations identify their underlying functionals with the convolution commutator and `WithConv.toConv a.1 ^ p`. Their codomains assert closure without additional closure hypotheses. |
| `D_(v^[p]) = D_v^p` | The second equation accompanying `P` is `contraction R C (P a).1 = contraction R C a.1 ^ p`. |
| `R`-bilinear, alternating bracket and Jacobi | The type of `B` imposes bilinearity with the existing `R`-module structure. `B a a = 0` and `B a (B b c) + B b (B c a) + B c (B a b) = 0` impose exactly alternation and Jacobi. |
| Restricted scalar and adjoint identities | `P (r • a) = r ^ p • P a` for every `r : R`; `B (P a) b = Nat.iterate (B a) p b` for every `b` is the pointwise equality of adjoint endomorphisms. |
| Restricted sum and coefficient normalization | `toConv (P (a+b)).1 = toConv (P a).1 + toConv (P b).1 + ∑ i ∈ Finset.Ico 1 p, LieAlgebra.restrictedJacobsonTerm k p (toConv a.1) (toConv b.1) i`. The imported definition uses the finite recursion `LieAlgebra.jacobsonAdjointCoefficients` for the coefficient and multiplies the coefficient of degree `i-1` in `ad(ta+b)^(p-1)(a)` by `(i:k)⁻¹`. Convolution-polynomial coefficients are the coefficientwise images of those in `L_C ⊗_R R[t]`: bracket closure and scalar closure keep every iterated-bracket coefficient in `L_C`. Thus this states exactly the specified normalization, using the already canonical helper rather than a new correction-term definition. |
| Bialgebra-map functoriality | For every `C' : Type w'` with `[CommRing C'] [Bialgebra R C']` and `f : C →ₐc[R] C'`, the existential `T : L_C' →ₗ[R] L_C` is required to be `a.1.comp f` on underlying functionals. The following two equations identify `B (T a) (T b)` and `P (T a)` with precomposition of the source convolution commutator and pth power, respectively. This states preservation without composing derivations on different algebras. |
| Correspondence with augmented dual-number algebra maps | The final conjunct supplies `E : L_C ≃ {g : C →ₐ[R] DualNumber R // fstHom.comp g = counitAlgHom}` and requires `(E a).1 c = inl (ε c) + inr (a.1 c)`. This is exactly `ε(c) + ε_dual a(c)` in Mathlib's split square-zero algebra. Equivalence asserts that every augmented lift is obtained uniquely. |
| Naturality in augmented algebra maps | Quantification over any commutative `R`-algebra `A`, augmentation `ε : A →ₐ[R] R`, and algebra map `f : A →ₐ[R] C` satisfying `counit.comp f = ε` requires linear precomposition `T`, with no coalgebra condition. The last equation identifies `E(a) ∘ f` with `ε + ε_dual T(a)`. This is the naturality square in its canonical pointwise formula; uniqueness of the second coefficient determines the correspondence on `A`. |
| Affine-group interpretation | The augmented algebra maps in the final conjunct are exactly the coordinate description of `Spec(DualNumber R) → Spec(C)` over `Spec(R)` reducing to the identity section. This is the node's definition of relative tangent vectors (proof step 10). Invariance and both operations have already been identified by the preceding clauses. This last sentence is an interpretation of the same maps, not an extra smoothness or representability assertion. |

Dependency declarations used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, line 180;
  `[CharP k p]` and `[Fact p.Prime]` express this node's extra characteristic condition.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`,
  `TensorProduct.map`, `LinearMap.rTensor`, `LinearMap.rTensorHom`, in the
  recorded `Defs`, `Basic`, and `Map` modules. Read their signatures and docstrings;
  the construction uses the canonical tensor map and unitor directly.
- `lem-sfb-associative-jacobson-identities`:
  `Sheaf.Algebra.Lie.AssociativeJacobsonIdentities`,
  `Algebra.associative_jacobson_identities`; this remains a plain proof import.
- `def-sfb-restricted-enveloping-algebra`:
  `Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra`,
  `LieAlgebra.restrictedJacobsonTerm` and its coefficient recursion
  `LieAlgebra.jacobsonAdjointCoefficients`. This is a public import.
  Their complete source signatures and docstrings were read, together with the
  definition node. The recursion gives the formal coefficients of the iterated
  adjoint, with the exact node normalization. The statement explicitly supplies
  `LieRing.ofAssociativeRing` for the convolution ring;
  `LieAlgebra.ofAssociativeAlgebra` and `LinearMap.convAlgebra` supply its Lie
  algebra over `k`, with the convolution commutator bracket. No local instance
  or second definition of the correction terms is introduced.
- `lem-sfb-commuting-binomial-expansion`: `Commute.add_pow`,
  `Mathlib.Data.Nat.Choose.Sum`, line 34; plain proof import.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `productMap`, `productMap_apply_tmul`, and `ext` in
  `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`. Their full source
  signatures and docstrings were read. `.Maps` is a plain proof import.

Other canonical APIs used: `Bialgebra`, `counitAlgHom`, `Coalgebra.comul`,
`BialgHom`, `Derivation`, `Ideal.Cotangent`, `Ideal.toCotangent`, `DualNumber`,
`TrivSqZeroExt.inl`, `.inr`, and `.fstHom`. None is redefined.

Edge cases checked mathematically before writing:

- `R = 0`: allowed; all module and dual-number spaces collapse, and every displayed
  formula remains meaningful. No exact-characteristic or nontriviality condition on `R`.
- `C = R` with its self-bialgebra: the augmentation ideal and tangent submodule are
  zero; the only augmented dual-number lift has zero second coefficient.
- `p = 2`: the interval `Ico 1 2` contains `1`; alternation is stated as `B a a = 0`,
  rather than inferred from skew-symmetry, and the argument for `a(1)=0` is subtraction.
- Additive group: primitive-coordinate contraction is ordinary differentiation and
  its pth iterate vanishes on polynomials in characteristic `p`.
- Multiplicative group: the invariant operator `t d/dt` has pth iterate itself,
  consistent with the toral restricted operation; no additive-group specialization.
- Noncocommutative coordinate coproduct: the convolution order is unchanged;
  contraction of `a*b` gives first `D_b`, then `D_a`, by coassociativity.
- No finite-dimensional, flat, projective, reduced, smooth, or antipode assumption
  is needed. All four universes are explicitly declared. All variables are bound
  with `set_option autoImplicit false`.

Searches actually run through the prescribed `msearch.py` wrapper (recorded in
`searches.jsonl`, 2026-10-24):

1. LeanFinder: `Augmentation derivations of a commutative bialgebra over a commutative ring identify with invariant derivations and form a restricted Lie algebra under convolution powers`.
   Eight hits, headed by `LieRinehartAlgebra.instLieRinehartRingDerivation`,
   `LieRinehartAlgebra.instDerivation`, and `Derivation.instLieAlgebra`; these
   ordinary derivation Lie structures do not state the relative tangent calculus.
2. Loogle: `"counit", "derivation"`. Zero hits.
3. Grep: `(invariant|counit|augmentation).*[Dd]erivation|[Dd]erivation.*(invariant|counit|augmentation)`.
   Seven hits, all smooth-manifold left-invariant derivation documentation in
   `Geometry/Manifold/Algebra/LeftInvariantDerivation.lean` and `GroupLieAlgebra.lean`;
   no relative algebraic statement.
4. LeanSearch: `Augmentation derivations of a bialgebra identify with the dual of the augmentation ideal modulo its square and with invariant derivations`.
   Eight hits: `ModuleCat.Derivation`, `Derivation.instAddMonoidHomClass`,
   `Derivation.mk`, `Bialgebra.toCoalgebra`, `Derivation.instLieRingModule`,
   `ModuleCat.Derivation.mk`, and the two Lie-Rinehart instances; no exact match.
5. Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for augmentation/invariant
   derivations, restricted tangents, dual numbers, and the item id; direct `rg` of
   `dag/lean_names_upstream.json`, both project trees and Mathlib for the new
   namespace and theorem name. No name collision or complete existing statement.
   The field-only module `Sheaf.RingTheory.BialgebraDistributionTangentCalculus`
   was found and read in full. Its definitions and theorem require `[Field k]`
   on the bialgebra base, so they cannot express this node's arbitrary ring `R`,
   including the zero ring, and it has no restricted pth operation. Its general
   Mathlib constructions are reused; the two relative helpers are the owning
   node's missing general-base interfaces, not private copies of usable interfaces.
   `WeilConjectures.AlgebraicGeometry.TangentSpace` was read to distinguish the
   existing tangent-sheaf construction from this coordinate-module calculation.

The existing example module `CompactObject.lean` is now a withdrawn module with
no declarations. Its node records the identical upstream declaration
`CategoryTheory.IsCompactObject` in
`WeilConjectures.CategoryTheory.CompactObject`; that module's signature and
docstring were also read. The delivered file follows current module mode and docstrings.

Initial `scompile.py N5 lem-sfb-relative-restricted-tangent-calculus <module>`
passed both the sandbox and library-mode compiles with no errors or warnings.
The final dry run recompiles the final file and validates its record. There are
no node faults and no `STATEMENT-DISPUTED` flag.

## Second reading by N5

The dispatcher assignment explicitly prohibits starting another agent and assigns
independent review to the maintainer. This section records this worker's second
reading, not a claim that an independent group reader ran.

Reopened the node and the complete generated module. Checked the arbitrary ring
base and independent universes, the literal augmentation product rule, the
restriction evaluation equation (rather than bare existence of some linear
isomorphism), and both formulas of the invariant-derivation equivalence. Checked
that the convolution composition formula quantifies over all functionals; `B`
is bilinear on the inherited module, not an independently chosen module; `P`
is exactly convolution power; and the scalar formula quantifies over `R`.
Checked the Jacobi signs, `Ico 1 p` coefficient range, the central-polynomial
normalization of the imported correction term, the direction `C → C'` versus
`L_C' → L_C`, and the naturality domain of arbitrary augmented algebra maps.
The final affine-group sentence is the coordinate interpretation of the precise
augmented lift subtype, with invariant operations specified earlier, and does
not introduce a new group or tangent construction.

The maintainer's return identified one dependency mismatch in the original
delivery: a theorem node was added to `stmt_deps` solely for its helper
definition. The repaired file now uses the canonical coefficient definition
from `def-sfb-restricted-enveloping-algebra` as described below. Added the module's main-declarations
list. Every helper has its source and owning blueprint id; the single theorem
contains the complete ten-step proof plan and has `sorry` as its entire proof.


## Returned delivery repair

H2, returned immutable head `62a9e5cf889b`: removed
`lem-sfb-associative-jacobson-identities` from `stmt_deps`; kept it in the
unchanged `proof_deps`, and changed its module to a plain proof import. Adopted
the reviewer's preferred correction: publicly import
`Sheaf.Algebra.Lie.RestrictedEnvelopingAlgebra`, cite its landed definition node
`def-sfb-restricted-enveloping-algebra`, and use
`LieAlgebra.restrictedJacobsonTerm k p` on the two convolution functionals.
The explicit `@` form supplies `LieRing.ofAssociativeRing` without a forbidden
file-local instance. The Lie-algebra instance uses the existing convolution
`Algebra k` structure.

Read the canonical definition node and its entire module, and Mathlib
`Algebra.Lie.OfAssociative`: the associative Lie bracket is `xy-yx`; the
coefficient recursion expands `[tx+y,q]` into `[x,q_(i-1)] + [y,q_i]`,
so the normalization still gives exactly the item's `s_i`, including `p=2`
and the zero-base-ring case. The theorem's other clauses remain as independently
checked in the return.

Compared the retained sandbox with the returned source and the current shared
node: main still has only the two original statement dependencies and no Lean
record. Rebuilt the node copy from current main and applied only the Lean
record and the permitted landed-definition addition to `stmt_deps`. Refreshed
`lean.statement` verbatim from the repaired signature. No statement correction,
new node, or dependency-module repair is involved. The wrapper handles the
required current-base delivery bookkeeping; no direct Git mutation was run.
