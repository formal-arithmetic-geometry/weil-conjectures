## Worker report

The module `Sheaf.RingTheory.RelativeHopfCounitCriterion` states the two clauses of
`lem-sfb-relative-hopf-counit-criterion`, without changing the informal statement.
`RelativeHopf.relativeHopfCounitCriterion` is the only postponed theorem. Its proof is
`sorry`; its docstring gives all six steps of the node's proof. The helper
`counitMultiplication` is a real tensor lift, and `CounitCriterionConclusions` merely
expands the conclusions into a proposition. Both helpers belong to the item's own
canonical multiplication-map interface and are listed in `lean.declarations`.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; `[CommRing H] [Bialgebra k H]` supplies the
  commutative algebra, algebra-valued comultiplication and counit and their axioms.
  The explicit `(S : H →ₐ[k] H)`, `hSleft`, `hSright` are precisely the two antipode
  identities from the recorded dependency. This follows that dependency's encoding,
  without assuming cocommutativity or antipode stability of A.
- The unital subalgebra is `(A : Subalgebra k H)` and its right coideal condition is
  `hA : IsRightCoideal k H A`, using the recorded definition, not a copy.
- `augmentationIdeal k H A`, `Quotient k H A`, and `quotientMap k H A` are the
  dependency's actual ideal HA-plus, quotient H/HA-plus, and quotient map pi.
  The theorem existentially supplies only its coideal proof `hJ`, as the dependency
  does. The coalgebra is Mathlib's canonical quotient coalgebra. There is no extra
  coideal assumption in the theorem and no choice of unspecified coalgebra data.
- Every relative Hopf module is quantified as `X : Type w`, `[AddCommGroup X]`,
  `[Module H X]`, `[Module k X]`, `[IsScalarTower k H X]`, and
  `α : Coaction k H (Quotient k H A) X`. This uses the recorded left coassociative,
  counital coaction with its action compatibility.
- Restriction of the H-action to A is automatic via Mathlib's
  `Subalgebra.moduleLeft`; no independent A-action on X is introduced. This avoids
  an elaboration diamond encountered in an earlier draft with `[Module A X]`.
  The resulting scalar action is definitionally `a • x = (a : H) • x`.
- `∃ R : Submodule A X, (R : Set X) = coinvariants ... (quotientMap ... 1) α`
  identifies exactly R(X), including its A-module structure. This existential is
  harmless: equality of the carriers uniquely determines a submodule. It does not
  replace coinvariants by a larger span or introduce an arbitrary invariant submodule.
- `R.subtype` is j_X. `counitMultiplication k H A X R` is mu_X, defined as
  `TensorProduct.lift ((Algebra.lsmul A A X (A := H)).toLinearMap.compl₂ R.subtype)`.
  On a pure tensor it reduces to `h • (r : X)` by `TensorProduct.lift.tmul`.
- Clause (1) is the direct equivalence
  `Function.Injective (counitMultiplication ...) ↔
  Function.Injective (R.subtype.baseChange H)`. Mathlib's
  `LinearMap.baseChange_tmul` gives h tensor r maps to h tensor j_X(r).
  Neither flatness nor E occurs in this clause's premises.
- Clause (2) is nested under `∀ (E : H →ₗ[A] A), (∀ a : A, E (a : H) = a) → ...`.
  This is precisely the conditional assertion for an A-linear retraction; it does
  not ask for an algebra retraction or a coalgebra retraction.
- Its conclusion is `Function.Surjective (counitMultiplication ...)` together with
  `∀ x : X, ∃ (n : ℕ) (h : Fin n → H) (r : Fin n → R),
  x = ∑ i, h i • (r i : X)`. Thus every summand really has its second factor in
  R(X), and the finite-sum clause is retained explicitly. The index may be empty.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`,
  `Mathlib/Algebra/Field/Defs.lean:170–180`, including the docstring and signature.
- `lem-sfb-relative-hopf-module-kernels`:
  `Sheaf.RingTheory.RelativeHopfModuleKernels`,
  `RelativeHopf.relativeHopfModuleKernels` and `RelativeHopf.QuotientConclusions`.
  Its public dependency `Sheaf.RingTheory.RelativeHopfModuleData` supplies
  `RelativeHopf.IsRightCoideal`, `augmentationIdeal`, `Quotient`, `quotientMap`,
  `Coaction`, and `coinvariants`; all their signatures and docstrings were read.
- Proof dependency `lem-sfb-coideal-canonical-tensor-isomorphism`:
  `Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism`,
  `RelativeHopf.CanonicalTensorIsomorphism` and
  `RelativeHopf.coidealCanonicalTensorIsomorphism`, read in full.
- Proof dependency `lem-sfb-coideal-coinvariant-projection`:
  `Sheaf.RingTheory.CoidealCoinvariantProjection`,
  `RelativeHopf.CoinvariantProjectionConclusions` and
  `RelativeHopf.coidealCoinvariantProjection`, read in full.
- `def-weil-pbc-module-tensor-product`: its `mathlib_match` names `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift` and the tensor maps. Read the tensor
  definitions, lift signature and generator equation, and `LinearMap.baseChange`
  with `baseChange_tmul` in `Mathlib/LinearAlgebra/TensorProduct/Tower.lean:657–670`.
  These Mathlib modules are already publicly available through the statement dependency.

Source reading: Bichon, arXiv:2301.05480v2, sections 2.1, 2.2, and 2.4, especially
Proposition 2.7 and Lemma 2.6, read at https://arxiv.org/html/2301.05480v2.
The statement intentionally follows the node's retraction repair of the unproved
tensor-row exactness claim in the printed Proposition 2.7 proof. No correction of the
node is required. The latest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`
was also read; the supporting Hopf argument is located by the node's recorded chain,
not asserted to appear literally in that blueprint file.
WANTED: `literature/bichon-faithful-flatness_arXiv-2301.05480.pdf`, as already recorded
in the source metadata. The online v2 text was available and read.

Edge cases checked mathematically before finalizing the declaration:

- X = 0: both tensor maps are injections on the zero module, and the empty finite
  sum represents its unique element. No nontrivial-module hypothesis is imposed.
- A = H: C is k via epsilon, the coaction's counit identifies it with the trivial
  coaction, so R(X) = X; multiplication is H tensor_H X to X, the usual unitor.
- A = k: this is the ordinary Hopf-module situation; epsilon is a k-linear
  retraction. Both the criterion and the finite generation assertion agree with it.
- Arbitrary characteristic is retained; there is no separability, dimension or
  finite-generation premise. Universes u, v and w are independent and explicit.
- Without E, only the injectivity equivalence is asserted. Under E the finite-sum
  witnesses have arbitrary n, including n = 0. No flatness assumption has entered.

Searches actually performed (using the prescribed msearch.py wrapper):

- LeanFinder: “For a relative Hopf module the multiplication map from H tensor over
  A coinvariants is injective exactly when tensoring the inclusion is injective,
  and is surjective under an A-linear retraction”. Eight hits, including
  `Module.Invertible.rTensor_injective_iff`, `LinearMap.rTensor_injective_iff_subtype`,
  `Algebra.IsEpi.injective_lift_mul`, and `Submodule.injective_tensorToSpan`.
  None states the relative Hopf counit criterion: the invertible and epi hypotheses
  are absent here, and the subtype comparison alone lacks this multiplication map.
- Loogle: `"Hopf", "counit"`. Nine hits: antipode/counit Hopf identities and
  categorical Hopf-object equivalence components. None is this theorem.
- Mathlib grep: `relative.?Hopf|HopfModule|coideal|counit.*[Ss]urjective` in RingTheory.
  Seventeen hits on quotient coideals, `Bialgebra.counit_surjective`, and Witt-vector
  applications. None states the two clauses or defines this relative counit map.
- LeanSearch: “Relative Hopf module counit multiplication surjectivity under a
  coideal subalgebra retraction”. Eight hits on ordinary coalgebra/bialgebra counits
  and their categorical encodings, which are different maps.
- `rg -n 'relative.?Hopf|HopfModule|counitCriterion|counit_criterion'` on
  `lean/WeilConjectures` and `lean/Sheaf`: only the existing dependency modules.
- `grep -rn 'lem-sfb-relative-hopf-counit-criterion' lean/WeilConjectures`: no hits.
- `rg` for `relativeHopfCounit|relativeHopfCounitCriterion|counitMultiplication` in
  Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: no hits.
  The canonical multiplication helper is consequently new, built from the existing
  tensor lift and scalar action, rather than a duplicate of a named project notion.

Validation: every compiler invocation used the prescribed scompile.py wrapper.
Earlier compiler errors were repaired in the multiplication definition; an ensuing
style warning was repaired by splitting its signature. The final clean compilation
and delivery preflight results are recorded below after running the prescribed tools.

## Second reading by Q127

The dispatcher explicitly forbids starting other agents, so this is a second reading
by the same worker, not a claim of an independent worker review. The maintainer's
independent review follows delivery. I re-opened the informal node and the completed
module and checked the field, commutative Hopf structure, unital right coideal A,
canonical quotient C, relative coaction axioms, exact coinvariant equality, both
maps and the direction of the injectivity iff. I also checked that E is scoped only
inside the second clause, with E(a) = a, and that both surjectivity and finite-sum
expressions are present. The existential coideal proof is a proof supplied by the
same hypotheses as in the dependency, not an extra mathematical hypothesis.
The only implementation correction during this reading was to use Mathlib's actual
restricted A-action throughout, rather than binding a potentially distinct A-module
structure. There is no change to the node's mathematical statement, no new node,
and no dependency replacement. The source proof's tensor-kernel issue is handled
exactly by the six-step retraction argument retained in the theorem docstring.

Final validation: scompile.py completed the sandbox and library-path compiles cleanly,
with no errors or warnings (1.5 seconds each). The first `deliver2.py --no-push` dry
run printed `OK (dry run): commit b635cfa9a2e passes the preflight and compiles;
nothing pushed`. This final validation paragraph is the only subsequent report edit.
