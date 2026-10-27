## Worker report

The module `Sheaf.RingTheory.HenselianParameterRootRegularity` states
`Algebra.henselian_parameter_root_regularity`, with its entire proof `sorry`.
The only helper, `Algebra.parameterRootCoordinate`, is real data: the quotient
class of `MvPolynomial.X i`. No object is chosen from an unproved existence theorem.
There are no additional postponed theorems.

The polynomial quotient is the existing `Algebra.pthRootAlgebra n r R a` of
`WeilConjectures.RingTheory.PthRootAlgebraLocal`, read at lines 26–32.
Despite the name, that definition has arbitrary natural exponent and arbitrary
commutative coefficient ring. Its prime and characteristic assumptions belong
only to the subsequent theorem `pthRootAlgebra_local`, which is NOT applied here.
The new definition node `def-sfb-parameter-root-algebra` is added to `stmt_deps`
to cite this existing declaration, as required by the H2 repair. The theorem node
`lem-weil-pbc-pth-root-algebra-local` is not a statement dependency. The definition
is exactly R[X_i]/span(range(X_i^n-C(a_i))). It also supplies the zero-parameter
presentation used for the closed fibre; no second root-algebra notion is defined.

The source was read in the supplied ILO PDF, PDF pages 139–140, printed pages
133–134, IX Proposition 2.1(i) and its proof. It gives the simultaneous root
presentation for a strict-local regular parameter tuple. As the node's
proof_origin explicitly explains, its extension to arbitrary positive exponents
and henselian bases is the detailed algebra argument, not an attribution of
arbitrary-n Kummer etaleness to ILO. The local sources read for that argument
include Stacks algebra.tex, definition-regular-local (00KU),
lemma-characterize-henselian (04GG), and lemma-finite-over-henselian (04GH).
There is no statement correction or mathematical dispute.

Hypothesis and clause correspondence (write B for the existing root quotient,
a=t ∘ Fin.castLE hr, x_i=parameterRootCoordinate a n i, and k=ResidueField R):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Commutative henselian local base | `R : Type u`, `[CommRing R]`, `[HenselianLocalRing R]`; the latter extends `IsLocalRing R`. |
| Noetherian regular local base | `[IsRegularLocalRing R]`, which extends both `IsLocalRing R` and `IsNoetherianRing R`. |
| Dimension d and the ordered full regular parameter system | `d : ℕ`, `t : Fin d → R`, `ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t)`; the recorded definition says span of the list is m and its length, hence d, equals `ringKrullDim R`. No separate dimension hypothesis is needed or lost. |
| 0 ≤ r ≤ d | `r : ℕ`, `hr : r ≤ d`; natural numbers include zero. |
| Arbitrary integer n ≥ 1 | `n : ℕ`, `hn : 0 < n`, which is precisely the same range of integers. |
| B=R[x_1,...,x_r]/(x_i^n-t_i) | `pthRootAlgebra n r R (t ∘ Fin.castLE hr)`; `Fin.castLE` selects exactly the first r entries. The coefficient algebra is the standard polynomial/quotient algebra. |
| Free basis of bounded monomials, unique expansions | `∃ b : Module.Basis (Fin r → Fin n) R B`, with `∀ a, b a = ∏ i, x_i ^ (a i).val`. A basis means exactly that each element has a unique finite linear expansion. This index is finite, so its finitely supported coefficient functions are all coefficient functions on the n^r bounded exponent vectors. |
| Finite coefficient algebra | `Module.Finite R B`. |
| Injective coefficient map | `Function.Injective (algebraMap R B)`. |
| Integral coefficient map | `Algebra.IsIntegral R B`. |
| B Noetherian, local and regular local | Existential `_hreg : IsRegularLocalRing B` supplies precisely the named class and its local/Noetherian superclass instances; these properties are conclusions, not extra hypotheses. |
| B henselian local | Existential `_hhen : HenselianLocalRing B`, also a conclusion. |
| Maximal ideal n=mB+(x_1,...,x_r) | Equality of `IsLocalRing.maximalIdeal B` with `(maximalIdeal R).map (algebraMap R B) ⊔ Ideal.span (Set.range x)`. Supremum of ideals is their sum. |
| n=(x_1,...,x_r,t_(r+1),...,t_d) and this is a regular parameter system | `IsRegularSystemOfParameters (List.ofFn x ++ ((List.ofFn t).drop r).map (algebraMap R B))`. The definition itself asserts exactly this second maximal-ideal equality as well as the dimension/length equality. |
| Closed fibre k[x_1,...,x_r]/(x_i^n) | An R-algebra equivalence from `B ⧸ (maximalIdeal R).map (algebraMap R B)` to `pthRootAlgebra n r k (fun _ ↦ 0)`. The following equality on each quotient root coordinate fixes the intended identification. R-algebra compatibility fixes the coefficient map, and R→k is surjective, so it fixes all k-coefficients. |
| Induced residue-field map is an isomorphism | `∃ e : ResidueField R ≃+* ResidueField B, ∀ a : R, e (residue R a) = residue B (algebraMap R B a)`. This specifies the canonical induced map, not an unrelated field isomorphism: the surjectivity of `residue R` determines e uniquely. |
| dim B=d | `ringKrullDim B = (d : WithBot ℕ∞)`. |
| B is a domain | `IsDomain B`, including nontriviality. |
| Strict henselian base gives strict henselian B | `IsStrictlyHenselianLocalRing R → IsStrictlyHenselianLocalRing B`. |
| No invertibility or roots of unity assumed | Neither is a hypothesis; n has only its positivity hypothesis. |
| r=0 gives B=R and basis 1 | `r = 0 → Function.Bijective (algebraMap R B)` identifies B canonically with R as an R-algebra. With empty `Fin r`, the index `Fin r → Fin n` has one member and the basis product is the empty product 1. The quotient is presented canonically rather than asserted to be definitionally the same carrier type. |

Every type and universe is bound explicitly (`universe u`, `set_option autoImplicit false`).
The existential class witnesses put local structures on B only after proving
that they exist. `IsRegularLocalRing` and `HenselianLocalRing` have Prop-valued
local-ring fields, so the two routes to that instance agree by proof irrelevance.
There are no statement-level lets, local notation, private definitions or local instances.

Dependency declarations read and reused:

- `def-weil-pbc-henselian-terminology`: Mathlib's `HenselianLocalRing` from
  `Mathlib.RingTheory.Henselian` and upstream `IsStrictlyHenselianLocalRing` from
  `WeilConjectures.Mathlib.RingTheory.Henselian`, lines 121–138. They have the node's
  henselian and separably-closed-residue-field meaning.
- `def-weil-regular-scheme`: its recorded
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is imported; its unchanged ring
  clauses are `IsRegularLocalRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`
  (class at line 51, with local and Noetherian superclasses). The scheme predicate
  itself is unnecessary to an assertion about local rings; no scheme is substituted.
- `def-weil-residue-field`: recorded module `Mathlib.AlgebraicGeometry.ResidueField`
  is imported. `Scheme.residueField` at line 45 is precisely the bundled
  `IsLocalRing.ResidueField` of the stalk, and `Scheme.Hom.residueFieldMap` at
  line 123 uses `IsLocalRing.ResidueField.map`. Here the same underlying local-ring
  quotient `IsLocalRing.ResidueField R` and its `residue` map are used directly
  (definitions read in `Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean:30–39`;
  induced map in `Basic.lean:96`). No residue-field definition is copied.
- `def-weil-pbc-regular-system-of-parameters`:
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters`, full definition read and used on both
  the input and the output lists, including the empty-list case.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`, `MvPolynomial.aeval`,
  `MvPolynomial.algHom_ext` in the recorded Basic/Eval modules, read at Basic:82,
  Basic:436, Eval:593–611. The quotient's actual polynomial construction is reused.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs:196` (the superclass used here).
- Added definition node `def-sfb-parameter-root-algebra`:
  `WeilConjectures.RingTheory.PthRootAlgebraLocal`, helper `Algebra.pthRootAlgebra`
  as explained above. Its subsequent characteristic-p locality theorem is not
  assumed or used.

The proof-only imports provide all stated proof dependencies:
`Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`, lines 633–652),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`),
`Mathlib.RingTheory.Noetherian.Basic` (`IsNoetherianRing.of_finite`),
`Mathlib.RingTheory.Ideal.GoingUp` (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`),
`WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
(`ringKrullDim_eq_of_isIntegral`),
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
(`IsRegularLocalRing.isDomain`), and
`WeilConjectures.RingTheory.FiniteLocalHenselian`
(`HenselianLocalRing.finite_local_henselian`). Their signatures/docstrings were read.
The statement's docstring contains each of the node's nine proof steps and its
named dependencies. No proof dependency is omitted for an import cycle.

Edge cases checked mathematically against the exact signatures:

- r=0: no variables or relations; coefficient algebra is R and the unique basis
  monomial is 1; the output list is the original list, and the closed fibre is k.
- d=0: hr forces r=0; the regular local base is a field and is not excluded.
- n=1: the quotient evaluates x_i to t_i; the basis index has one exponent
  vector, the basis is 1, and the output system recovers the input system.
- r=d: the dropped tail is empty; all d parameters are replaced by their roots.
- Residue characteristic divides n, or mixed characteristic: no etaleness,
  derivative-unit or separability-of-the-root-polynomial assertion is made.
- The zero ring cannot be a local base under Mathlib's nontrivial local-ring
  definition; this agrees with the node's local-ring convention. All allowed
  residue fields and coefficient universes are retained.

Searches actually run via the prescribed `msearch.py Q65 <item>` wrapper
(the exact results are also in sandbox `searches.jsonl`):

- LeanFinder: “Adjoining positive integer roots of a subset of regular parameters
  of a henselian regular local ring gives a finite free henselian regular local
  domain with the same residue field”. Eight hits including `HenselianLocalRing.TFAE`,
  `HenselianLocalRing`, and `PreTilt`; no theorem giving these simultaneous clauses.
- Loogle: `"IsRegularLocalRing", "MvPolynomial"`; zero hits.
- Mathlib grep:
  `(AdjoinRoot|MvPolynomial).*(IsRegularLocalRing|Henselian)|(IsRegularLocalRing|Henselian).*(AdjoinRoot|MvPolynomial)`;
  zero hits.
- LeanSearch: “Adjoining positive integer roots of regular parameters to a
  henselian regular local ring is finite free henselian regular local with
  unchanged residue field”. Eight hits: henselian criteria, `AdjoinRoot.of`,
  `IsAdjoinRoot.mkOfAdjoinEqTop`, `AdjoinRoot.isAdjoinRoot` and ring structures;
  no exact theorem.
- `rg` over the project's `lean/WeilConjectures` and `lean/Sheaf` for root algebra,
  parameter-root, and regularity names found `Algebra.pthRootAlgebra` and
  `AlgebraicGeometry.ProEtale.sncRootLevel`. Both present the same quotient;
  the former's smaller upstream module is reused. The latter lives in a chart
  module whose DAG depends on results downstream of this item, and is not imported.
  `RootAlgebraRegularAtRoot` only proves a one-variable localization theorem;
  `SNCFiniteRootRegularRing` imposes n invertible and gives global regularity only.
  Neither states this node. Exact node-id grep in `lean/WeilConjectures` was empty.
- Exact proposed names `henselian_parameter_root_regularity` and
  `parameterRootCoordinate` were absent in both library roots and
  `dag/lean_names_upstream.json`; no declaration is shadowed.

Validation: the prescribed server `scompile.py` compiled this file in sandbox
and library contexts (2.4 s and 2.5 s), with no errors or unexpected warnings.
Dry-run preflight and delivery are performed with `deliver2.py` after this report.

## New nodes

`def-sfb-parameter-root-algebra` records the existing upstream construction
`Algebra.pthRootAlgebra` in `WeilConjectures.RingTheory.PthRootAlgebraLocal`
(lines 27–32), with `existing: true`; no new Lean module or second definition
is introduced. Its only statement dependency is
`def-weil-pbc-mv-polynomial-ring`. The source is the simultaneous root presentation
in ILO IX Proposition 2.1(i), proof, printed p.133 (PDF page 139), read again
during this repair. The new node records only that algebraic construction,
for an arbitrary commutative ring A, natural exponent p, finite variable
number n, and coefficient family a; it asserts no locality theorem.
The signature has exactly these objects and assumptions, and the body is
`MvPolynomial (Fin n) A` modulo the span of the relations `X i ^ p - C (a i)`.
The canonical quotient algebra supplies the coefficient map. In particular,
exponent zero, zero rings, and the empty family are all well-defined; the
item itself retains the positive-exponent hypothesis of its own theorem.

Fresh prescribed searches: LeanSearch query “The quotient of a multivariate
polynomial ring by the relations X_i^p minus a_i over any commutative ring”
returned eight generic presentation/quotient results, none this named root
construction. Loogle query `"MvPolynomial", "Ideal.Quotient"` returned zero
hits. Mathlib grep `pthRootAlgebra|simultaneous.*root|adjoining.*roots`
returned six hits about AdjoinRoot and field extensions, no exact construction.
Their exact wrapper results are in this node's `mathlib_searches` and
`searches.jsonl`. The same project grep over `lean/WeilConjectures/RingTheory`
and `lean/Sheaf/RingTheory` found the existing upstream abbreviation and its
users, which are reused. `rg -l 'pthRootAlgebra' dag/nodes` found no definition
node; the locality node carries a theorem with additional prime, F_p-algebra
and local hypotheses. Blueprint searches for `pthRootAlgebra` and `root algebra`
each returned zero matching units. The ancestor command returned None,
matching the item's recorded ancestor; the new node retains its via path
with this item prepended. Thus this is a new DAG record for an existing Lean
definition, rather than a new implementation of the notion.

## Repair of H2

The saved packet first passed the required `deliver2.py --no-push` dry run
(commit e680e442765). That mechanical pass did not resolve the independent
return on immutable head 8070caf8b257. The returned dependency defect is
repaired by replacing `lem-weil-pbc-pth-root-algebra-local` in `stmt_deps`
with `def-sfb-parameter-root-algebra`, whose complete H12 record binds only
`Algebra.pthRootAlgebra` with the requested verbatim abbreviation signature.
The Lean source is byte-identical to the saved packet; every mathematical
clause and edge-case correspondence above remains applicable. Comparison
with the current read clone before repair showed only the packet's original
`lean` and `stmt_deps` fields differed. No statement, proof, proof dependency,
or other existing-node field is changed by this repair. The delivery wrapper
rebases the repaired packet onto the current live branch.

Repair validation: the prescribed `scompile.py` compiled the unchanged item
module successfully in sandbox and library contexts (1.9 s and 2.0 s).
The local self-check confirmed the new definition signature verbatim in the
upstream source, the requested single-declaration existing record, exactly
the original item dependencies plus the new definition node, only authorized
item fields changed, and the original theorem signature unchanged.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
