## Worker report

The delivery states `lem-sfb-polynomial-translation-acyclic` in
`Sheaf.CategoryTheory.PolynomialTranslationAcyclic`. The main declaration is
`Profinite.CondensedAction.PolynomialTranslation.polynomial_translation_acyclic`.
Its proof is `sorry`; no theorem is proved. The three accompanying helpers are
`translatedMonomial`, `Model`, and `Assertion`, all recorded in `lean.declarations`
and documented against this same node. They express the formula, the presentation
of the module introduced by this node, and the node's vanishing assertion. No data
is selected from an existence theorem and no definition contains `sorry`.

Source read: the complete node statement and all five proof steps, and the current
main-20261015 blueprint file
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). That paragraph delegates the open-direct-image coefficient input; the
more specific polynomial analytic obligation and its noncomplete all-continuous
reference remain agent-formulated/WANTED, as the node already records. The theorem
docstring carries the node's five-step induction, including the finite-stage analytic
input, explicit difference contraction, and normalized derived composition.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(ell : ℕ) [Fact ell.Prime]` |
| Algebraic closure Omega of Q_ell | `(Ω : Type u) [IsAlgClosure ℚ_[ell] Ω]` with the displayed algebra structure |
| Extended norm topology | `[NormedField Ω] [NormedAlgebra ℚ_[ell] Ω]`; the induced norm/topology on each intermediate field is Mathlib's subtype norm/topology |
| Finite intermediate E | `(E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E]` |
| F is E or Omega | The conclusion is exactly `Assertion ell E r m ∧ Assertion ell Ω r m` |
| A(S)=C(S,F), all continuous maps | Existing `continuousScalarRing F`, which bundles the recorded `continuousMapRingObjOfUniverse F`, its canonical multiplication and commutativity; its section coefficients here are `ULift.{u + 1} C(S,F)` |
| r,m nonnegative integers | `(r m : ℕ)` with no positivity or nonemptiness restriction |
| L=Z_ell^r with inverse-limit topology | `Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))`; the function space has the finite product of Mathlib's ell-adic integer topology; the lift and multiplicative tag preserve it |
| Monomials in y_1,...,y_r,z_1,...,z_m | `(Fin r ⊕ Fin m) →₀ ℕ`; left variables are y and right variables are z |
| Internal direct sum of copies of A | `Model.ι` maps `Mod.regular (continuousScalarRing F).X` into `Model.object.module`, and `Model.isColimit : IsColimit (Cofan.mk object.module ι)` is the actual internal coproduct universal property |
| Internal A-linear L-action | `Model.object` has the dependency's existing `CondensedBar.Equivariant` type, definitionally `Profinite.CondensedAction.ActionModule`; its `act` is a sectionwise linear monoid homomorphism and its naturality quantifies over all profinite restrictions |
| g acts by f(y-g,z) | `translatedMonomial` applies `MvPolynomial.eval₂Hom` to `MvPolynomial.monomial d 1`; its left-variable image is `X (Sum.inl i) - C(g_i)`, and its right-variable image is `X (Sum.inr j)` |
| Varying g in C(S,L), coordinates included through Z_ell -> Q_ell -> F | `Model.translation` quantifies over every `S : Profinite.{u}` and `g : C(S,L)`; the continuous coefficient function is `fun s ↦ algebraMap ℚ_[ell] F ((g s).toAdd.down i : ℚ_[ell])` |
| Polynomial substitution extends internally | For every monomial d and coefficient section c, `Model.translation` equates the action on `ι d` applied to c with the finite sum over the support of `translatedMonomial`; each coefficient is multiplied by c and inserted by its coprojection. This determines the action on the coproduct after every base change, rather than only at global points |
| Ordinary internal modules | The module is the existing `CategoryTheory.Mod` on abelian sheaves, accessed through `CondensedBar.Modules`, not solid modules or discrete representations |
| Ordinary total right derived invariants | The expression uses the recorded `CategoryTheory.CondensedDerivedRestriction.derived`, defined as the ordinary `rightDerivedFunctor` of normalized internal invariants |
| T[0] | `(DerivedCategory.singleFunctor _ 0).obj T.object` |
| R^q Gamma is q-th cohomology of R Gamma | `DerivedCategory.homologyFunctor (CondensedBar.Modules (continuousScalarRing F)) q` applied to the preceding derived object |
| Vanishes as an internal A-module for every q>0 | `∀ q : ℤ, 0 < q → IsZero (...)`; the conclusion lives in the module category itself |
| Compatible universes containing the parameter sets | Explicit `universe u`, arbitrary `Ω : Type u`, all profinite objects in `Profinite.{u}`, coefficient groups in `AddCommGrpCat.{u+1}`, and the dependency's `DerivedCategory.{u+1}` localization. The group is lifted into u rather than restricting test objects to universe zero |
| Unbounded polynomial direct sum | All finite exponent vectors are indexed; there is no degree bound, completion, product, or finite-dimensional hypothesis on T |
| Noncomplete topology for Omega | There is no `CompleteSpace Ω` hypothesis and no completion; `continuousScalarRing Ω` uses all continuous functions, not `padicAlgClCondensedRing`, which only allows finite-subextension-valued functions |

`Assertion` includes `Nonempty (Model ...)` and the vanishing statement for every such
presentation. Existence is the construction implicit in “put T equal to the internal
direct sum and give it the specified action.” The presentation consists of the actual
coproduct universal property and the exact translation formula, so it is determined up
to the equality used here, namely equivariant isomorphism. The universal quantifier
ensures that vanishing cannot hold merely by selecting a convenient representation.
No additional mathematical assumption is made on the module.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`,
  `continuousMapRingObjOfUniverse`, `continuousMapRingObjOfUniverseMonObj`, and
  `isCommMonObj_continuousMapRingObjOfUniverse`, including their full construction
  and docstrings. The existing bundle is
  `Profinite.CondensedAction.continuousScalarRing` in
  `Sheaf.CategoryTheory.ContinuousScalarRing`. The already-landed node
  `def-sfb-bundled-continuous-scalar-ring` is added to `stmt_deps` under brief-stage2
  section 5's rule allowing landed definition dependencies. No new node is created.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.monomial`, `MvPolynomial.eval₂Hom`, `MvPolynomial.aeval`, and
  `MvPolynomial.algHom_ext`. The formula directly uses the existing polynomial ring
  and substitution; there is no replacement polynomial definition.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.Modules`, `sectionModule`, `ActionModule`,
  `Invariants`, and `ProductInvariants`, with their naturality, inclusion and
  normalized adjunction fields. `CondensedBar.Equivariant` reuses this very category.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`,
  and `Mod.regular`, the recorded ordinary internal-module notion.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` and its imported
  `CondensedDerivedInvariants`: `boundedBelowComputation`, `invariants`, and
  `derived`. The latter is the ordinary total derived functor used by the assertion.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and `.HomologySequence`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`, and
  `DerivedCategory.homologyFunctor`; degree zero uses `singleFunctor`.
- `def-weil-size-convention` has its recorded convention-only binding. Its explicit
  universe constraints are rendered directly, rather than invented as a Lean object.

The two already-stated proof-dependency modules are imported without `public`:
`Sheaf.CategoryTheory.CondensedProductActionInflation` and
`Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`.
Their recorded declarations and source signatures/docstrings were read.
`lem-sfb-ind-unipotent-procyclic-difference` had no Lean record in the inspected DAG,
so there is no recorded module to import; it remains explicitly identified in the
proof docstring, and is not an extra assumption of this statement.

Edge cases checked: r=0 gives the singleton finite product group and allows arbitrary
spectators, m=0 imposes no unnecessary spectator, and r=m=0 still has the constant
monomial (the index of monomials is not the empty type). q=0 is deliberately excluded
from vanishing; every positive integer degree is included. Empty profinite S has its
unique continuous coefficients and action parameter, and all displayed section formulas
remain meaningful. Degree-zero monomials and g=0 give the identity substitution.
Nonconstant profinite-valued g is expressly included. Noncomplete Omega is allowed.

Searches actually executed through `msearch.py NY lem-sfb-polynomial-translation-acyclic`:

- `leanfinder`: “Higher derived internal invariants vanish for polynomial functions
  with p adic lattice translation and norm topological coefficients”. Eight hits,
  primarily `PadicInt` Mahler/fwdDiff declarations and an unrelated elliptic-function
  declaration. These do not state internal derived acyclicity; several Mahler results
  require `CompleteSpace`, which this Omega case must not assume.
- `loogle`: `MvPolynomial, groupCohomology`. Zero hits.
- `grep`: `(polynomial|MvPolynomial).*(acyclic|invariant|cohomolog)|(acyclic|invariant|cohomolog).*(polynomial|MvPolynomial)`.
  Two Mathlib hits, `FieldTheory/Fixed.lean` and
  `RingTheory/MvPolynomial/Symmetric/Defs.lean`, concern invariant polynomials and
  do not state this result.
- Direct `rg` with the same pattern in `lean/WeilConjectures` and `lean/Sheaf`, and
  the required `grep -rn` for the node id in `lean/WeilConjectures`: no upstream
  declaration of the item. The project hit in `PolynomialDerivedBarComparison`
  is a reference to this item in its proof, not a statement of it. The additional
  search for `translation|PolynomialTranslation|polynomialTranslation` found only
  other actions and that proof reference. The existing scalar-ring bundle is reused.

No mathematical statement correction, unusable dependency repair, or independent new
notion was needed. The original mathematical statement and proof are unchanged.

## Second reading by NY

The dispatcher prohibits starting another agent and assigns independent review to the
maintainer. This section records the worker's separate source-versus-file rereading,
not an assertion that another worker reviewed it.

I reread the node beside the finished module. The left and right variable indices
separate the translated and spectator variables. The substitution uses subtraction,
not addition. Each action parameter is a continuous function on the entire test object,
and the underlying action record requires naturality for every base change. The finite
support sum multiplies the substituted monomial coefficient by the original coefficient
section, so it specifies the A-linear extension, including nonconstant coefficients.
The coproduct cocone uses one regular module per exponent vector with no degree bound.
The conclusion is `IsZero` in internal modules after actual total derived invariants and
cohomology, not vanishing of global points or ordinary continuous cochains. Both allowed
coefficient fields and r=m=0 remain present. There is no completeness assumption on Omega.
Existence is part of the assertion, so the presentation quantifier cannot be vacuous.

The first compile exposed namespace collisions with the parent `CondensedAction`'s
`Equivariant` predicate and `Modules` abbreviation. Those references were fully qualified
as `CategoryTheory.CondensedBar.Equivariant` and `.Modules`. A subsequent long-line
warning was repaired by wrapping the cohomology functor expression. These repairs do
not change the mathematics. The module uses only the owning node's helper declarations;
no copied dependency construction or additional axiom is introduced.
