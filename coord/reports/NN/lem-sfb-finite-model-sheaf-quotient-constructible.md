## Worker report

This delivery states finite_model_sheaf_quotient_constructible, with a sorry proof,
in Sheaf.Paper.FiniteModelSheafQuotientConstructible.lean. Its concrete helpers belong
to this node and are listed in lean.declarations. The mathematical statement, proof and theorem signature are unchanged. stmt_deps
cites the already landed def-sfb-finite-constant-model-data, which owns modelFunctor.
The finite free scalar modules are written inline as ModuleCat.of (A l E)
(Fin a → ULift.{u + 1} (A l E)); no theorem conclusion is needed to state them.
No new node or dependency repair is needed.

Hypotheses and clauses, matched individually:

- Prime and finite extension: l, [Fact l.Prime], E, [Field E], [Algebra (Padic l) E],
  [FiniteDimensional (Padic l) E]. A and R alias coefficientExtensionIntegers and
  coefficientExtensionRing. The uniformizer is the chosen one defining the recorded
  coefficientExtensionIdeal; no arbitrary replacement of that ideal occurs.
- Induced topology: model and Encoding explicitly install
  (coefficientExtensionAbsoluteValue l E).toNormedField. DiscreteTopology uses exactly
  AdicCompletion.finiteTopology. No arbitrary topology on E is a hypothesis.
- Size and sites: Scheme.{u}, Scheme.ProEt.topology, abelian coefficients and module
  sections in u+1. ULift puts scalar coordinates in that universe without changing
  the coefficient ring. autoImplicit is false and all universes and binders are explicit.
- B_T: AdicCompletion.Modules over DerivedNakayama.integerRing, the pulled-back
  continuous integral ring. k_n: AdicCompletion.finiteRing over quotientRing. reduction
  applies the existing derivedReduction to singleFunctor at degree zero, so the result
  is in D(k_n), with the actual quotient coefficient action. It is not an object in a
  completed derived category. The contextual C_T and c_T notation is unused by this
  lemma's assertions; both existing completion modules are publicly imported.
- qcqs: [CompactSpace V] [QuasiSeparatedSpace V]. Constructible M: precisely the
  recorded IsConstantModelConstructible for the continuous integral ring. No geometric
  condition on l, Noetherianity, torsion-freeness, or completeness hypothesis is added.
- Every positive exponent: n : Nat denotes n+1, exactly the levels of the existing
  derivedReduction API. The existential hf asserts Finite R, followed by discreteness
  of its actual quotient topology. hf only installs the finiteness instance needed to
  state the ordinary constructibility predicate.
- Uniform vanishing: forall q : Int, q != -1 -> q != 0 -> IsZero H^q of reduction,
  with the same interval [-1,0] at every level.
- Internal bounded constructibility: exactly constantModelBoundedConstructible.
  OrdinaryConclusion uses boundedness and, in every degree, the recorded
  Scheme.IsConstructibleProEtaleFixedModuleSheaf predicate after Encoding.fixedDerived.
  Encoding is the dependency's normalized section-action equivalence: its ring map is
  fixed on constant scalars and its forward functors are prescribed. Its actual
  termwise derived extension is used, not an arbitrary derived equivalence.
- Chosen strata and covers: LocalCalculation quantifies every Scheme.Stratification S,
  every family C of proetale covers of its strata, every chart, every finitely presented
  scalar P and every model isomorphism eP. The cover/stratum composite is explicit.
  model reuses FiniteConstantModel.modelFunctor, the genuine discrete-constant scalar
  extension B tensor_A P, with the specified induced topology.
- Every exact scalar resolution: a,b : Nat, the original matrix v, augmentation w,
  injectivity, Function.Exact, and surjectivity. integralDifferential is the original
  v.mulVecLin conjugated by the coordinate ULift.moduleEquiv isomorphisms; it is not an
  arbitrary presentation map. Ranks zero are allowed.
- Specified two-term reduction: matrix sends each entry through Ideal.Quotient.mk
  of the actual recorded ideal. differential is that matrix's mulVecLin.
  scalarComplex is HomologicalComplex.double at -1 and 0; ordinaryComplex applies
  the constant-sheaf functor termwise. internalComplex uses the inverse normalized
  encoding on this exact complex. The local isomorphism therefore lives in D(k_n)
  and represents k_n^a -> k_n^b with precisely the reduced matrix.
- Ordinary cohomology: the next two local clauses identify H^-1 and H^0 with constant
  sheaves of the kernel and cokernel of that differential. Both scalar modules are
  asserted Finite and Module.FinitePresentation over the lifted quotient ring.
- Restriction and local comparison scope: LocalCalculation uses the derived pullback
  along each explicit cover/stratum composite and asserts Nonempty of the chart
  isomorphism. It gives an isomorphism class per chart, not a chosen family of
  comparisons satisfying a restriction compatibility equation. As explicitly permitted
  by the return, the unused restrictChartIso helper has been deleted; its mere
  existence did not state that equation. The natural-language node's compatibility
  sentence is therefore not encoded as an additional coherence assertion.

Dependency declarations used and read in their source modules:

- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and the publicly imported coefficient
  constructions, in particular coefficientExtensionIntegers/Ideal/Ring/Uniformizer.
- def-weil-size-convention: no declaration, as its lean.convention record explains;
  explicit universes and the existing small-site derived structures implement it.
- Sheaf.Paper.CondensedModuleDerivedPushpull:
  CondensedRing.moduleObjectDerivedPullback, with the imported
  CondensedRing.leftDerivedUpperStarComp and the ordinary derived functor interfaces.
- Sheaf.SixFunctors.ProEtale.DerivedCompletion:
  AdicCompletion.Modules, finiteRing, finiteTopology, quotient, derivedReduction;
  their public source gives the actual continuous quotient ring and coefficient map.
- Sheaf.Paper.CompletionTriangleComparison:
  CompletionTriangle.completion_triangle_comparison (contextual completion notation).
- Sheaf.Paper.CondensedConstantConstructibility:
  IsConstantModelConstructible, HasFiniteConstantLocalModel,
  constantModelBoundedConstructible, and their finite stratification definitions.
- Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence and its public Encoding module:
  FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence,
  Encoding, Encoding.fixedDerived, prescribed ring normalization and sectionEncoding.
- Sheaf.Paper.ProEtaleFixedModuleConstructible:
  Scheme.IsConstructibleProEtaleFixedModuleSheaf, using finite locally constant
  restrictions and finite geometric stalks on a finite constructible partition.
- Sheaf.Paper.FiniteConstantModelResolution:
  FiniteConstantModel.modelFunctor, owned by def-sfb-finite-constant-model-data; its
  source constructs actual scalar action, constant functions, extension of scalars,
  then inverse image from the point. The two-term resolution theorem is not a statement
  dependency and freeScalars is not referenced.

Proof dependencies are imported from their recorded modules, privately unless already
publicly needed by the signature. Mathlib leaf inputs use FreeModule.PID, Dimension.Free,
Sites.LocalProperties, ShortComplex.PreservesHomology and Valued.LocallyCompact.
The theorem docstring records all seven proof steps and their source nodes, including
flatness, specified scalar resolution, balanced reduction/pullback, finite kernel and
cokernel, cover descent, and finite open/closed refinement instead of Noetherian induction.
The only sorry is the theorem proof; all definitions have real data.

Edge cases checked: n=0 means exponent one, not exponent zero. a=b=0 and zero P work.
For P=A/(pi^r), r>=n+1, the reduced scalar differential can be zero, so H^-1 and H^0
can both be nonzero; there is no erroneous flatness or degree-zero concentration claim.
Empty schemes, empty strata/covers, non-Noetherian qcqs schemes, and characteristic l
are included. Cohomology towers are not asserted normalized. No statement dispute or
correction was found.

Searches actually run:

- msearch.py leanfinder, "Derived reduction of constructible integral proetale module
  sheaf modulo uniformizer power has finite constructible cohomology in degrees minus
  one and zero": eight hits about BDeRham, cotangent cohomology, etale loci and smoothness,
  no matching theorem.
- msearch.py loogle, "Module.FinitePresentation, DerivedCategory.homologyFunctor": zero hits.
- msearch.py grep in Mathlib CategoryTheory,
  "finite.*model.*quotient|constructible.*reduction|twoTerm": zero hits.
- msearch.py leansearch, "constructible module sheaf derived reduction finite quotient
  ring two term resolution": eight hits about SheafOfModules and finite presentation
  (including FGModuleRepr), no matching quotient theorem.
- rg of the item id in lean/WeilConjectures: no match. Concept searches for scalar
  matrices, twoTerm and constructible quotients in lean/WeilConjectures and lean/Sheaf
  found the existing constructions used above. TwoTermReductionCohomology concerns
  the specific multiplication-by-l rank-one example, not this arbitrary scalar
  resolution theorem. Mathlib Double, ToLin, ULift and Pi definitions were read.

scompile.py has compiled the entire module in both sandbox and library modes without
errors or warnings. No live source edit, direct git command, or global build was run.

## Second reading by NN

The explicit dispatcher brief forbids starting another agent; independent maintainer
review follows delivery. This section records a self reading, not an independent review.
Checking the node and full signatures caught missing induced topology when using the
Encoding methods outside the alias, and missing carrier coercions in the finite
kernel/cokernel clauses. Those were repaired and the full module recompiled. The returned review correctly found that the previously added restrictChartIso was
not referenced by the statement and did not assert compatibility. It has now been
deleted under the explicit alternative offered in that return; the chart isomorphism
class scope is stated above. The original modelFunctor is reused,
all positive levels occur, and no completeness or geometric hypothesis was introduced.


## Returned-delivery repair

The return names immutable head 04509ddc05f6. The retained packet was inspected before
editing and its initial deliver2.py --no-push completed successfully at 7e06f52dc1f,
with no push. The current read-clone item has no Lean record; comparison showed only
the retained lean and stmt_deps delta. Delivery wrappers refresh and rebase against
current server main; no direct git command was used.

1. H2/H13 dependency ownership: replaced
   lem-sfb-finite-constant-model-two-term-free-resolution in stmt_deps with the existing
   def-sfb-finite-constant-model-data. Read that definition node's full existing:true
   record and the modelFunctor source signature and docstring in
   Sheaf.Paper.FiniteConstantModelResolution. The same public module import supplies
   modelFunctor. Replaced every freeScalars reference by its literal ModuleCat.of
   expression, including both endpoints of integralDifferential and the augmentation
   domain. No new helper or node is needed. lean.statement and the theorem signature
   are byte-for-byte unchanged.
2. Restriction clause: took the return's explicit second option: removed the unused
   restrictChartIso declaration and its lean.declarations entry. LocalCalculation
   provides an isomorphism class on each chart; it does not supply a chosen compatible
   family of chart comparisons. Corrected the report and lean.note so neither claims
   that the removed helper states compatibility. No assertion of coherent restriction
   is silently inferred from Nonempty.

Self-check: all other local and global clauses remain identical to the returned packet,
whose mathematical checks the return accepted. The only Lean type changes expand a
definition to its exact body. The main signature is verified against lean.statement;
the sole sorry remains the main theorem. No new hypotheses, universe restrictions,
scalar maps, proof steps, or mathematical statement corrections are introduced.

Repair validation: scompile.py completed sandbox and library compiles cleanly (7.6 s
and 7.7 s). Revised deliver2.py --no-push passed preflight and compiles at
410521aefff. Final self-check confirmed exact lean.statement, no freeScalars or
restrictChartIso references in Lean, the definition-owned dependency, one theorem
sorry, and all Lean lines at most 100 characters.
