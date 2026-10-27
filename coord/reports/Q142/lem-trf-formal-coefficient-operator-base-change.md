## Worker report

Stage 2, Q142, lem-trf-formal-coefficient-operator-base-change.

The current live item has status split, its accepted Q40/L eight-step proof, no
Lean record, and a stage-2 state entry in coord/queue.tsv. The inherited BLOCKED
ending concerned a stage-1 unchanged-node refusal. The stage handoff in
coord/brief-stage2.md §0 explicitly permits this stage-2 statement delivery.
The accepted statement and proof are preserved. Only lean and the addition of
one definition dependency change in the item. No repair note or numbered return
for this item was present in coord/repair-notes or coord/returns/Q142.md.

The delivery defines the finite-expression syntax and states ten named theorem
clauses, all with sorry proofs. The main recorded declaration is
MvPowerSeries.FiniteCoefficientExpression.eval_map; lean.declarations lists all
ten clauses. Every postponed theorem belongs to this same DAG statement and its
docstring gives the corresponding complete argument, citing the accepted steps.
Definitions have actual data and no postponed well-definedness obligations.

Hypotheses and clauses, matched to Lean:

- Arbitrary commutative rings R,S and a unital homomorphism are explicit
  [CommRing R], [CommRing S], and σ : R →+* S. Independent universes u and v
  allow any relative coefficient sizes. No flatness, locality, nontriviality,
  injectivity, surjectivity, topology or lifting hypothesis is imposed.
- A finite set of variables is Fin n, and exponents are Fin n →₀ ℕ. Every finite
  variable set has a labeling of this form, including n = 0. Finite tuple sizes
  are Fin k and Fin l; matrix intermediate boundaries retain their tuple sizes.
- The exact list of allowed operations is the inductive
  FiniteCoefficientExpression: identity, add, comp, multiply, insert, extract,
  matrix. Source and target variable/tuple counts are its four indices, so comp
  can only connect matching boundaries. Fixed series may have arbitrary support.
- FormalCoefficientTest stores an injection of retained variables and a fixed
  exponent zero on those retained variables. Its eval reads the coefficient at
  fixed + gamma.mapDomain inclusion, giving the full complementary series. This
  is precisely E_(U,beta), including U or V empty. It permits any variable order.
- Matrix evaluation is the finite sum of M i j acting on H j. An inverse is
  represented by its supplied entries, without a noncanonical inverse operation.
- FiniteCoefficientExpression.map recursively applies σ to every stored matrix
  entry or complete series and preserves all index data. eval_map is the stated
  intertwining formula on tuples; scalarEval is the one-component specialization.
- linear_finite_continuous asserts additivity, scalar compatibility, finite
  dependence of each output coefficient on a finite set of component/exponent
  input coordinates, and Continuous for the explicitly discrete coefficient
  product topologies. Applying it to A.map σ supplies S-linearity on all inputs.
- eval_eq_map transports equality of operator functions to all target inputs.
  value_eq_map transports equal values on specified inputs, permitting different
  source boundaries. formalCoefficientMatrix_inverse_map explicitly preserves
  both equations M*N=1 and N*M=1 for the supplied inverse.
- isKernelProjection_map quantifies over D : ι → FormalCoefficientTest n with
  ι : Type z unrestricted. IsKernelProjection is exactly image containment and
  pointwise fixing. formalCoefficientKernel demands equality to the zero FULL
  extracted series, so no complementary coefficient is discarded.
- hasIdealCorrection_map assumes [IsNoetherianRing S] only for the ideal clause.
  HasIdealCorrection f is ∀ H, P.scalarEval H - H ∈ Ideal.span (Set.range f).
  The conclusion uses f mapped coefficientwise and quantifies over every S
  series. No image-of-σ input restriction appears. A finite generator list is
  Fin q, allowing q=0 and zero or repeated entries.
- flattenFormalCoefficients and unflattenFormalCoefficients use
  Finsupp.sumFinsuppEquivProdFinsupp in opposite directions. The
  flattenFormalCoefficients_ring_identification clause states inverse identities
  and preservation of addition, multiplication and one. This is an actual ring
  identification and makes no assertion that two chosen topologies coincide.
- hasIdealCorrection_formalTarget quantifies over any Field L and arbitrary
  τ : R →+* MvPowerSeries (Fin x) L, asserts that its coefficient ring is
  Noetherian, and gives the ideal containment for EVERY joint-variable series
  H : MvPowerSeries (Fin x ⊕ Fin t) L after the specified regrouping. The
  generators are exactly flatten(map τ (f j)). No continuity of τ is required.
- map_identity_comp explicitly gives identity and composition compatibility of
  all recursively stored expression data. The accompanying Mathlib map_map and
  map_id give the same compatibility for specified series. Matrix entries are
  pointwise coefficient maps. Continuous changes of coefficient variables fixing
  T are included among these arbitrary coefficient-ring homomorphisms.

Dependency declarations read and used:

- def-weil-pbc-multivariate-power-series records Mathlib.RingTheory.MvPowerSeries.Basic,
  MvPowerSeries, with its full coefficient-family definition and ring operations.
- def-weil-matrix records Mathlib.LinearAlgebra.Matrix.Defs, Matrix. The concrete
  matrix import is Mathlib.Data.Matrix.Basic, which exposes that definition and
  finite products/maps. The draft's nonexistent LinearAlgebra.Matrix.Basic import
  was corrected to this actual Mathlib module.
- def-weil-field is a Mathlib leaf with match Field, read in
  Mathlib.Algebra.Field.Defs. No lean record is needed on that dependency.
- def-weil-pbc-noetherian-ring records Mathlib.RingTheory.Noetherian.Defs,
  IsNoetherianRing, read together with isNoetherianRing_iff_ideal_fg.
- Proof-only imports are Mathlib.RingTheory.MvPowerSeries.Equiv, whose
  MvPowerSeries.isNoetherianRing supplies lem-weil-pbc-power-series-noetherian,
  and Mathlib.RingTheory.Filtration, whose
  Ideal.iInf_pow_smul_eq_bot_of_le_jacobson supplies the Jacobson intersection
  node. Their full signatures and surrounding source were read. The Stacks
  source algebra.tex, lemma-Noetherian-power-series and
  lemma-intersection-powers-ideal-module(2), was read locally. The current
  literature/blueprint/latest local-term-locality and sk-i-curve-zero statements
  were read for the ancestry; this is the generic algebra subargument described
  by the accepted split, not a change to the unit statement.

Searches:

The prescribed msearch wrapper logged LeanSearch, Loogle, LeanFinder and Mathlib
grep in searches.jsonl. Loogle `MvPowerSeries.map, MvPowerSeries.coeff` returned
coeff_map and map_toSubring: these transport individual coefficients but do not
state the finite-expression theorem. LeanFinder on the full finite-expression
base-change statement returned coefficient convolution/truncation identities,
which were read in the result signatures. LeanSearch on finite formal coefficient
operator syntax returned finite-free tensor base-change matrix lemmas and
unrelated analytic/coefficient lemmas; none constructs this syntax. The inherited
successful LeanFinder query on the definition returned MvPowerSeries, PowerSeries
and their constructors, not a finite operator language. Mathlib grep
`coefficient.*operator|row.?finite|partial.*coeff` in RingTheory/MvPowerSeries
returned zero hits. Local rg searched FiniteCoefficientExpression,
FormalCoefficientTest, finite coefficient expression, and coefficient/operator
patterns in dag/nodes, dag/lean_names_upstream.json, lean/Sheaf and
lean/WeilConjectures: no duplicate. The item-id search in WeilConjectures found
no existing statement. blueprint_refs.py search 'coefficient operator' returned
zero blueprint nodes; ancestor returned lem-trf-local-term-locality. The new
node records the wrapper search outputs verbatim in mathlib_searches, as well as
the local and blueprint searches. No search outage was counted as a negative.

Edge cases checked before finalizing:

Zero rings are admitted by CommRing; a unital map from the zero ring can only
have a zero-ring target. No Nontrivial hypothesis is used. Variable and tuple
counts may be zero; exponent zero on Fin 0 is the sole exponent. Empty matrix
rows/columns give empty sums, and both inverse equations remain meaningful for
0-by-0 matrices. No tests gives the entire kernel and forces P to fix every
series. A test retaining all variables with fixed=0 is the identity test, so its
kernel is zero; retaining none tests just one scalar. Arbitrarily many tests are
allowed, without an added Fintype instance. q=0 means the zero ideal; the theorem
then transports P=identity, also consistent with the operator-equality clause.
Zero and repeated generators need no additional hypothesis. Empty X or T in
the iterated formal-target clause have the expected regrouping. The target ring
need not be a field, local or a domain in the general Noetherian clause.

Both files compiled successfully via scompile.py, separately in dependency
order, under the default per-file 60-second limit, with no errors or warnings.
There is no statement dispute, statement correction or dependency-record repair.

## New nodes

`def-trf-finite-coefficient-expression` provides exactly the missing syntax and
semantics: the finite typed grammar, full-series coefficient tests, recursive
evaluation and coefficient transport, coefficient topology, common-kernel
projection predicate, ideal-correction predicate, and coefficient regrouping in
both directions. Its source is the coefficient-family construction in the
accepted item's Steps 1--4 and 8, the generic algebra input to BM 1997 Remark 9.11.
The existing power-series and matrix nodes define its underlying objects, but
neither they nor the searches above supply this finite-expression language.
The node has an independent definition module and the item cites it in stmt_deps.

## Second reading by Q142

A separate agent was explicitly prohibited by the dispatched brief. This section
records a second pass by the same worker, not an independent review; the delivery
is submitted for the maintainer's independent reading as the brief specifies.

I reread the original node alongside both complete Lean files and checked every
hypothesis/clause against the correspondence above. The expression grammar does
not restrict full series to polynomials. Its map acts on coefficients rather than
performing algebraic tensor base change. The partial-test fixed exponent vanishes
on the retained coordinates, so no index is selected twice, and evaluating the
whole complementary series enforces all complementary degrees. The arbitrary
family's universe is independent of the coefficient rings. The ideal correction
uses scalarEval on all source and all target series; it does not replace a
Noetherian target by a field or assume flatness. The field-target statement
includes arbitrary joint formal inputs after an explicit ring regrouping. Both
inverse matrix equations and identity/composition compatibility are explicit.
No statement mismatch was found. During compilation I corrected the draft's
nonexistent matrix import, marked the two noncomputable exponent-regrouping maps
noncomputable, and marked the topology definition instance_reducible to remove
a class-definition warning. No mathematical hypothesis or conclusion changed.

Preflight metadata repair: the current stage2_delivery.py NEW_NODE_KEYS requires
import_flags (maintenance update 2026-10-23), although the brief omits it. The
new definition node now contains import_flags: []. No existing-node field changed.
