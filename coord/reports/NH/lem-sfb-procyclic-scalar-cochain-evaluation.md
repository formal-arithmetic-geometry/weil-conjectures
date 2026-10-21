## Worker report

The delivery states `ContinuousCohomology.exists_procyclicScalarCochainEvaluation`
in `Sheaf.RepresentationTheory.ProcyclicScalarCochainEvaluation`. Its sole postponed
proof is `sorry`. The four supporting declarations are specifications of the exact
complexes and coefficient square and the existing forgetful and ordinary derived-localization functors on complexes.
No theorem about their existence is used to choose unspecified data. No new independent
notion is introduced, and no dependency declaration is replaced.

Hypotheses and clauses, matched individually:

- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Algebraic closure of Q_ell: `(Ω : Type u) [NormedField Ω]`,
  `[NormedAlgebra ℚ_[ell] Ω]`, and `[IsAlgClosure ℚ_[ell] Ω]`.
  This retains the extended norm topology, with no CompleteSpace assumption.
- Finite intermediate field: `(E : IntermediateField ℚ_[ell] Ω)` and
  `[FiniteDimensional ℚ_[ell] E]`. Its topology and norm are inherited from Ω.
- Both F=E and F=Ω: the existential witnesses D and D' have precisely these two
  coefficient types; both generator maps are asserted quasi-isomorphisms.
- Size convention: explicit universe u is the chosen common bound containing
  coefficients and all test objects, as in the already landed continuousScalarRing.
  Test sets are arbitrary `Profinite.{u}` and additive sheaves have values in u+1.
  This is a universe containing both types, not a condition identifying preassigned
  unrelated universes. The statement does not impose a countability restriction.
- H=Z_ell: Mathlib `ℤ_[ell]`, with its usual p-adic (inverse-limit) topology,
  additive faces `Fin.contractNth i (· + ·)`, and generator `(1 : ℤ_[ell])`.
- Nonnegative U: D.U is integer indexed, D.uNegative makes negative terms zero,
  and D.uEval is an additive bijection onto all `C(S × (Fin n → ℤ_[ell]), F)`.
  Degree zero uses the empty Fin tuple; the coordinates identify H^0 with a point.
- The scalar module structures are the recorded internal modules, not copies.
  D.uScalar says evaluation of a • x at (s,t) is a(s) times x(s,t), and
  D.kScalar gives the same statement on the target.
- Differential: D.differential gives the first deletion with sign +1 and the
  sum over Fin(n+1) with exponent i.val+1. The first n contracted faces add
  adjacent coordinates and the last face drops the last coordinate. These are
  exactly the internal sum i=1,...,n and the last term (-1)^(n+1). D.uZero records
  d^0=0 explicitly. Squaring to zero is built into CochainComplex.
- Two-term K: D.kEval identifies both degrees 0 and 1 with C(S,F);
  D.kOutside makes every other integer degree zero and D.kZero kills all d.
- Actual cochain map: D.epsilon is a morphism of complexes of the internal modules.
  It therefore is linear, respects all restrictions, and commutes with d.
- Degree-zero identity: D.epsilonZero is the identity in the C(S,F) coordinates,
  identifying the unique empty tuple by Fin.elim0.
- Degree-one generator evaluation: D.epsilonOne is exactly evaluation at the
  tuple `fun _ ↦ 1`. D.epsilonOutside makes all higher components zero.
- Parameter naturality for every continuous map: D.uRestriction and D.kRestriction
  specify precomposition for any `v : T ⟶ S`; naturality of the sheaf morphism
  epsilon gives the evaluation square. There is no Nonempty S assumption.
- Coefficient inclusion E→Ω: `E.subtype` in the last conjunct. The compatibility
  structure supplies actual maps uMap and kMap between the underlying sheaf
  complexes; uFormula and kFormula specify postcomposition with this inclusion
  on every section. Its square is equality of the actual cochain maps.
  These formulas also determine scalar semilinearity for the inclusion uniquely.
- Sheaf quasi-isomorphism: `QuasiIso D.epsilon ∧ QuasiIso D'.epsilon` uses the
  ordinary categorical kernel/image homology in the abelian internal module
  categories. It therefore states isomorphism of the cohomology sheaves, without
  closures, and implies invertibility after the ordinary derived localization.
  The conclusion also explicitly supplies the two derived-category isomorphisms,
  each with forward arrow equal to the localized epsilon, as required by the
  2026-10-21 derived-isomorphism convention. procyclicScalarLocalization is the
  existing Q with HasDerivedCategory.standard in the larger universe, without
  any added size hypothesis. These normalized isomorphisms are equivalent to
  the specified quasi-isomorphisms, not arbitrary isomorphisms of the objects.
  No termwise/global exactness of the evaluated section complexes is assumed.
- Local primitives are interpreted in `coherentTopology Profinite`, whose covering
  families are finite jointly surjective families. No global primitive on each S
  and no identification with right derived internal invariants is asserted.

Dependencies actually used:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`, its canonical MonObj and commutativity.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its objects,
  morphisms and forgetful functor. These are the dependency's generic internal
  modules, specialized to the actual abelian sheaves on the profinite site.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: CochainComplex and QuasiIso
  for ordinary abstract kernel/image homology and derived localization.
- The already landed `def-sfb-bundled-continuous-scalar-ring` gives
  `Sheaf.CategoryTheory.ContinuousScalarRing`:
  `Profinite.CondensedAction.continuousScalarRing`. It only bundles the recorded
  continuous-function ring object.
- The already landed `def-sfb-condensed-equivariant-bar-data` gives
  `Sheaf.CategoryTheory.CondensedEquivariantBarData`:
  `CategoryTheory.CondensedBar.Modules`, `sections`, `sectionRing`, `sectionModule`.
  These retain the recorded internal module category and section-module equivalence.
  These two landed nodes are added to stmt_deps as authorized by brief-stage2 §5.
- The size-convention dependency has no declaration: explicit universes implement it.

The proof-only imports retain every already-stated proof input: the homogeneous
cochain coordinates module, spectral norm completeness, normed-field completion,
compact continuous-map norm/completeness and currying, Mahler coordinates, and the
short-exact-sequence homology sequence. The still-unstated
lem-sfb-parameter-cochain-completion-boundary-descent is not imported. Its role and
all nine DAG proof steps are retained in the theorem docstring. A reference for
that analytic descent remains WANTED exactly as in the reviewed DAG; this delivery
makes no new assertion of a completed proof of it.

Edge cases checked before writing: S empty gives the zero function group in every
source and target degree; every field and parameter binder still includes that case.
For n=0 the two differential terms cancel, matching uZero. For n=1 the generator
map is defined on arbitrary cochains, not just cocycles; its cochain-map condition
in degree one is automatic from epsilonOutside and kZero. Negative and n≥2 target
degrees vanish. E=Q_ell is allowed. No completeness of Ω is needed for any
coordinate or scalar operation. A coefficient primitive in the completion is never
used as a continuous Ω-valued function. For H^1, evaluating the additive cocycle at
1 matches the density argument in the node; higher vanishing is sheaf-local only.

Searches performed (results are also in the sandbox searches.jsonl):

- msearch.py leanfinder: "Evaluation at one is a quasi-isomorphism from continuous
  scalar cochains of the p-adic integers on profinite parameters to the
  zero-differential two-term complex". Eight hits: abstract Rep resolutions,
  finite cyclic resolutions, and general quasi-isomorphism/truncation results;
  none states this parameterwise norm-coefficient sheaf assertion.
- msearch.py loogle: "ContinuousCohomology, PadicInt, QuasiIso". Zero hits;
  service reports unknown identifier ContinuousCohomology.
- msearch.py grep: "procyclic|scalar.*cochain|cochain.*scalar", RepresentationTheory.
  Zero Mathlib hits for the requested expressions.
- rg in lean/WeilConjectures and lean/Sheaf for
  "procyclic.*scalar|scalar.*cochain.*evaluation|" followed by the item id:
  no existing declaration of this statement.
- Wider rg searches for procyclic, continuous cochains, scalar cochains and
  parameter cochains found the discrete-coefficient Procyclic modules and
  TopologicalHomogeneousCochainCoordinates, not this comparison. The discrete
  results impose discrete torsion coefficients and are not reused as norm-field
  results. Read ContinuousScalarRing, CondensedEquivariantBarData and the actual
  section-module equivalence before using their declarations.

Sources read: the node and every stmt_deps statement/record; their actual declaration
signatures and docstrings; Stacks etale-cohomology.tex section
section-continuous-group-cohomology (Tag 0DVG); and current main-20261015
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). Stacks only supplies
the continuous differential and explicitly warns against unjustified exactness for
topological coefficients. The analytic scalar comparison remains agent formulated,
as the node states. No mathematical statement correction or dependency repair was
needed. No STATEMENT-DISPUTED flag is introduced.

The preceding worker's stale-assignment report concerned the now-merged stage-1
split. The present packet instead supplies the missing stage-2 Lean statement on
top of that split. No stage-1 content is replaced.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
