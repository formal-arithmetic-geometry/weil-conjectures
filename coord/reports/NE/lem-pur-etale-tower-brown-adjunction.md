## Worker report

The delivery states `AlgebraicGeometry.etaleTowerBrownAdjunction` in
`Sheaf.Paper.EtaleTowerBrownAdjunction`. Its only postponed proof is that named theorem.
All auxiliary definitions have real data. The statement is unchanged.

The prior attempt's unchanged-node refusal did not represent an existing stage-2
statement: the live node has a stage-1 PASS and no Lean attachment. This packet supplies
a new Lean theorem and its attachment. No released repair order is needed to replace
a reviewed Lean attachment, since none existed.

### Hypotheses and clauses

- The two primes are `(p l : ℕ) [Fact p.Prime] [Fact l.Prime]` and `_hpl : p ≠ l`.
- The arbitrary characteristic-p field is `(k : Type u) [Field k] [CharP k p]`.
  No algebraic closure, finiteness or perfection of k is assumed.
- The finite extension is `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`.
- R is exactly `Padic.coefficientExtensionIntegers l E`. The variable `t` ranges
  over that ring; `_ht : Ideal.span {t} = Padic.coefficientExtensionMaximalIdeal l E`
  says that it is a uniformizer. This includes every uniformizer, not only the
  selected one `Padic.coefficientExtensionUniformizer`.
- `X Y : Scheme.{u}`, their `Over (Spec (.of k))` structures, `IsSeparated` on
  their structure maps, and `LocallyOfFiniteType` plus `QuasiCompact` on those
  maps say precisely separated finite-type k-schemes. `(f : X ⟶ Y)` with
  `[f.IsOver (Spec (.of k))]` is the k-morphism. No extra properness,
  separatedness or finiteness hypothesis is placed on f.
- `(c : Compactification f)` is the recorded open/proper factorization. Its
  `c.i`, `c.Z`, and `c.g` are j, X-bar and g, and its factorization field is jg=f.
- `strictEtaleCoefficientSystem T R t` abbreviates the recorded `CoefficientSystem`
  of quotient-ring module sheaves. Its objects have actual semilinear successor
  transitions; its morphisms have actual compatible components. These are not
  normalized, bounded or constructible systems. The coefficient at Lean index n
  is `R / (Ideal.span {t})^(n+1)`, precisely the node's A_(n+1).
- `DerivedCategory` is the ordinary unbounded localization. Its standard instance
  is the existing `strictEtaleSystemDerived`, not a separately chosen category.
  `S.PX`, `S.PZ`, `S.PY` are the existing exact derived-evaluation packages;
  their `evaluationFactors` tie them to componentwise evaluation on complexes.
  The pro-etale categories mentioned in the node introduce context only: no
  pro-etale functor or pro-etale exceptional adjoint occurs in its conclusion.
- Existence of `S : StrictEtaleCompactSupport R t c` supplies the ordinary
  termwise open extension, its exactness, normalized level adjunctions and
  termwise derived factorization, and the universal proper right-derived
  functors computed on K-injectives. In particular `S.functor` is definitionally
  `S.derivedOpen ⋙ S.properDerived.system.direct`, and `S.levelFunctor n` is
  its recorded finite-level counterpart. S is a conclusion, not a hypothesis.
- `siteX`, `siteZ`, `siteY` assert `EtaleTowerBrownSiteProperties` for the three
  specified sites. This predicate asserts `IsGrothendieckAbelian.{u+1}` and
  existence of ordinary and derived coproducts, preservation of coproducts by Q,
  preservation by every derived evaluation, and `IsIso a ↔ ∀ n, IsIso (e_n.map a)`.
  Q preserving coproducts means exactly that sums of complexes represent derived
  sums: sums in complexes are termwise. Componentwise abelian exactness is
  already the recorded coefficient-system category's abelian structure.
- `S.evaluation n` is the existing *defined composite* of the open and proper
  natural comparisons, giving `F ⋙ e_n ≅ e_n ⋙ F_n` on the whole derived category.
  Naturality includes the map action, not just objectwise isomorphisms.
- `openRestriction` is the open-extension comparison for scalar restriction.
  `openRestrictionMate` fixes it by the *inverse* of the already recorded
  inverse-image restriction isomorphism. The derived mate fixes its normalization;
  it is not an arbitrary natural isomorphism.
- `etaleTowerBrownRestriction` pastes that open comparison with
  `S.properDerived.restrictedDirect`, using associators and whiskering. The
  `transition` field is exactly the commuting square between `S.evaluation m`,
  `S.evaluation n`, and the source/target actual quotient transitions. It covers
  every n≤m, including identity quotients, and every unbounded system K. The
  transition transformations are natural and already obey their quotient laws.
- `leftAdditive`, `leftShift`, `leftExact` state exactness of F as a triangulated
  functor. `coproducts` quantifies over every `I : Type (u+1)`, the common sheaf
  universe, including empty and infinite index sets.
- `scalarX` and `scalarY` are the existing `StrictEtaleScalarAction` records.
  Their ordinary normalization is multiplication by the image of r in each
  constant quotient sheaf; their representative equation is its localization on
  complexes. These normalizations fix the canonical scalar action, with its ring
  laws. `leftLinear` and additivity express R-linearity on derived Hom groups.
- `right` is an actual ordinary derived-system functor G and `adjunction` is
  `S.functor ⊣ right`, containing the actual unit and counit and both triangles.
  `rightAdditive`, `rightShift`, `rightExact` state that G is exact.
- `scalarTranspose` says that the transpose of scalar multiplication followed by
  the counit is scalar multiplication on G(L), precisely the node's prescribed
  action. `rightLinear` records scalar preservation by G. `homLinear` is the
  R-linearity formula for the actual `adjunction.homEquiv`, and `homAdditive`
  gives its additive part. All compositions have their actual categorical types.

### Dependency declarations used

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, reexports the coefficient extension
  construction. `CoefficientExtension` defines the integer ring, maximal ideal,
  ideal powers, quotient rings and quotient homomorphisms used here.
- `WeilConjectures.Compactification.RefinementCategory`,
  `AlgebraicGeometry.Compactification.Refinement` and its category; its public
  underlying `Compactification` is the actual open/proper factorization.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`,
  `SheafOfModules.coefficientSystemDerivedComparison`, and its public modules
  provide `CoefficientSystem`, `CoefficientEvaluationDerivedPackage`,
  `CoefficientSystemOrdinaryImage`, `CoefficientSystemDerivedImage`, and their
  canonical evaluation/restriction/transition data.
- `Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint`,
  `CategoryTheory.grothendieckDerived_hasRightAdjoint`, is the Brown input. Its
  common indexing-universe convention is retained; the main result does not
  assert compact generation.
- `def-weil-pbc-scheme-conventions` is explicitly a convention node with no
  declaration. Its Mathlib scheme, Over, IsOver, IsSeparated,
  LocallyOfFiniteType and QuasiCompact meanings are used directly.
- The already landed `Sheaf.Paper.EtaleCoefficientSystemAdjoint` supplies
  `strictEtaleCoefficientSystem`, `strictEtaleLevel`, `StrictEtaleEvaluation`,
  `StrictEtaleCompactSupport`, its `functor`, `levelFunctor`, `evaluation`, and
  `StrictEtaleScalarAction`. We reuse these definitions only. Its theorem assumes
  a finite-field datum and cannot serve as an existing match for this node.
  These plain definitions are owned by the live definition node
  `def-per-strict-etale-system-interfaces` (existing:true on that same module,
  N5, reviewed pass), which is the added stmt_dep under brief-stage2 §5
  (STMT_DEPS MAY GAIN LANDED NODES). No theorem of
  `lem-pur-etale-coefficient-system-adjoint` is needed. This avoids private
  copies of these notions and introduces no new node or statement correction.
- Every recorded proof-dependency module is imported without `public` (those
  also needed in the signature are public). The Mathlib leaves for linear
  localization, exact factorization, linear derived categories, adjoint exactness
  and shift compatibility are imported by their recorded source modules.

### Edge cases

The field k need not be algebraically closed or finite; the theorem has neither
restriction. Ramified finite extensions are allowed. Any generator of the maximal
ideal is allowed, so changing a uniformizer by a unit is covered. Lean level 0 is
positive exponent 1, not the zero coefficient quotient. Identity reductions n=m
are included in both mate and transition equations. Empty X, empty Y, empty
compactifications and empty coproducts are allowed; no nonempty hypothesis or
positive dimension occurs. The coproduct index has the common sheaf universe,
and the derived localization has the existing standard universe u+2. Neither
boundedness nor normalization nor constructibility is assumed on derived objects.
The asserted canonical comparisons are natural isomorphisms of functors in the
derived category, not only degreewise homology identifications.

### Searches and source checks

- `msearch.py leanfinder`: “Compact support on derived categories of strict etale
  coefficient systems preserves coproducts and admits a linear Brown right adjoint”.
  Eight hits: condensed locally-constant adjunctions, general derived adjunctions
  and unrelated condensed functors. No matching geometric system Brown theorem.
- `msearch.py loogle`: `CategoryTheory.Functor.IsLeftAdjoint,
  CategoryTheory.Functor.Linear`. Zero hits for the combined query.
- `msearch.py grep`: `etale.*[Bb]rown|[Bb]rown.*etale|[Cc]oefficient[Ss]ystem.*[Aa]djoint`
  in Mathlib CategoryTheory. Zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for Brown/etale tower and system
  adjunction names found the existing `EtaleCoefficientSystemAdjoint` module;
  its full structures and theorem hypothesis were read. Searching the exact node
  id and proposed declaration names in both roots found no existing declaration.
- Read all five original statement-dependency node statements and Lean records,
  including the convention-only node. Read their recorded source declarations
  and docstrings and the evaluation/ordinary-image/derived-image helper signatures.
- `scompile.py --source Sheaf.Paper.EtaleCoefficientSystemAdjoint` confirms the
  current server source has the same reusable definitions and finite-field theorem.
- Read Stacks `injectives.tex`, proposition-brown (Tag 0F5Y): the source explicitly
  concludes an exact right adjoint from Grothendieckness, exactness and preservation
  of sums. The node's nine proof steps are carried in the theorem docstring.

No STATEMENT-DISPUTED flag and no statement correction. The main conclusion is a
Nonempty record containing the actual functor, adjunction and canonical data; no
definition selects unspecified data from the postponed existence theorem.


## Repair of returned delivery 0731a6545a1d

H2: replaced the added theorem statement dependency
`lem-pur-etale-coefficient-system-adjoint` with its live definition owner
`def-per-strict-etale-system-interfaces`. Read the latter node's full statement,
Lean declarations and N5 review, and checked the existing module's definitions
and projections. They supply exactly the strict coefficient system, derived
evaluation, compact support and scalar action interfaces used by this file,
without the enclosing finite-field existence theorem. Updated `lean.note` and
the dependency account above. The Lean module is unchanged. The saved packet's
initial dry run passed (8507732ae4a); that did not repair H2, so this packet
contains the requested actual dependency replacement.

Compared the saved node with current live main: before repair only `lean` and
the added statement dependency differed. All original stage-1 fields remain
identical; the repaired packet adds only the existing definition owner to the
five live statement dependencies. The return's other clauses and advisories
require no changes. No new nodes, dependency modules or statement correction.

## Self-check by NE

Re-read the unchanged Lean file and the node. The hypothesis and clause mapping
in the Worker report still applies verbatim: arbitrary characteristic-p field,
arbitrary uniformizer, positive coefficient exponents, separated finite-type
schemes, canonical evaluation and transition comparisons, Grothendieck and
coproduct properties at all three sites, exact linear compact support, and an
actual exact linear ordinary derived adjunction. The only repair is the DAG
ownership of the reused definitions. This is a worker self-check; the
maintainer's independent reading is supplied by the returned review.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
