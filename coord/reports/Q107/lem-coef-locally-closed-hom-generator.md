## Worker report

The module `Sheaf.Paper.LocallyClosedHomGenerator` states
`AlgebraicGeometry.Etale.LocallyClosedHomGenerator.normalizedComparison`.
Its only theorem has proof `sorry`; every helper has real data. No source statement is
changed and no dependency module is repaired. The four helpers only expose this node's N, Q,
the inverse of its fixed internal-adjunction arrow, and its expanded conclusion.

Hypotheses, objects and conclusions, matched clause by clause:

- The fixed algebraic closure of a finite field is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  This supplies p, its primality, q, the finite field and its chosen algebraic closure D.k.
- The prime ell is `l : ℕ` with `[Fact l.Prime]`; `_hl : l ≠ D.p` is the required
  prime-to-characteristic hypothesis. E is `Type u`, with `Field E`, `Algebra (Padic l) E`
  and `FiniteDimensional (Padic l) E`.
- Positive integers n,m are `n m : ℕ+`; `hmn : m ≤ n` is the level inequality. The actual
  coefficient rings are `CoefficientPairingChange.coefficient l E n` and its m analogue,
  namely the existing uniformizer-power quotient rings with `ULift.{u+1}`. This standard
  lift implements the module universe and makes no restriction on the ring or its values.
  `reduction l E n m hmn` is the quotient factor homomorphism, not an arbitrary ring map.
- `X : Scheme.{u}`, `X.Over (Spec (CommRingCat.of D.k))`, `LocallyOfFiniteType` and
  `QuasiCompact` on its structure map express finite type over k; `IsSeparated` expresses
  separatedness. No finite-type or separated hypothesis is added on S, Z, g or j.
- `g : Z ⟶ X` with `IsClosedImmersion g` and `j : S ⟶ Z` with `IsOpenImmersion j`
  are exactly the given factorization. All operations are ordinary unbounded operations
  on `Sheaf T.smallEtaleTopology (ModuleCat R)`, never pro-etale operations.
- `L` is an actual A-module sheaf. `_hL` supplies a `Scheme.LocallyConstantDatum L` and,
  for each cover member, a constant module P with `Module.Finite A P` and
  `Module.Projective A P`, and an isomorphism of module sheaves on the localized site.
  This is precisely etale-local constancy with finite-projective values; global freeness
  is not assumed. `DerivedCategory.singleFunctor _ 0` places L in degree zero.
- `M : DerivedCategoryModule A X` and `_hM : finiteTorConstructibleEtale ... X M`
  use the existing intersection of bounded constructible cohomology with the existence
  of integers a ≤ b and `hasTorAmplitudeIn A X a b M`. The latter tests every degree-zero
  module sheaf, with no flatness restriction on the tests.
- `exceptionalObject g j M` is N, definitionally the existing `exceptional A g j` applied
  to M, hence j^* Rg^! M for the ordinary closed-support adjunction.
  `innerHom g j (singleFunctor ... L) M` is Q = H_A(L,N), using `derivedHom`.
- The first two conjuncts assert precisely that N and Q lie in the same D^b_ctf on S.
- `IsNormalizedComparison` expands the remaining conclusion. It first asserts `IsIso`
  of the specified I_A arrow; `inverseInternalAdjunction` is its inverse where it is
  invertible (and zero otherwise, only to totalize the data). Its inverse therefore
  uses no postponed choice and no assumption of invertibility of the target map v.
- The subsequent six `IsIso` conjuncts assert invertibility of every arrow in the
  displayed formula: F_X(I_A^-1); c; Rs_*(u); Rs_*(H_B(1,b)); I_B; H_B(q,1).
  The formula in the node contains these six arrows, although some surrounding proof
  prose calls them seven. All displayed factors are retained.
- c is `CoefficientPairingChange.ordinaryComparison`, the ordinary counit comparison
  in the canonical Rg_* Rj_* composition coordinates. u and v are
  `CoefficientPairingChange.evaluationComparison`, the transpose of reduced evaluation.
  b is the actual `etaleShriekLocallyClosedCoefficientMap`, not arbitrary data;
  its dependency gives invertibility and exactly the stated pasted-counit equation.
  q is `CoefficientPairingChange.compactComparison`, closed direct-image comparison
  followed by g_*(open comparison), equal by construction to the published support map.
- I_A and I_B are `CoefficientPairingChange.internalAdjunction`: their construction
  transposes exactly the compact-support projection, ordinary counit, evaluation, and
  pasted exceptional counit. In particular the projection is the specified closed
  proper projection followed by inverse open projection, with the published left-tensor
  argument convention. Neither internal adjunction is an arbitrary endpoint isomorphism.
- The last conjunct is equality of the fully expanded composite with the evaluation
  transpose v at `(shriek A g j).obj L, M`. Contravariance in q uses `.map q.op`;
  covariance in b uses the second-variable `.map`. The intermediate objects therefore
  are exactly the objects in the node, including F_SN before applying H_B(1,b).

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its coefficient constructions underlie
  the existing `CoefficientPairingChange.coefficient`, `coefficientFinite`, `reduction`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary `DerivedCategory`,
  `DerivedCategory.singleFunctor`, `DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`,
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` provide the general
  ringed-site interface. The already-published constant-etale specialization is
  `AlgebraicGeometry.Etale.scalarExtension`, used through the pairing-change module;
  there is no replacement of the generic ringed-site construction.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` publicly exposes the
  constant-etale `AlgebraicGeometry.Etale.derivedHom`, `derivedTensorHomAdjunction`;
  these are used directly, as its recorded dependency note prescribes.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: `hasTorAmplitudeIn`, also the
  public upstream declaration tested against every degree-zero module sheaf.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`. The convention-only scheme-properties node
  has no declaration: `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` are its
  prescribed Mathlib notions.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`; this is the instance
  used by the recorded `CoefficientPairingChange.exceptional` and its counit.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`; the prescribed closed/open presentation
  is the existing `CoefficientPairingChange.shriek`, not a new compact-support functor.
- `Sheaf.Paper.InternalAdjunctionPairingChange`: `shriek`, `star`, `exceptional`,
  `internalAdjunction`, `ordinaryComparison`, `compactComparison`,
  `evaluationComparison`, `coefficient`, `coefficientFinite`, `reduction` in
  `AlgebraicGeometry.Etale.CoefficientPairingChange`.
- `Sheaf.Paper.EtaleLocallyClosedShriek`: `etaleShriekLocallyClosedCoefficientMap`
  and `etaleLocallyClosedShriekComparisons`, including its exact counit normalization.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`.
  The two new definition nodes below name the plain published interfaces; the two
  theorem nodes remain proof dependencies. The finite-Tor definition is cited through
  the new exceptional-comparison definition node.
- Proof dependencies imported include the recorded finite-dimension theorem from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, Mathlib Noetherian
  and Krull-dimension facts, and `Sheaf.Paper.FiniteCoefficientDirectImage`.
  `lem-coef-finite-hom-domain-calculus` and `lem-coef-etale-lisse-hom-reduction` have
  no recorded declarations and are proof-only prerequisites, so have no module to import.

Edge cases checked before writing: n=m gives identity reduction and is allowed;
positive levels include m=1; zero L and zero M are allowed; a trivialization by the zero
projective module is allowed; empty S, Z, X and an empty covering index are allowed;
no nonemptiness or positive rank is imposed; Tor intervals for N,Q are existential,
not fixed to the interval of M. No independent index universe makes an assumption
vacuous. The geometry and coefficient universe conventions match the published maps.

Searches (no matching existing theorem found):

- `msearch.py ... leanfinder`: "Derived internal Hom of locally closed extension by zero
  finite projective local system commutes with coefficient reduction". Eight hits on
  light condensed internal Hom and its pointwise currying; none is this etale theorem.
- `msearch.py ... loogle`: `"ihom", "curry"`. Twelve generic monoidal currying hits;
  none includes exceptional restriction or coefficient reduction of a stratum generator.
- `msearch.py ... grep`: `locallyClosed.*[Hh]om|[Hh]om.*locallyClosed|[Ll]ocallyConstant`
  in `CategoryTheory/Sites`: no hits.
- `msearch.py ... leansearch`: "Internal Hom extension by zero locally closed finite
  projective etale coefficient change". Eight hits on function extension by zero,
  module morphisms and Ext, none on this normalized comparison.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for local constancy, finite projectivity,
  and locally-closed Hom found the reusable pairing-change and shriek modules and the
  existing `Scheme.LocallyConstantDatum`/constant-value trivialization interface.
  `rg` for the exact item id in `lean/WeilConjectures` found no declaration. Direct reads
  confirmed that the pairing-change theorem proves an equality before precomposition
  and assumes N,Q finite-Tor; it does not assert this generator theorem.

Validation: `scompile.py Q107 lem-coef-locally-closed-hom-generator` compiled both the
sandbox and library module names cleanly in 4.2 seconds each. Final delivery checks follow.
No STATEMENT-DISPUTED flag and no dependency-module repair. The returned H2 ownership
fault is repaired by the two new definition records below.

## Second reading by Q107

Self-review with the node and module open: checked the ring quotient and its direction,
positivity of both levels, geometry without extra hypotheses, finite-projective local
trivializations, degree-zero inclusion, ordinary etale categories, N and Q, and each
factor and its direction. Checked the final q map is contravariant, b is covariant,
and that u and v use the published evaluation transpose. Checked that inverse data is
real and its isomorphism locus is asserted, and that every helper is recorded in
lean.declarations. No mathematical mismatch was found. The numerical "seven" in
proof prose was avoided in the module because the displayed formula has six arrows.
The dispatcher prohibits starting other agents; this section records a self-review,
not an independent review. The maintainer's separate delivery review is independent.


## New nodes

`def-coef-internal-adjunction-comparison-maps` records the existing definitions in
`Sheaf.Paper.InternalAdjunctionPairingChange` with `existing: true`: shriek, star,
exceptional, both counits, projection, internalAdjunction, compactComparison,
ordinaryComparison, evaluationComparison, coefficient, coefficientFinite, and reduction.
The self-contained statement defines exactly their closed/open pairing and scalar maps;
it asserts neither invertibility nor a comparison theorem. The source is the unchanged
blueprint proof of thm-coef-finite-hom, paragraphs 3–4.

`def-coef-etale-locally-closed-comparison-maps` records the existing definitions in
`Sheaf.Paper.EtaleLocallyClosedShriek` with `existing: true`: closed exceptional functor,
closed and composite adjunctions, conditional direct inverse, closed and locally closed
coefficient maps, support map, and the expanded comparison predicate. The statement
includes the inverse's zero value away from its IsIso locus and the complete predicate,
without asserting it. It cites `def-weil-finite-tor-amplitude` for the prescribed
finite-level domain. Source: the same blueprint proof, paragraphs 3–4.

Searches for both records (2026-10-22): LeanSearch query “Canonical internal adjunction
and exceptional coefficient comparison for closed open factorizations on small etale
sites” returned eight generic adjunction hits, including CategoryTheory.ihom.adjunction
and Functor.sheafAdjunctionCocontinuous, with no such derived stratum maps. LeanFinder
query “Derived etale internal adjunction coefficient change canonical evaluation pairing
for locally closed immersion” returned eight standard-etale presentation/site hits,
with no match. msearch grep `internalAdjunction|etaleShriekLocallyClosedCoefficientMap|
compactComparison` returned zero Mathlib hits. Direct rg of Mathlib/CategoryTheory and
WeilConjectures found none. Direct rg of Sheaf found the two exact published modules;
no replacement definitions are written. Direct rg of DAG nodes for the declaration
names found only the two theorem nodes; the definition-node scan found no owners.
blueprint_refs searches “internal adjunction” and “locally closed comparison” both
returned zero matches. The searches are recorded in each new node's mathlib_searches.

## Returned H2 repair and second reading by Q107

The saved packet's initial dry run passed at 0b35c20246f, but independent review
correctly found that its two added theorem statement dependencies did not own the
plain helper definitions used in the statement. Compared the retained packet with
the current shared source: only lean and stmt_deps differ on the item. The original
12 statement dependencies are retained; the two theorem entries and the direct
finite-Tor entry are replaced by the two definition nodes above. Both original
theorems remain in proof_deps, byte-for-byte unchanged. The Lean module remains
byte-for-byte unchanged, and only lean.note changes within its binding.

Re-read the item module and both published modules with the new node statements.
For the first new node, checked the three functors, both counits, projection direction,
internal-Hom transposition, the closed-then-open scalar maps, evaluation transpose,
positive quotient levels, quotient-factor reduction and lifted finiteness instance
against every listed declaration. For the second, checked the ambient adjoint,
pasted adjunction, conditional inverse, exact counit transpose, restriction comparison,
support map and every conjunct of the generic comparison predicate. Its finite-Tor
specialization cites the existing definition rather than introducing a copy.

The generator's hypotheses and all conclusion factors are unchanged from the
clause-by-clause reading above. Checked again n=m, m=1, zero L/M and projective rank,
empty schemes or cover, and identity g/j: the new records introduce no hypotheses,
nonemptiness conditions or universe restrictions. All new lean.statement signatures
are extracted verbatim from the unchanged published declarations. No theorem is
used to choose any of these constructions. No mathematical mismatch remains.
The dispatcher forbids other agents, so this is the required self-check; independent
review remains the maintainer's responsibility.

Repair validation: the unchanged delivered Lean module passed the prescribed
`scompile.py` checks in 11.4 seconds (sandbox name) and 10.9 seconds (library name),
with no errors or disallowed warnings. The new definition nodes only attach existing
declarations; no published module is copied or edited.
