## Worker report

The item is stated by `WeilConjectures.coef_rational_retract_evaluation` in
`Sheaf.SixFunctors.RationalRetractEvaluation`. Its proof is `sorry`. All eight auxiliary
declarations in `RationalRetractEvaluation` are explicit definitions of the clauses
of this one node, with source/blueprint docstrings. They introduce no new operation:
transposition, evaluation, symmetry, tensor, scalar extension, and duality are the
published operations. In particular there is no arbitrary pairing chosen in place
of evaluation and no Karoubi completion.

I read the node, its thirteen proof steps, all six statement-dependency statements
and Lean records, their declarations/docstrings, and the current blueprint statement
at `main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-rational-retract-evaluation.md`.
The current blueprint statement is identical to the node's statement. The repair note
for this item is resolved, stage 1: it required splitting long proof steps while
preserving the statement. This delivery does not alter that proof or statement.

Hypotheses and their Lean renderings:

- The finite-field base datum is `D : FiniteFieldDatum.{u}`; `l : ℕ`, `[Fact l.Prime]`
  and `hl : l ≠ D.p` give the coefficient prime different from the characteristic.
- The separated finite-type scheme over the given algebraic closure is `X : Scheme.{u}`,
  `[X.Over (Spec (.of D.k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`,
  `[QuasiCompact (X ↘ Spec (.of D.k))]`, and `[IsSeparated (X ↘ Spec (.of D.k))]`.
  Locally finite type plus quasi-compact is the recorded finite-type convention.
  There is no smoothness, properness, nonemptiness, or geometric connectedness hypothesis.
- `Conclusion` quantifies over every `E : Type u` with `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`.
  The objects are `sfRationalConstructibleCategory l E X`, precisely the raw localization
  of the intrinsic derived-complete integral constructible category in the dependency.
- The internal-Hom permitted-pair witness `h` is existentially asserted in the conclusion,
  not a hypothesis of the theorem. It is the closure infrastructure already supplied
  by rational operations; its proof has no bearing on the resulting Hom object.
- A pairing is an actual arrow `b : (RationalVerdier.tensor D l hl X E).obj (K,L) ⟶ W`.
  The target variable `W` serves as omega in the general formula and as the coefficient
  unit in the last clause. `adjoint` uses `podRationalClosed.transpose`, not an arbitrary
  arrow to a dual. `IsPerfect` means `IsIso` for this adjoint and for the transpose after
  the canonical signed braiding. Thus both adjoints, not just one, occur.
- Chosen images are objects `P,Q` with arrows `i,p,j,q`. The assumptions
  `i ≫ p = 𝟙 P` and `j ≫ q = 𝟙 Q` state the two splitting identities. Their induced
  idempotents are `p ≫ i` and `q ≫ j`, so no image object or additional splitting
  hypothesis is hidden. Adjointness is exactly equality of tensoring the first
  idempotent and tensoring the second idempotent before composing with `b`.
- Finite scalar extension is every `F` with the same finite-extension instances and
  every `ι : E →ₐ[Padic l] F`. Since both fields are finite over the base this is
  exactly a finite coefficient-field extension; no chosen embedding is excluded.
- Site-perfectness is required only by the final implication
  `IsSfRationalCoefficientSitePerfect l E X K → ...`. Neither the general retract
  assertion nor the Verdier assertion assumes site-perfectness.

Clauses and actual maps:

1. `Retracts` says that under precisely the two-sided perfection and adjoint-idempotent
   hypotheses above, the restricted arrow `tensor.map (Prod.mkHom i j) ≫ b` is
   two-sided perfect. Every splitting is quantified over; no object is adjoined.
2. `EvaluationRestriction` gives the actual canonical evaluation identity for every
   retract: apply `homDual.map p.op` to the dual factor and `i` to the original factor,
   then evaluate. The result equals `evaluation P W`. This concerns equality of the
   normalized arrows, not existence of a new perfect pairing.
3. `VerdierRestriction` quantifies over the recorded coherent integral dualizing
   presentations `w` and rationalized Verdier data `A`. Its first clause says that
   `A.evaluation K`, with the canonical symmetry placing the dual first, has both
   adjoints isomorphisms. Its remaining clauses are the actual evaluation restriction,
   `delta_P = i ≫ delta_K ≫ D²(p)`, and
   `delta_P⁻¹ = D²(i) ≫ delta_K⁻¹ ≫ p`. The arrows are `A.bidual.hom` and `.inv`,
   whose integral normalization is part of `RationalVerdier.Datum`. The source's
   right-to-left composition has been converted to Lean's left-to-right convention.
4. `ScalarExtension` states perfection of the transported pairing. Its formula is
   the inverse of `rationalTensorScalarComparison` followed by `scalar.map b`.
   Thus the target is the actual scalar extension of the original target. For Verdier
   evaluation the published dualizing-object comparison identifies this target with
   omega over F; the canonical evaluation/duality comparison squares are retained by
   the imported rational-Verdier and rational-operations interfaces. The general
   retract clause also applies over F, including to the scalar-extended splittings.
5. The unit-valued clause applies `IsPerfect` to the actual
   `evaluation K (RationalOperations.coefficientUnit ...)`, whose first factor is
   the recorded `homDual ... coefficientUnit` applied to K. This is the usual tensor
   dual. `Retracts`, `EvaluationRestriction`, and `ScalarExtension` use arbitrary
   targets and therefore apply to this same unit-valued evaluation without another
   construction or any integral-perfect-lattice assumption.

Dependency declarations used:

- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension`; objects and morphisms stay in the raw localization.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleRationalHomPairs`, `rationalDerivedInternalHom`,
  `rationalDerivedTensor`, `rationalTensorScalarComparison`.
- `Sheaf.SixFunctors.RationalVerdier`:
  `RationalVerdier.units`, `.tensor`, `.Datum`, and `.scalar`, together with
  `IntegralFiniteExtension.DualizingDatum` from its public dependency.
- `Sheaf.SixFunctors.RationalOperations`:
  `RationalOperations.homDual`, `.coefficientUnit`, and the published identification
  of normalized Hom/evaluation with rationalized Verdier evaluation.
- `Sheaf.Paper.CompletedTensorHomTranspose`:
  `CoefficientTransposeLaws` and `completedTensorHomTranspose`; the actual transpose
  is `podRationalClosed.transpose` and its evaluation is `PodPartialClosed.evaluation`.
  I checked their published signatures and the pure-tensor normalization in
  `DerivedAutomorphismHomEvaluation`; this is precisely the completed/rational
  transpose used in the dependency theorem. The signed symmetry is
  `pullbackTensorRationalBraiding`.
- `Sheaf.Paper.SitePerfectComplex` (dependency repair below):
  `IsSfRationalCoefficientSitePerfect`, using the existing
  `IsRationalFiniteProjectiveTerm`, `sitePerfectRationalAmbient`,
  `integralDerivedPullback`, and `DerivedCategory.Q`.

The stated proof-dependency modules are imported privately, including the exact
Mathlib files `CategoryTheory.Triangulated.Pretriangulated`,
`Algebra.Homology.DerivedCategory.HomologySequence`, and
`RingTheory.Localization.BaseChange` for the recorded Mathlib matches.
`lem-coef-rational-scalar-transpose-compatibility` has no recorded Lean module and
therefore has no import; the docstring retains the proof step using that node.
No statement of it is needed to type the present item. The theorem docstring carries
all thirteen DAG proof steps, including the actual inverse maps, the bounded-model
argument, finite-cover denominator argument, and bounded-cohomology truncation argument.

Edge cases checked before finalizing: zero idempotents and zero summands satisfy
exactly the same splitting equations; identity idempotents recover the given pairing;
no mono/image convention excludes either case. The empty scheme is allowed. The
bounded-model definition allows a zero complex and finite free rank zero. Arbitrary
integer bounds and degrees, shifts, and Koszul signs are retained. Identity scalar
extension and every field embedding are included; no positive extension degree is
assumed. Coefficient fields and the scheme use the universe convention of the recorded
intrinsic library, with explicit universe and variable binders and both auto-implicit
options disabled. Definitions contain real data only; the only postponed theorem
is the item itself.

Searches for an existing declaration:

- The preserved `searches.jsonl` records LeanFinder query "A perfect pairing restricts
  to adjoint split idempotents and is preserved by scalar extension": eight hits,
  headed by `LinearMap.IsPerfPair.restrictScalars` and `.restrict`. These concern
  bilinear pairings of modules, not the completed derived coefficient category.
- Its Loogle query `CategoryTheory.Retract, CategoryTheory.IsIso` returned no hits.
- Its Mathlib grep query `[Rr]etract.*[Pp]airing|[Ee]valuation.*[Rr]etract` in
  `CategoryTheory` returned no hits.
- A further LeanSearch query "Perfect pairing evaluation restricts to split adjoint
  idempotents in a closed monoidal derived category" returned generic closed-category
  evaluations, `ExactPairing.evaluation`, and module perfect-pairing results. None
  states the present coefficient-category restriction/extension result.
- `rg` for retract/evaluation in Mathlib's `CategoryTheory/Idempotents` and
  `CategoryTheory/Monoidal/Closed` found the Karoubi retract and generic evaluation
  definitions, not this statement.
- `rg` for evaluation/retract and the item identifier in `lean/WeilConjectures` and
  `lean/Sheaf` found finite-projective module evaluations, strictly-perfect local
  retractions, and proof citations, but no existing declaration of this item.
  The intrinsic site-perfect predicate name was absent in both trees. The existing
  DAG definition is the owning node repaired here, so no new definition node is needed.

Validation: the initial prescribed dry run found a stale dependency `lean.statement`
with a `noncomputable` prefix that the signature extractor omits. The record now
matches the original eight-declaration record and the extracted signature. The
ownership repair and five consumer compile checks are recorded below. No node statement, proof,
statement-dependency list, or proof-dependency list has changed. No statement dispute
remains.

## Dependency modules

`def-weil-site-perfect-complex`: the old record's rational predicate
`IsRationalCoefficientSitePerfect` takes `rationalConstructibleCategory D l hl E Y`.
The statement dependency `def-weil-rationalization-karoubi` now records the different,
intrinsic `sfRationalConstructibleCategory l E Y`. An intrinsic integral representative
has no legacy category membership witness, so the old rational predicate cannot be
applied to the item's objects. Under section 1(B),
`Sheaf.Paper.SitePerfectComplex` states the same rational local-model condition
on those actual intrinsic objects: on every pro-etale slice there is a covering sieve,
and on every member the pulled-back integral representative becomes isomorphic, in
raw scalar localization, to a bounded complex with the existing rational
finite-projective-term predicate in each degree. The old predicate's formula has
been followed clause for clause, including term splittings only after localization.
The new predicate is appended to the owning `SitePerfectComplex.lean`, whose eight
Q33 declarations and bodies remain intact. Its new public import is
`Sheaf.Paper.SfRationalizationKaroubi`, and its scheme binder and topology use
`AlgebraicGeometry.Scheme` in full. The dependency record keeps its original module,
file and primary declaration; its declarations list is the eight original names plus
`IsSfRationalCoefficientSitePerfect`. Only this dependency's `lean` record changes.
Its `lean.note` explains the domain mismatch and additive repair.

## Return repair

H13/H4: removed `IntrinsicSitePerfectComplex.lean`; the single owning module is
`Sheaf.Paper.SitePerfectComplex`. Preserved all eight existing declarations and
appended the intrinsic rational predicate with the same local-model body. The item
publicly imports `SitePerfectComplex` and no longer imports the removed module.
The dependency node now has a superset record rather than a replacement interface.
The live source read through `scompile.py --source` agrees with the shared baseline.

## Second reading by ND

Re-read the retained node, theorem and all eight clause definitions against the
return. `D,l,hl,X` retain exactly the finite-field, prime, characteristic exclusion,
separated and finite-type hypotheses. `Conclusion` still quantifies over every finite
coefficient extension, existentially supplies the permitted-pairs witness, and
conjoins `Retracts`, `EvaluationRestriction`, `VerdierRestriction`, `ScalarExtension`
and site-perfect unit-valued evaluation. Retracts retains both splitting identities,
two-sided perfection and adjointness; restriction is equality of the actual canonical
evaluation maps. The pinned Verdier datum and delta/inverse formulas remain literal.
Scalar extension still uses the canonical inverse tensor comparison. The last clause
uses the same intrinsic rational category as the appended site-perfect predicate.
Its formula matches the live rational predicate clause by clause: every slice, a
covering sieve, a bounded integral complex, rational finite-projective terms, and an
isomorphism after raw localization. No integral splitting assumption was introduced.
Zero and identity splittings, empty X, zero local complexes, and identity scalar
extension remain covered. The theorem signature and all thirteen proof steps are
unchanged. The only changes are dependency ownership, imports, and its superset record.

The five live importers were compiled from current server sources with `scompile.py`:
`Sheaf.Paper.GeometricFrobeniusInternalHomComparison`,
`Sheaf.Paper.InternalHomPullback`, `Sheaf.SixFunctors.InternalHomPullback`,
`Sheaf.Paper.FiniteTorStability`, and `Sheaf.Paper.BasicOperationsCoefficientReduction`.
All compiled cleanly with the repaired public `SitePerfectComplex` interface (the
slowest was `BasicOperationsCoefficientReduction` at 45.2 seconds, within the limit).
