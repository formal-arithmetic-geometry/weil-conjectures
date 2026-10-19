## Worker report

The module `Sheaf.Paper.QuasiFiniteCompactSupportWeights` states
`WeilConjectures.sfQuasiFiniteCompactSupport` with one `sorry`, and contains no new
definitions. It renders all three clauses of the unit, in the recorded
common-stage constructible Weil heart. It does not change the natural-language
statement or the reviewed proof split.

This is the repair of the returned immutable head 4d595ece6c30. The saved
statement is retained; the return concerns compilation of its dependency closure,
not a mismatch with the unit's mathematical statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The chapter's finite field and geometric Frobenius are `D : FiniteFieldDatum.{u}`;
  `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` supply the coefficient prime.
  `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]` are the algebraically closed coefficient field.
  Scheme and coefficient universes are independent.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` and `f₀ : X₀ ⟶ Y₀` express schemes and a
  morphism over the same base field. An Over morphism includes the structural
  commutative triangle; no extra compatibility is assumed.
- `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]` express finite type of the
  target, and `[QuasiSeparated Y₀.hom]` records the stated quasi-separatedness.
- `[IsSeparated f₀.left]` is relative separatedness. Neither structure map is
  assumed separated. `_hqf : Scheme.Hom.IsQuasiFinite f₀.left` is exactly the
  recorded Stacks predicate: locally finite type, quasi-compact, and every point
  isolated in its scheme-theoretic fibre. It includes the finite-type condition
  on the morphism; Mathlib's weaker LocallyQuasiFinite alone is not substituted.
- `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]` provide the source structures
  required to form the recorded Weil category. They follow from the finite-type
  morphism and target by composition and the Over triangle, and impose no new
  mathematical restriction. The published `zlSource_finiteType` and
  `zlSource_quasiCompact` state these consequences explicitly.
- `c : Compactification f₀.left` is arbitrary. It fixes the choice required by
  the existing compact-support construction. Such a compactification exists by
  the reviewed Zariski-main factorization. Quantification over every c, together
  with the published compactification-independence comparison, includes every
  compact-support realization; no finite choice or separated middle scheme is
  imposed on c.
- `F : sfCommonStageWeilSheaf D l hl X₀ Ω` is an arbitrary constructible Weil
  sheaf in the exact heart specified by def-weil-weil-sheaf-complex, not the
  derived category of pairs or an arbitrary discrete coefficient sheaf.
- `∀ i : ℕ, 0 < i → IsZero (zlWeilHigherShriek ... i F)` is precisely the
  positive-degree vanishing. This clause is outside the coefficient-embedding
  quantifier and therefore assumes no embedding or weight condition.
- `∀ (iota : Ω →+* ℂ) (w : ℝ)` allows any field embedding (injectivity follows
  for a unital map between fields), with no surjectivity or integrality of w.
- The first implication uses `SfIsMixedOfWeightsAtMost ... X₀ iota F w` and the
  identical predicate on Y₀ and `zlWeilHigherShriek ... 0 F`. This is the
  recorded finite filtration by Weil subobjects with pure quotients of real
  weights at most w, with the original embedding on both sides.
- The second implication quantifies over every closed source point and every
  eigenvalue α via `SfPunctualEigenvalue`, bounds `‖iota α‖` by
  `(Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)`, and concludes exactly
  the same inequality for every closed target point and every eigenvalue β of
  `zlWeilHigherShriek ... 0 F`. Residue-field cardinalities are finite and
  greater than one on finite-type schemes over the finite base field, so this
  inequality is equivalent to normalized weight at most w.
- In both weight conclusions, `zlWeilHigherShriek ... 0 F` is R⁰f₀!F, the
  f₀!F named by the unit. The degree-zero equality is definitional notation in
  the paper; it is not an equality between two independently chosen objects.

Dependency declarations read and reused:

- `Sheaf.Paper.WeilMixedUpperBounds`: the recorded
  `WeilConjectures.SfComplexIsMixedOfWeightsAtMost` and its cohomology/closure
  interface import the same `SfIsMixedOfWeightsAtMost` used here. The node also
  defines mixed sheaf bounds through that imported predicate.
- `Sheaf.Paper.AdicPunctualWeights`: `WeilConjectures.SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, and `SfIsMixedOfWeightsAtMost`. Their actual
  definitions were read: finite-stage geometric-Frobenius eigenvalues,
  embedding-based norm equality, and finite pure-quotient filtration.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`, the full subcategory
  of geometric-Frobenius fixed pairs with carrier in the actual common-stage
  standard heart; the complete definition and its Frobenius/forgetful interface
  were read. These declarations are publicly provided through the weight module.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`, read in full and used verbatim.
- `def-weil-pbc-scheme-conventions` is a convention-only record with no module;
  its recorded Mathlib scheme, separatedness, finite-type and quasi-separatedness
  properties supply the structures in the signature.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`, the recorded integral proper/open comparison
  on all finite-type schemes, with no absolute separatedness assumption. It
  reexports the integral/rational/common-stage values of
  `Sheaf.Paper.IntegralRationalQbarCompactSupport`, read in full at their signatures.
- `Sheaf.Paper.WeilCompactSupportCohomology`: `zlWeilHigherShriek`, whose
  representing-object definition and full signatures, compactification
  independence and compact-support comparison were read. It is the current
  published higher-image realization in the same Weil heart. The existing
  definition node is added to stmt_deps, along with the already landed
  def-weil-punctual-weights; no new node is needed. The import repair below preserves this predicate definitionally.

All available proof-dependency modules are imported non-publicly, including
base change, the exact finite-image and immersion statements, the closed-point
and dimension facts, and the upstream functor-package/Zariski-main modules.
Mathlib proof leaves supply affine opens, Noetherianity, and stability of finite,
open, separated and finite-type morphisms. The two proof-only nodes
lem-a1-finite-weil-sections-decomposition and
lem-zl-framework-pbc-open-exchange-comparison have no recorded module in the
base; they are not needed to type the statement and are not restated here.
The theorem's docstring includes all ten reviewed proof steps, including the
framework/PBC exchange compatibility, affine target restriction, finite-orbit
calculation for an arbitrary embedding, and the global mixed filtration.

Edge cases checked before writing: empty source and zero sheaf (all spectra
empty, the zero mixed filtration allowed), empty target, identity and a finite
morphism, a nonseparated target such as the doubled-origin line, nonreduced
finite fibres (the formula uses geometric stalks), orbit length one and a
nontrivial residue extension (β^e = α and q_x = q_y^e), negative and nonintegral
real weights, arbitrary nonsurjective coefficient embeddings, and arbitrary
scheme/coefficient universe levels. The vanishing clause is only i>0; no stronger
vanishing assertion, purity theorem, or exactness conclusion is added.

Searches for an existing statement:

- msearch leanfinder: “For a separated quasi-finite morphism compact support
  higher direct images of Weil sheaves vanish and degree zero preserves mixed
  and punctual upper weights”. Eight results about qcqs section and limit
  arguments; no matching Weil/coefficient statement.
- msearch loogle: `LocallyQuasiFinite, IsZero`. No hit (the public Loogle endpoint
  does not recognize the unqualified identifier).
- msearch loogle, qualified follow-up: `AlgebraicGeometry.LocallyQuasiFinite`.
  Twelve quasi-finite geometry declarations, no higher-image or weight theorem.
- msearch grep: `higherLowerShriek|SfIsMixedOfWeightsAtMost|sf.*quasiFinite`.
  Eleven Mathlib quasi-finite geometry results; no Weil-weight or higher-image
  statement.
- msearch leansearch: “For separated quasi-finite morphisms the higher
  compact-support direct images of constructible Weil sheaves vanish and degree
  zero preserves mixed and punctual upper weight bounds”. Eight scheme-property
  results, no matching coefficient/Weil theorem.
- rg on upstream `WeilConjectures`, the item's blueprint id, and
  `dag/lean_names_upstream.json` found the old `isZero_higherLowerShriek_of_quasiFinite`
  and the two `WeilSheaf` weight theorems. Read FormalSteps locally and fetched
  current QuasiFiniteVanishing and WeilSheaf.Category through `scompile --source`.
  These quantify over the old `AlgebraicGeometry.WeilSheaf` of constructible
  pro-etale Qbar module sheaves and its derived-of-Weil-sheaves construction,
  not the dependency's literal common-stage fixed-pair categories. Their
  signatures do not apply to `sfCommonStageWeilSheaf` or `zlWeilHigherShriek`;
  silently binding them would contradict the dependency's repaired record.
- rg on `lean/Sheaf/Paper` for quasi-finite weight or vanishing theorems found
  no theorem on the current common-stage categories. It found the required
  existing `zlWeilHigherShriek` and punctual/mixed definitions, all reused.
- The `same_as` node lem-zl-quasi-finite records the same old-model upstream
  declarations, rather than a statement on the published current category.

No STATEMENT-DISPUTED flag. The known source error in the old proof (a finite
compactification need not be separated over k₀) is already repaired in the
reviewed DAG route and is not used as an assumption of this signature.

## Dependency modules

`def-weil-punctual-weights`: the first compile fails while rebuilding
`Sheaf.Paper.AdicHeartPullbackFibres`, with “environment already contains
AlgebraicGeometry.Scheme.galoisFiniteUnit” from the two imported Galois modules.
The only import path from this delivery is WeilMixedUpperBounds →
AdicPunctualWeights → AdicHeartIntrinsicFibres → AdicHeartPullbackFibres.
The punctual predicates use AdicHeartIntrinsicFibres only for
`sfAdicCoefficientEmbedding`. Its full source definition is precisely
`L.val.subtype.comp (Shrink.algEquiv (Padic l) L.val).toRingHom`.
This delivery inlines that same canonical ring homomorphism at its sole use and
reduces the imports to LocalFrobeniusTrace, WeilIndSheafCategory, and the two
Mathlib modules used by the predicates. The removed imports are redundant for
these three definitions; their transitive declarations remain in their owning
modules. It neither duplicates nor replaces the
adic fibre construction. All three predicate definitions are definitionally
unchanged. The coefficient-model universe is retained by the explicit codomain
ascription on the ring homomorphism. The dependency node changes only in `lean`,
with the required note. The module's source and blueprint docstrings are retained.
Both this module and its consumer are compiled separately in dependency order.
Import-exposure audit: `ConstantExtensionWeilHeartEquivalence` explicitly uses
`sfAdicCoefficientEmbedding` through the former public reexport; its source will
need to import the owning fibre interface or inline this same canonical map when
it is rebuilt. It is outside this item's statement/proof dependency closure and
is not edited by this packet. `ExtensionByZeroPunctual` and `AdicSectionClosedSupport`
import the owning interface explicitly already. No declaration is removed from
its owning fibre module. This is recorded for the maintainer's independent
interface review.

## Self-check by NX (returned-delivery repair)

The first required dry run of the saved packet failed because
`CoefDerivedSystemEvaluationCalculus.lean` had no owning node in the packet.
Inspection against the current shared source showed that this file differed only
by a final blank line. The saved `ZlImmersionWeilLocalBehavior.lean` was also an
unrecorded experimental override, with import deletions and profiling options.
Both files are preserved under `scratchpad/retained-attempt/` and excluded from
the delivery. The original two recorded modules and their node records are retained.

The next prescribed `deliver2.py --no-push` passed compilation and server
preflight at commit 64fb74e595. The returned timeout in the published
`DerivedPullbackTensorHom.lean` dependency does not recur against the current
published library; no override of that module is included. The wrapper refreshes
and packages the delivery on current `newtargets-dag`; no direct git commands or
edits to the shared checkout were used.

Reread the unit statement, both delivered files and both node records, and the
current quasi-finite, fixed-pair heart, higher-image and canonical coefficient
embedding interfaces. The main signature still states exactly the three unit
clauses: positive-degree vanishing, the mixed upper bound, and the closed-point
punctual eigenvalue upper bound for every field embedding and real weight.
The finite-type source instances follow from the target and morphism hypotheses;
no absolute separatedness, surjectivity of the embedding, or extra weight
hypothesis enters the vanishing clause. Empty source, zero sheaf, identity,
nonseparated finite-type target, and negative or nonintegral weights remain
covered. The dependency repair substitutes the literal defining expression of
`sfAdicCoefficientEmbedding`, with the same coefficient universe, so all three
predicates are definitionally unchanged. The original full hypothesis/clause
correspondence and search record above still apply.

Mechanical self-check: the item differs from the current node only in `lean` and
the two added existing statement dependencies; the punctual-weight dependency
node differs only in `lean`. Both signatures occur verbatim in their files.
Every delivered module belongs to exactly one node. All Lean lines have at most
100 characters. Universes are explicit and `autoImplicit` is false.

The prescribed explicit `scompile.py` invocation on both modules, separately in
dependency order, passed with exit code 0 and no compiler diagnostics. Preliminary
compiles took 4.7/6.5 seconds; sandbox compiles took 4.9/6.1 seconds; library
compiles took 4.7/6.5 seconds, within the unchanged 60-second file limit.
This self-check is by the repairing worker; independent mathematical review
remains the maintainer's delivery review.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-19)

The §1(B) import repair of `Sheaf.Paper.AdicPunctualWeights` (def-weil-punctual-weights) is withdrawn again. The same fix was given on the returned head 4d595ece6c30; the landing returned that head only because the unrelated base side module `Sheaf/Paper/DerivedPullbackTensorHom.lean` timed out at 60 s (batch 20261018-213717). The fix restores the module byte-for-byte to its current newtargets-dag text, which keeps `sfAdicCoefficientEmbedding` and the public re-exports added there on 2026-10-19.
(1) The workaround is not needed. The side tree has only one `galoisFiniteUnit`, in `GaloisLisseRepresentations`. `WeilMixedUpperBounds`, which this item imports, now publicly imports `AdicHeartIntrinsicFibres` and `DerivedPullbackTensorHom` itself, so dropping the import from `AdicPunctualWeights` does not shrink the item's closure. The item compiles clean against the live module: 5.1 s for the dependency and 5.5 s for the item.
(2) The delivered text is based on an older base. Landing it would delete about 35 public imports that were added to the live module after that base, and it would replace the named canonical `sfAdicCoefficientEmbedding` with an inlined copy of its body.
All three predicates are definitionally unchanged, so the item statement is unaffected. The dependency record's lean.note about the import repair is obsolete. Landing with `--revert-nodes def-weil-punctual-weights` gives the same Lean and keeps Q52's record.
