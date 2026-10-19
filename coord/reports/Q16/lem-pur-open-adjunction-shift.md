## Worker report

The module `Sheaf.SixFunctors.OpenAdjunctionShift` states
`WeilConjectures.IntegralSystemRealization.openAdjunctionShift`. Its only theorem has
`by sorry`; no mathematics is proved and no new notions or nodes are introduced. The delivery uses the current published dependency modules unchanged.

Hypothesis and clause correspondence:

- The algebraic closure of a finite field is `D : FiniteFieldDatum.{u}` with field `D.k`.
  The prime is `(l : ℕ) [Fact l.Prime]`, and `_hl : l ≠ D.p` is the distinct-characteristic
  assumption. The finite coefficient extension is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The valuation ring, uniformizer and quotients are the existing
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and
  `coefficientExtensionRing l E (n+1)`, used by the imported coefficient system construction.
  Natural index n encodes the positive exponent n+1; the quotient with exponent zero is
  not inserted. No new coefficient object or alternative uniformizer is selected.
- Finite-type k-schemes are `U W : Over (Spec (CommRingCat.of D.k))`, with
  `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom]` and the same two instances for W.
  The morphism `(j : U ⟶ W)` is over k by its type; `[IsOpenImmersion j.left]` and
  `[QuasiCompact j.left]` give exactly the stipulated quasi-compact open immersion.
- The small pro-etale sites, strict semilinear module systems and ordinary unbounded
  derived categories are those underlying `IntegralSystemRealization.System l E` =
  `coefficientSequenceDerived l E`, defined using `coefficientSequenceModules` on
  `coefficientSequenceCommRingSheaf` and `coefficientSequenceTopology`. The object
  universe of the site is u+1 and its morphism universe is u; these are not equated.
  The recorded reduction/limit calculus is imported, with its actual completed ring,
  reconstruction and total limit. The statement does not apply evaluation or limit.
- `o : Operations l E` names the simultaneous operations stipulated in the realization
  dependency. It is presentation data for the functors already named in the informal
  statement, not a new exactness or shift-compatibility hypothesis. Their existence is
  the conclusion of `integralCompactificationSystemRealization`. The theorem applies to
  every such presentation and hence in particular the recorded realization.
- `o.extension j.left` is the existing exact ordinary system open extension, with
  ordinary adjunction to `pullbackTensorSequenceInverse l E j.left`.
  `(o.extension j.left).derived` is J and `pull l E j.left` is P. Their specified
  localized adjunction is `(o.extension j.left).adj`, using
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`.
- Both `Functor.CommShift ℤ` instances are the existing ones for `mapDerivedCategory`,
  induced from termwise cochain shifts by localization. No arbitrary comparison or
  comparison chosen from the adjunction is supplied.
- The conclusion `((o.extension j.left).adj).CommShift ℤ` is Mathlib's conjunction of
  `NatTrans.CommShift` for the unit and counit. It says, for every integer a, naturally
  in X and Y, eta at X[a] followed by the composite shift comparison equals eta_X[a],
  and the composite shift comparison followed by epsilon_Y[a] equals epsilon at Y[a].
  These are maps of `coefficientSequenceDerived`, before finite evaluation, restriction
  of scalars or total limit. Thus neither faithfulness of derived evaluation nor a lift
  of finite-level maps is asserted or assumed.

Dependency declarations read and used:

- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`,
  `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`;
  its `IntegralSystemOperations` interface supplies `Operations`, `Open.ordinary`,
  `Open.adj`, `Open.derived`, `pull` and `System`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`,
  `SheafOfModules.localizedSystemExact`, `localizedSystemExtension`,
  `localizedSystemRestriction`, `localizedSystemAdjunction`: the levelwise exact,
  section-normalized extension/restriction adjunction. This is proof input; the
  simultaneous functors themselves are already supplied by the realization interface.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`, with its sequence-site
  categories, actual reduction and total limit. These fix the ambient systems, rather
  than a category of diagrams in finite derived categories.
- Proof dependencies are imported: `CoefficientRingedSequenceSite`,
  `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`, Mathlib module
  sheafification and restriction of scalars, `DerivedCategory.ExactFunctor`, and
  `CategoryTheory.Shift.Adjunction`. The latter contains all the clauses of
  `lem-weil-pbc-adjunction-shift-compatibility-unique`; `Adjunction.CommShift` is read
  directly there. The current published sequence-site interface is used unchanged.

The docstring follows the three proof steps of the DAG: the levelwise localized-site
adjunction and its compatibility with scalar restriction; the signed degreewise shift
calculation and localization; then the observation that these are system equalities
before evaluation/limit. The actual sequence site has no single object representing
U in every degree, so no localization at such an object is attempted.

Edge cases checked: the identity open gives its identity equivalences; the empty open
has zero source category and zero extension, so the same natural-transformation squares
are valid; zero complexes impose no extra nonzero hypothesis. Shifts range over all
integers, including zero and negative integers, not only nonnegative shifts. There is
no normalization, constructibility, boundedness or Tor-amplitude restriction on system
complexes in this assertion.

Searches for existing statements (2026-10-18):

- msearch leanfinder: `open extension by zero restriction derived adjunction unit counit
  commute integer shifts`; eight generic hits, including CompatibilityUnit,
  CompatibilityCounit and the unit/counit commShiftIso formulas. None specializes to
  the system open adjunction.
- msearch loogle: `CategoryTheory.Adjunction.CommShift, CategoryTheory.NatTrans.CommShift`;
  four hits, the generic class fields and constructors, not this assertion.
- msearch grep: `commShift_mapDerivedCategoryAdjunction|open.*CommShift` in CategoryTheory;
  only generic Shift/Adjunction and unrelated opposite-shift declarations.
- msearch leansearch: `extension by zero derived adjunction shift compatibility`;
  eight generic adjunction shift hits, no coefficient-system open specialization.
- rg in upstream `WeilConjectures` and side `lean/Sheaf`: open adjunctions exist,
  particularly the exact system `Open.adj` used here; no open-system shift assertion.
  Name searches for `openAdjunctionShift|openAdjunctionCommShift` across Mathlib,
  upstream and side sources find no declaration. Upstream blueprint-id grep gives
  no match. The upstream DAG name index gives no match for the proposed name.
- Read upstream `CategoryTheory/DerivedCategory/MapDerivedCategoryAdjunctionShift.lean`:
  its instance concerns a differently constructed generic derived adjunction and
  imposes auxiliary monoidal and resolution assumptions. It is useful proof guidance,
  not an exact existing statement of this node; it is not rebound as this node.

No statement correction, disputed statement or new node is needed.

## Second reading by Q16

Author self-check, as required by the dispatcher; the maintainer supplies the independent
review. Reopened the node and the Lean module and compared each binder and both class
fields. The finite field and coefficient data, finite-type base objects, over-base open
morphism, quasi-compactness, whole strict-system derived categories, fixed exact-functor
shift structures, and both natural unit/counit equations are represented as above. In
particular the typeclass conclusion is a proposition to prove, not an assumed instance.
The presentation binder names the dependency's existing operations and introduces no
assumption of the desired compatibility. No finite evaluation occurs in the conclusion.
No mismatch requiring a node correction was found.

## Current-source self-check

The required initial dry run tested the saved packet before any investigation was
restarted. Its stale dependency repairs exposed compilation failures. A separate
file-only compile against the current published library established that those
repairs are no longer required: the original sequence-site module already contains
the canonical coefficient-universe sheafification witnesses needed downstream.
The saved replacements changed generated helper names used by already published
modules; retaining them would introduce a regression.

Retired all four dependency modules and their lean-only node copies from the
delivery, retaining the work under scratchpad/retired-packet for reference.
Restored the item's original statement-dependency list and removed the three
imports that were added solely for those repairs. The theorem and canonical
restriction shift instance remain unchanged. This delivery now contains only the
item's Lean module, its lean-only node record, and this report.

Reopened the current `IntegralSystemOperations` declarations `System`, `pull`,
`Open.ordinary`, `Open.derived`, `Open.adj`, and `Operations`, the realization
theorem, the localized-system exact adjunction module, the blueprint coherence
source paragraph, and Mathlib's `Adjunction.CommShift`. The localized adjunction
and both termwise shift comparisons are exactly the dependency's existing ones.
The proposition contains the unit and counit shift squares before evaluation.
The recorded signature matches the Lean file verbatim; auto-bound implicits are
disabled and every line is within 100 characters.
