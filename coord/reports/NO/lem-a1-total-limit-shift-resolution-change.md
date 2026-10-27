## Worker report

The module `Sheaf.CategoryTheory.TotalLimitShiftResolutionChange` states
`CategoryTheory.totalLimitShiftResolutionChange`, with `sorry`. It also states the
additivity fact `CategoryTheory.ringedTowerLimit_additive` used to type the canonical
limit homotopy and shift constructions; this has `sorry` and is registered as a
public instance. This is the additivity assertion proved by step 1 of this same
node, not a new construction or an independent notion. Both declarations have
source and blueprint docstrings and complete natural-language proof plans.
No definition contains postponed data. No node statement was changed.

Hypotheses and clauses, in order:

- The site is `{C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)`.
  `[EssentiallySmall.{r} C]` expresses smallness relative to the module universe,
  allowing any presentation of such a site. The usual Mathlib sheafification and
  locally-bijective-equivalence instances are explicit. Site object and morphism
  universes remain independent of each other and of the coefficient universe.
- `R : Sheaf J RingCat.{r}` and `_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U),
  a * b = b * a` express a sheaf of commutative rings using the recorded
  `ringedSiteModules.{r, r, vC, uC} R` interface. The helper's more general
  noncommutative additivity fact needs no commutativity.
- A is exactly `ringedSiteModules.{r, r, vC, uC} R`, the recorded transparent
  abbreviation for Mathlib's `SheafOfModules`. T is `ℕᵒᵖ ⥤ A` with the
  levelwise abelian structure `CategoryTheory.Abelian.functorCategoryAbelian`.
  Natural index n represents the positive index n+1: this is the reindexing
  explicitly allowed by the tower-category dependency's Mathlib match.
- `[HasDerivedCategory.{wA} A]` and `[HasDerivedCategory.{wT} T]` fix the two
  unbounded localizations. Their morphism universes are independently quantified;
  no equality of universe choices is imposed. Complexes are cochain complexes
  indexed by all integers, with Mathlib's signed cochain shifts.
- The ordinary limit is exactly `(lim : T ⥤ A)` and its degreewise extension is
  `lim.mapHomologicalComplex (.up ℤ)`, with its type written in full in the file.
  No separate limit, tuple construction or private alias was introduced.
- The supplied `L : DerivedCategory T ⥤ DerivedCategory A`, the transformation
  `η : lim.mapHomologicalComplex (.up ℤ) ⋙ Q_A ⟶ Q_T ⋙ L`, and `_hL :
  L.IsRightDerivedFunctor η (HomologicalComplex.quasiIso T (.up ℤ))` retain
  ANY total right-derived pair. This is the chain-level presentation supplied by
  the strict-tower dependency, equivalent to the homotopy-category presentation
  of `def-sfb-right-derived-functor` by the canonical quotient factorization.
  The chosen-pair dependency is imported; its chosen functor is not substituted
  for the arbitrary L required here.
- K-injectivity is always Mathlib's `CochainComplex.IsKInjective`, whose definition
  is precisely null-homotopy of maps from acyclic complexes. There is no hypothesis
  that the degree terms are injective, no boundedness, and no exact-products
  assumption anywhere in either signature.
- The first conjunct quantifies every tower homotopy H and states
  `(lim.mapHomotopy H).hom i j ≫ limit.π (Y.X j) (op n) =
  limit.π (X.X i) (op n) ≫ (H.hom i j).app (op n)`.
  `Functor.mapHomotopy` is the actual additive-functor construction, with degree
  homotopy maps `lim.map (H.hom i j)`. This gives the stated limit homotopy,
  characterized uniquely by the jointly monic limit projections.
- Lambda is the EXISTING canonical `commShiftIso s` of the degreewise limit
  functor (instance `Functor.commShiftMapCochainComplex`). The second conjunct
  explicitly gives `lambda.hom.f i = 𝟙 _`, so it is identity on compatible tuples,
  not an arbitrary isomorphism. Source and target objects in that equality are
  definitionally the same degreewise limit. Mathlib's construction already
  supplies its chain condition, inverse, and coherent shifts.
- The third conjunct quantifies all tower chain maps v, without K-injectivity
  restrictions, and gives `lim(v[s]) ≫ lambda_J = lambda_I ≫ (lim v)[s]`.
  This is exactly the node's naturality square in diagrammatic composition order.
- `∃ d : ∀ (X I) (q : X ⟶ I) [QuasiIso q] [I.IsKInjective],
  Q_A.obj (lim I) ≅ L.obj (Q_T.obj X)` supplies the resolution isomorphism
  for EVERY q. Simultaneous choice of this uniquely characterized family is
  equivalent to the pointwise unique-existence assertion in the node.
- Its first property is `(d X I q).hom ≫ L.map (Q_T.map q) = η.app I`, exactly
  `L(Q_T q) ∘ d_q = eta_I`. Every other isomorphism e with this normalization
  equals `d X I q`; thus uniqueness is included explicitly.
- For two arbitrary resolutions q,q', its next property supplies
  `∃ v : HomotopyEquiv I I', Nonempty (Homotopy (q ≫ v.hom) q')`.
  It then quantifies EVERY such homotopy equivalence and states
  `Q_A.map (lim v.hom) ≫ (d X I' q').hom = (d X I q).hom`.
  Consequently the value does not depend on a representative of that homotopy
  class. The preceding actual limit-homotopy construction also transports any
  homotopy between representatives. No preferred v is selected in the statement.
- The next property states `QuasiIso (q⟦s⟧') ∧ (I⟦s⟧).IsKInjective` for
  every integer s and every resolution q. The shifted map really has source
  X[s] and target I[s], so this is exactly the shifted-resolution assertion.
- Finally `∃ c : L.CommShift ℤ` supplies natural isomorphisms for EVERY derived
  object and EVERY derived morphism, with zero and addition coherence as the
  fields `commShiftIso_zero` and `commShiftIso_add`. It does not limit naturality
  to localized strict chain maps. The final equation holds simultaneously for
  every q and s:
  `d_(q[s]) ; L(Q_T shift_X) ; c_(Q_T X) =
   Q_A(lambda_I) ; Q_A-shift_(lim I) ; d_q[s]`.
  Composing on the left with the inverse of d_(q[s]) gives precisely the node's
  beta formula, with the explicit canonical localization-shift identifications.
  The SINGLE c valid for ALL q proves resolution independence of that formula.
  Its natural-isomorphism and CommShift fields give naturality for arbitrary
  derived tower morphisms and coherence for zero and addition of integer shifts.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules` and its standard abelian instance, from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`,
  `CategoryTheory.Abelian.functorCategoryAbelian`; the recorded evaluation
  preservation and levelwise mono/epi clauses were read in
  `Limits.FunctorCategory.Basic` and `Limits.FunctorCategory.EpiMono`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its localization and shift instances.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit,
  universal property, uniqueness, unit-isIso theorem and resolution comparison.
  The generic `Functor.IsRightDerivedFunctor` is used to retain an arbitrary pair.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
  Its full signature provides the exact chain-level universal pair and
  computation on all K-injectives without exact-products assumptions.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective` and its shift instance.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`, the recorded proof dependency
  `lem-weil-pbc-kinjective-hom-derived`, and `IsKInjective.quasiIso_iff`.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`,
  `CategoryTheory.Functor.kInjectiveDerivedMapComputation` (proof import).
- The existing Mathlib constructions `Functor.mapHomotopy`,
  `Functor.mapCochainComplexShiftIso`, `Functor.commShiftMapCochainComplex`,
  `Functor.mapHomologicalComplex_commShiftIso_hom_app_f`, and
  `Functor.CommShift` were read in full and are reused, not redefined.

Sources read locally: `literature/stacks-project/derived.tex`,
`lemma-K-injective` (070I), `lemma-K-injective-defined` (070Y) and
`lemma-enough-K-injectives-implies` (070K), together with all seven proof steps
of the node and the complete dependency records/signatures/docstrings.
The limit and signed-shift calculations are the explicit agent refinement named
by this node's source, not claimed to be a separate Stacks lemma.

Edge cases checked before and after writing:

- X=0 and zero resolutions: the unique normalized isomorphism is the zero-object
  isomorphism, and the homotopy and shift equations remain typed.
- Identity resolution of any K-injective I: normalization gives d_id=eta_I.
  The identity homotopy equivalence compares it with itself.
- s=0: the formula reduces under the canonical zero-shift maps to the comparison
  followed by its inverse; the CommShift zero law records exactly this.
- s=-1 and positive/negative shifts: all indices are ℤ and no bounds occur.
  The canonical cochain shift incorporates the (-1)^s differential sign.
- s+t=0 and arbitrary sums: included in the CommShift addition law, with both
  localization shift identifications displayed in the computation formula.
- K-injectives without injective degree terms: only `I.IsKInjective` appears.
  A homotopy-equivalent non-injective-term presentation is not excluded.
- Empty sites and the zero sheaf of rings: no nonemptiness or nontriviality
  condition was added. The tower index is intrinsically countable and nonempty,
  exactly as in the node.
- A ringed site where countable products are not exact: neither a
  `HasExactLimitsOfShape` nor an AB4-star assumption appears. Ordinary limits
  and K-injective computation suffice.
- Independent site and coefficient sizes, and independent wA,wT localizations:
  no universe equality or artificial size increase restricts the statement.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Termwise inverse limit shifts computed on any
  K-injective tower resolution are independent of resolution and natural for
  derived morphisms"`: eight hits on bounded-below `InjectiveResolution`
  comparison naturality. None states the arbitrary unbounded K-injective
  tower-limit statement with normalization, homotopies and coherent shifts.
- `msearch.py ... loogle "CochainComplex.IsKInjective,
  CategoryTheory.Functor.CommShift"`: OK, zero hits.
- `msearch.py ... grep "limit.*commShift|commShift.*limit|limit.*KInjective|
  KInjective.*limit" Algebra/Homology`: OK, zero hits.
- `msearch.py ... leansearch "Canonical total right derived inverse limit shifts
  are independent of arbitrary K-injective resolutions and natural for all
  derived morphisms"`: eight hits, principally bounded-below comparisons and
  `Functor.totalRightDerived`. None is the exact statement.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` with
  `limit.*[Ss]hift|[Ss]hift.*[Ll]imit|[Tt]otalLimitShift|lem-a1-total-limit-shift-resolution-change`:
  related Roos and integral-operation shift modules, not this statement.
  In particular `NormalizedRoosShiftComparison` was opened: it has an exact-products
  hypothesis, cone/Roos data and a prescribed cone comparison; this node concerns
  the pure total-limit shift with no exact-products assumption. No declaration
  tagged with this item already existed.
- Local Mathlib source searches found the exact homotopy and canonical additive
  cochain-shift constructions above, which are used directly. Source searches
  for limit additivity showed it is only established locally inside the
  strict-tower proof; no public reusable instance was available. An initial
  module-mode server `#synth lim.Additive` confirmed this missing instance.
  The step-1 additivity theorem supplies it without an added hypothesis.

No `STATEMENT-DISPUTED` flag, correction, new node, or dependency repair is needed.
The earlier reported stale-assignment blocker was checked: the live node had
stage-1 `reviewed` only and no `lean`/`reviewed_lean`; this stage-2 delivery is new.

Validation: the complete single module was compiled by the prescribed server
`scompile.py` wrapper. Only stage-2 `sorry` proofs are present. The delivery dry
run and its server preflight are recorded below after execution.

Dry run: `deliver2.py NO lem-a1-total-limit-shift-resolution-change --no-push`
returned `OK (dry run): commit 505e4190395 passes the preflight and compiles;
nothing pushed`. The staged packet had exactly this report, the item's node
(changed only in `lean`), and its one Lean module. The node signature was also
checked byte-for-byte against the module; both declarations use `sorry`, all
variables and universes are explicit, and the maximum Lean line width is 99.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
