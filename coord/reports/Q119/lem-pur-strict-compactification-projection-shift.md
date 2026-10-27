## Worker report

The module `Sheaf.SixFunctors.StrictCompactificationProjectionShift` states
`WeilConjectures.IntegralSystemRealization.strictCompactificationProjectionShift`.
Its only postponed proof is this named theorem, with the five-step DAG proof in its
docstring. Five helper definitions compose existing isomorphisms; they contain real
data, no choice and no postponed proof. The original mathematical statement and
accepted split are unchanged. There is no statement dispute or dependency repair.

Hypothesis and clause correspondence:

- The global field is `D : FiniteFieldDatum.{u}`. Its `p`, `q`, `k₀`, `k`, primality,
  cardinality and algebraic-closure fields are precisely the finite-field convention.
  `l : ℕ`, `[Fact l.Prime]` and `_hl : l ≠ D.p` give the distinct coefficient prime.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]`
  give the finite extension. The valuation ring, uniformizer, positive quotient
  rings and quotient maps are those built into `System l E W`; system index `n`
  represents exponent `n+1`, so all and only positive exponents occur.
- `X Y : Scheme.{u}` with their `Over (Spec (.of D.k))` structures are the two
  k-schemes. `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on both structure
  maps give separated finite type over k. `f`, `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, `QuasiCompact f` render exactly the stated k-morphism.
- `d : Compactification f` supplies `d.i`, `d.Z`, `d.g`, open immersion, properness,
  and `d.comm : f = d.i ≫ d.g`. The open is quasi-compact by the existing
  `Compactification.quasiCompact_openImmersion_iff` and `[QuasiCompact f]`; this
  does not require a further assumption or a new compactification notion.
- `System l E W` is the existing `coefficientSequenceDerived l E W`, the ordinary
  unbounded derived category of modules on the small pro-etale vertical sequence
  site, with the actual quotient ring sheaf. Arbitrary `M`, `N` (and intermediate
  `Q`) in these categories impose no normalization, boundedness or Tor restriction.
- `o : Operations l E`, `c : Compositors l E o`, `a : OpenComparisons l E o c`
  supply precisely the simultaneous models fixed in the node. They are the
  presentation data of the recorded realization theorem, not a new assumption
  about input objects. Their ordinary/derived factorization, adjunction-transpose,
  and open-unit equations specify the maps; no square to be proved is a hypothesis.
- P is `pull l E v`, S is `Operations.push l E o v`, J is
  `Operations.shriek l E o j`, tensor is `(calculus l E W).systemClosed.tensor`.
  `compactificationProjection l E o c a d M N` is reused verbatim: proper mate at
  `J M`, then `S` of the open comparison, then `S J` of tensor with the inverse
  pullback compositor and transport by `d.comm`. No arbitrary map replaces it.
- The canonical shifts are the published `systemPullShift`, `systemPushShift`,
  `systemOpenShift`, `(systemShifts l E o).compactSupport`, and
  `(tensorShifts l E).systemRight`. The latter is characterized by
  `systemTensorRightProperty` and `systemTensorRightFormula`, with coefficient
  `(r * i).negOnePow` on a summand of first degree `i`. Helper
  `strictTensorPullShift` composes pullback shift and this signed tensor shift.
  `strictProperTargetShift`, `strictOpenTargetShift` and
  `strictCompactificationTargetShift` then apply S, J and S J, respectively,
  followed by their specified shift comparison.
- Conjunct 1 is exactly PF(M,N[r]) followed by s_H = s_F followed by PF(M,N)[r].
  Its quantified `r : ℤ` includes every integer. Conjunct 2 is the proper factor
  square, even for arbitrary `Q : System l E d.Z`. Conjunct 3 is the open factor
  square, for arbitrary second input on the ambient compactification. Mapping and
  precomposing these gives the middle factor in conjunct 1. Conjunct 4 is the
  canonical pullback-composition square; `strictCompactificationPullComp` is
  `(c.pullComp d.i d.g).symm` followed by the actual compactification equation.
  Tensoring and applying J and S gives the last factor in conjunct 1.
- All four equations are hom equalities in `System`, before evaluation, scalar
  restriction and total inverse limit. Their actual coefficient transitions are
  part of their morphism types. Normalized bounded constructible finite-Tor inputs
  are included by the unrestricted object binders; this is a special case, not
  an additional condition. There is no `IsIso` conclusion for PF or the proper mate.

Dependency declarations read and used (their source signatures and docstrings were
read, not merely the declaration names):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient-extension
  constructions through its public import and `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties` is a convention record with no declaration:
  its existing Mathlib `Scheme`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsOpenImmersion`, `IsProper` interfaces are used directly.
- `WeilConjectures.Compactification.RefinementCategory`: underlying
  `AlgebraicGeometry.Compactification` from `Compactification.Defs`, its open/proper
  fields and quasi-compact-open equivalence. Refinements are not part of this item.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, the `Systems`/`DS` sequence-site interfaces.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and the existing localization/shift instances.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `integralCompactificationSystemRealization`, `Realizations`, `properProjection`,
  `compactificationProjection`; public operation data `Operations`, `Compositors`,
  `OpenComparisons`, `System`, `pull`, `calculus` from `IntegralSystemOperations`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `mapBifunctorShift₂Iso`, the signed convention reused by the published shift data.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`,
  whose canonical normalization and proper-mate square supply proof steps 1–2.
- `Sheaf.SixFunctors.OpenTensorNormalization`: `SheafOfModules.openTensorNormalization`,
  with `Operations`, `Assertion`, the normalized `gamma` and its inverse transpose.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`,
  `ExchangeProjectionStage`: exactly the same counit/proper/open composite already
  specialized by `compactificationProjection`.
- `Sheaf.Paper.NormalizedDVRTower`: `WeilConjectures.NormalizedDVRTower` (only the
  included special case, not a premise), and `Sheaf.Paper.FiniteTorAmplitudeSites`:
  finite-Tor constructibility interfaces (likewise not extra premises).
- `Sheaf.SixFunctors.OpenSystemTensorShift`:
  `SheafOfModules.OpenTensorNormalization.open_system_tensor_shift`, for proof step 3.
- `lem-weil-pbc-commshift-nattrans-comp-whisker` is a Mathlib leaf, not missing Lean:
  its `mathlib_match` lists `NatTrans.CommShift.id`, `.comp`, `.whiskerRight`,
  `.whiskerLeft`, `.associator`. Read in `Mathlib.CategoryTheory.Shift.CommShift`,
  lines 406–426, and imported for the pasting proof.

The one added statement dependency is the already-landed definition node
`def-pur-integral-operation-shift-data`, owning
`Sheaf.SixFunctors.IntegralOperationShiftData`. Its declarations give the canonical
shifts already called for in the original statement: `tensorShifts`,
`systemTensorRightFormula`, `systemTensorRightProperty`, `systemPullShift`,
`systemPushShift`, `systemOpenShift`, `systemShifts`. This is permitted by the
landed-node addition rule of brief-stage2 §5. No new node or duplicate definition
is created. A traversal of its statement/proof dependency closure found no path
back to this item, so the added dependency creates no cycle.

Edge cases checked against the source and signature: r=0 has sign 1 and identity
comparison; r=1 and odd first degree gives sign -1 on both paths; r=-1 and all
negative shifts are retained. Zero M or N and empty source/open are allowed by
all object binders. Proper-only and open-only compactifications, including both
identity maps, are admitted by `Compactification.ofIsProper` and `.ofIsOpenImmersion`.
No flatness of quotient transitions, boundedness or degree concentration was added;
nonflat R/t^(n+1) to R/t^n remains the actual system. The small site retains object
universe u+1 and morphism universe u. The existing realization interface uses
Scheme.{u} and E : Type u, with modules in u+1; no equality of the two site sizes
was imposed. Independent coefficient/site universes are not quantified in this
item's supplied simultaneous-model interface and are not changed here.

Searches actually run using msearch.py, all for this item and group:

- leanfinder: `The projection map for compact support on derived strict semilinear
  inverse systems commutes with shifts in the second argument`: 8 hits, all unrelated
  LightProfinite/Profinite transition results; no exact statement.
- loogle: `CategoryTheory.NatTrans.CommShift, CategoryTheory.Adjunction`: 4 hits,
  `Adjunction.CommShift.commShift_counit`, `.commShift_unit`, `.mk'`, `.mk`;
  generic tools, no strict-system compactification projection result.
- grep: `projectionMap|CommShift`, directory `CategoryTheory/Adjunction`: 0 hits.
- leansearch: `Proper open compactification projection formula transformation for
  strict coefficient systems commutes with shifts`: 8 hits, generic NatTrans.CommShift,
  exact-derived functor and cochain-shift tools; no exact statement.
- Local rg of `strict.*[Cc]ompactification|compactification.*[Ss]hift|strictCompactification|
  projection.*[Ss]hift` in project Paper and upstream sources found the integral
  AdicProjectionShiftCoherence and generic ProjectionMapShift, both different domains.
  Focused rg of `strictCompactificationProjectionShift|compactificationProjection.*shift|
  properProjection.*shift` in Sheaf and WeilConjectures had no match. The required
  grep for this node id in WeilConjectures had no match. Subsequent searches found
  and reused IntegralOperationShiftData; no new tensor or primitive shift was written.

Source read: latest blueprint `sk-thm-purity-transport/_section.md` and its proof,
Step 2. The node expands the strict-system calculation supporting that step;
it is not the unit's own statement. The five accepted proof steps of the DAG were
preserved and included in the theorem docstring. No internet source was needed:
the blueprint and pinned Mathlib/project sources are available locally.

Validation: scompile.py compiled this module in both sandbox and final library
contexts cleanly (19.1s and 6.4s respectively on the initial compile). The final
module and node record are then checked by deliver2.py --no-push before delivery.

The completed dry run printed `OK (dry run): commit beb8d0b2e2c passes the
preflight and compiles; nothing pushed`. The local Stacks tag map and source
were also checked directly: sites-cohomology.tex lines 3658–3730 (0D6D and 07A4),
4578–4592 (0GL1), and 13660–13689 (0B56). They use the same unbounded inputs,
ordinary open-unit comparison, counit mate, and representative pullback compositor;
the following projection-isomorphism theorem's perfectness assumption is not
imported into this shift statement.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
