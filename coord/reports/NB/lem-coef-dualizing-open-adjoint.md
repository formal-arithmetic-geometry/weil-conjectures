## Worker report

The delivery states `lem-coef-dualizing-open-adjoint` in
`Sheaf.Paper.CoefficientDualizingOpenAdjoint`. The only postponed theorem is
`AlgebraicGeometry.Etale.coefDualizingOpenAdjoint`; its proof is `sorry`.
Every helper is public and has real data. No definition contains `sorry`.

The live Q65 record is a stage-1 split, not a stage-2 Lean delivery: its report explicitly
says “no Lean attachment”, and the node has no `lean` or `reviewed_lean` record.
There is no repair note for this item. Thus the previous duplicate-delivery objection
does not apply. The statement, proof, proof dependencies, source, status and stage-1
review metadata are preserved verbatim. Four already-landed notions are added to
`stmt_deps`, as authorized by brief-stage2 section 5.

### Hypotheses and objects

- `P : WeilConjectures.PurityFiniteSetting.{u}` contains exactly the finite-field datum,
  coefficient prime distinct from p, coefficient algebraic closure, finite extension E,
  and positive level n. Its `field : FiniteFieldDatum` fixes k as the algebraic closure
  of the finite field, and `coefficients.different` is ell != p.
  Its extension is an actual finite intermediate field in that coefficient closure.
  No ramification-divisibility, smoothness, regularity or projectivity condition is used.
- `P.level` is n, `m : ℕ`, `hm : 1 ≤ m`, `_hmn : m ≤ P.level` give exactly 1 <= m <= n.
  The theorem keeps the relation although the adjunction assertions themselves do not
  require it; `coefDualizingOpenReduction` uses it to construct the actual quotient map.
- A is `P.Coefficient`, the existing universe lift of O_E/(varpi^n).
  B is `({ P with level := m, level_pos := hm }).Coefficient`, the same field extension
  and uniformizer at level m. These are existing quotient rings, not arbitrary rings
  or new coefficient data. The lift is the standard small-etale size convention.
- `Y U : Scheme.{u}`, `aY : Y ⟶ Spec (.of P.field.k)`, `[IsSeparated aY]`,
  `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]` give the separated finite-type
  k-scheme and its named structure morphism. `j : U ⟶ Y`, `[IsOpenImmersion j]`,
  `[IsAffine U]` give an affine open subscheme, including the empty open.
  The structure map of U is exactly `j ≫ aY`.
- `DerivedCategoryModule R T` is the ordinary unbounded derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} R)`. Nothing is transported to
  pro-etale categories or to O_T-modules.

### Every conclusion and normalization

1. `CoefDualizingOpenAdjointStatement` includes `QuasiCompact j ∧ IsSeparated j ∧
   Etale j ∧ LocallyOfFiniteType j`, exactly the geometric clause. Its internal
   instance terms are already-proved Mathlib deductions, not additional hypotheses:
   `LocallyOfFiniteType.isLocallyNoetherian aY`,
   `QuasiCompact.compactSpace_of_compactSpace aY`, and
   `isLocallyNoetherian_of_isOpenImmersion j`. Existing Mathlib and Nagata instances
   then provide the required quasi-compactness and structural compactifications.
2. `F_Y` is `rightDerivedLowerShriek (ModuleCat R) aY`, the canonical chosen
   compactification's `Rr_* Dv_!`; `F_U` is that same construction at `j ≫ aY`.
   `G` and `H` in `CoefDualizingOpenCounitStatement` range over the actual right
   adjoints with supplied structural adjunctions `adjY` and `adjU`. This represents
   arbitrary choices of the structural right adjoints, not arbitrary comparison maps.
   Their existence is already the exceptional-adjoint theorem. No adjoint-compatibility
   hypothesis is added.
3. `omega_Y` is `G.obj (constantComplex R S)` and `omega_U` is
   `H.obj (constantComplex R S)`, with `S = Spec k`. `constantComplex R S` is R_s.
   The structural counits are precisely `adjY.counit.app (constantComplex R S)`
   and `adjU.counit.app (constantComplex R S)`.
4. The open functor is exactly `(openImmersionLowerShriek (ModuleCat R) j).
   mapDerivedCategory`, and its evaluation counit e is the actual
   `derivedOpenImmersionLowerShriekUpperStarAdjunction` counit, obtained degreewise
   from the specified open sheaf adjunction. This is not a supplied morphism.
5. `coefDualizingOpenNormalization` identifies canonical Rj_! with this termwise
   open functor using `Compactification.ofIsOpenImmersion j`, i.e. (j, identity),
   `rightDerivedLowerShriekIso`, the derived direct-image identity isomorphism,
   and the functor right unitor.
6. `coefDualizingOpenLeftIso` is the inverse open normalization whiskered by F_Y,
   followed by `unboundedEtaleLowerShriekCompIso R j aY`. Its inverse is exactly
   F_U ~= F_Y j_! as written in the node. This is a defined canonical natural
   isomorphism, not a bare existence assertion.
7. `coefDualizingOpenRightIso` composes the open evaluation and structural
   adjunctions with `Adjunction.comp`, transports along that specific left iso,
   and applies `Adjunction.rightAdjointUniq`. Its component at R_s is exactly
   j^* omega_Y ~= omega_U. Both directions are actual morphisms with inverse laws.
8. `CoefDualizingOpenCounitStatement` asserts the source's counit equality at R_s,
   with the identifications written explicitly. Its left side is
   F_U(theta_Rs) followed by epsilon_U. Its right side is beta^{-1} followed by
   F_Y(e_omegaY) followed by epsilon_Y. Both sides start at
   F_U(j^* omega_Y) and end at R_s. Canceling beta is precisely the displayed
   formula in the node, under its left and right identifications.
9. `coefDualizingOpenLeftPlusIso` is the ordinary bounded-below identification
   J_plus F_Y_plus ~= F_U_plus. Its first factor is the inverse of the actual
   canonical open normalization: `rightDerivedLowerShriekOfCompactificationPlusIso`
   from the selected compactification of j to `Compactification.ofIsOpenImmersion j`,
   then `lowerStarIdDerivedPlus` and the right unitor. This is followed by
   `rightDerivedLowerShriekPlusCompIso R j aY`.
   `CoefDualizingOpenPlusStatement` now compares this identification itself with
   `coefDualizingOpenLeftIso`. For every bounded-below K, the upper path includes
   the bounded-below left comparison and then uses
   `rightDerivedLowerShriekPlusCompatibility` for j followed by aY. The lower path
   first uses that compatibility for aY on J_plus K, then F_Y applied to
   `openImmersionLowerShriek.mapDerivedCategoryPlusCompatibility` on K, and finally
   `coefDualizingOpenLeftIso` on the inclusion of K. Both paths have source the
   inclusion of F_Y_plus(J_plus K) and target F_U(inclusion K).
   This asserts agreement of the item's left identification, including its open
   normalization. The right identification is already defined as its canonical
   counit-preserving mate by `Adjunction.rightAdjointUniq`, so this normalization
   determines the corresponding ordinary right comparison. No assertion that
   ambient right adjoints preserve bounded-below inputs is added. The old generic
   compositor and evaluation-compatibility conjuncts have been removed.
10. Both the counit and Plus statements occur twice, once for A and once for B.
    The two coefficient finiteness instances are obtained from the existing
    `Padic.finite_coefficientExtensionRing` at the two positive levels.
11. `coefDualizingOpenReduction P m hm hmn` is the actual ULift of
    `Ideal.Quotient.factor` for (varpi^n) <= (varpi^m), using
    `Ideal.pow_le_pow_right hmn`. `scalarExtension` is the existing derived
    coefficient tensor, with output in B-module sheaves.
12. `coefDualizingOpenTensorIso` applied to that reduction and j gives precisely
    j_B^* T_Y ~= T_U j_A^*. It is the published K-flat-normalized
    `scalarPullbackIso`, conjugated by `leftDerivedUpperStarIsoMapDerivedCategory`
    on the two sides. It is a natural isomorphism in the B-derived category,
    not a comparison merely after forgetting B. Its normalized K-flat model is
    unchanged by the conjugation; no flatness of the quotient map is assumed.
    This clause is constructed as data, so it has no separate postponed theorem.

The node introduces c_{Y,K} and bounded constructible finite-Tor terminology as
context, but makes no assertion about c_{Y,K} or any such K in its conclusions.
Their already-recorded modules are public imports. The canonical c is the existing
`compactSupportCoefficientComparisonPlus` on its stated finite-Tor domain;
bounded constructible is `DerivedCategory.isBoundedConstructible`, and finite Tor
amplitude is existence of an ordered integer interval for
`DerivedCategory.hasTorAmplitudeIn`. No new finiteness predicate or comparison
was introduced. These contextual definitions impose no input restriction on the
open adjunction or coefficient-tensor isomorphism.

### Dependency declarations used

- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`; `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`; `AlgebraicGeometry.Etale.derivedTensor`.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`; `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-pbc-composite-adjunction`: `Mathlib/CategoryTheory/Adjunction/Basic.lean`; `CategoryTheory.Adjunction.comp`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`; `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`; `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-extension-by-zero`: `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`; `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.IsProper`.
- `lem-amb-etale-adjoint-locality`: `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`; `AlgebraicGeometry.Etale.existsUnique_etaleAmbientAdjointLocalityIso`.
- `lem-amb-etale-compact-comparisons`: `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`; `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`.
- `lem-fix-compact-support-coefficient-change`: `Sheaf.Paper.EtaleCompactSupportCoefficientChange`; `AlgebraicGeometry.Etale.compactSupportCoefficientComparisonPlus`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`; `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `thm-amb-etale-exceptional-adjoint`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`; `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`; `WeilConjectures.PurityFiniteSetting`.
- `def-pur-etale-scalar-pullback-iso`: `Sheaf.Paper.PurEtaleScalarMateProjection`; `AlgebraicGeometry.Etale.scalarPullbackIso`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`; `Padic.finite_coefficientExtensionRing`.
- `def-sf-etale-support-compositor`: `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`; `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. This existing definition node owns precisely the canonical compositor used as data. Its theorem owner `lem-amb-unbounded-compact-support-comparisons` remains a proof dependency only.

The proof-only imports also retain `EtaleCompactSupportNormalization` and
`CompactifiableOverField`; the unbounded comparison module imports the full
geometric proof vocabulary. Mathlib `Adjunction.comp` supplies the exact composite
counit, and `Adjunction.rightAdjointUniq` supplies the counit-preserving isomorphism.
The dependency signatures and docstrings were read from their recorded sources;
no dependency module or repair is needed.

### Edge cases

- U empty: the affine empty scheme and its open immersion are allowed; extension
  and both dualizing-object values are the zero objects. No nonempty hypothesis.
- j identity when Y is affine: the open compactification is (identity, identity),
  and the normalization uses the canonical identity functor comparison.
- m=n: the quotient reduction is the identity-level factor, still allowed by
  `Ideal.pow_le_pow_right`. No strict inequality or nonflatness hypothesis.
- m=1: no lower-level exclusion.
- Arbitrary unbounded inputs: all main functors are the unbounded derived ones;
  the Plus equalities are separate restriction assertions only.
- A nonflat quotient for m<n is allowed. The B-linear tensor isomorphism is
  normalized on K-flat representatives; no underived replacement is made.
- Independent small-site object/hom universes are preserved by the imported
  ringed-topos theorem. The ordinary small-etale constant-coefficient realization
  uses its published `u+1` coefficient universe; no universe equality was added.

### Searches

All searches below were actually performed with msearch.py, or rg on the named
Mathlib/project directories, before writing the declarations.

- LeanFinder: “Open restriction of an etale dualizing complex with compact support
  adjunction and normalized composite counit”: 8 hits, on ordinary scheme-module
  restriction adjunctions and open immersion section formulas; none states this
  constant-coefficient small-etale derived assertion.
- Loogle: “CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.rightAdjointUniq”:
  0 hits for that combined query. Direct source searches found and read both
  categorical constructions, which are used rather than restated.
- msearch grep, CategoryTheory/Adjunction: `rightAdjointUniq|comp_counit_app`:
  9 hits, including Adjunction.Unique and Adjunction.Basic. They supply the generic
  ingredients, not this full geometric two-level statement.
- LeanSearch: “Open restriction of an etale dualizing complex preserves the
  structural composite adjunction counit”: 8 hits, including scheme-module
  restriction adjunctions, fully faithful restriction counits and core adjunction
  data. None states the item.
- `rg` for the node id in `lean/WeilConjectures` and `lean/Sheaf`: no declaration
  for this node before this delivery. Searches for dualizing/open/counit and
  structural adjunction found the general ambient-locality theorem and existing
  pro-etale normalization modules, not this exact statement.
- Source searches for scalar extension, scalar/pullback and open normalization
  found `Etale.scalarPullbackIso` in `PurEtaleScalarMateProjection`, with its
  unique K-flat characterization; it is used directly. The source already has
  `Compactification.ofIsOpenImmersion`, the open derived adjunction, and canonical
  unbounded and Plus compact-support compositors; none is defined a second time.

### Validation

The module compiles cleanly through scompile.py, in both sandbox and final module
modes, against the live published library. No compiler warnings or errors remain.
No local or global library build was run. The only `sorry` is the primary theorem.
All variables and universes are explicitly bound with `autoImplicit false`.
No statement is disputed and no statement correction is made.

### Added existing dependencies

`def-pur-conventions` supplies the already-published bundled finite-field and
coefficient-level setting; `def-weil-l-adic-coefficient-extension` supplies finiteness
at positive levels; `def-pur-etale-scalar-pullback-iso` supplies the canonical
B-linear K-flat-normalized scalar/pullback isomorphism; and
`def-sf-etale-support-compositor` supplies the particular canonical compositor
used by the comparison definitions. The theorem node
`lem-amb-unbounded-compact-support-comparisons` is retained only in `proof_deps`.
No new DAG node is created. No upstream source is changed.


## Repair of returned immutable head 692c626d5542

The first saved-packet dry run on 2026-10-22 passed at 4ca3748cbc2. A source
self-check nevertheless confirmed that the saved packet still contained both
returned faults, so it was repaired before pushing.

- H2: replaced the added statement dependency
  `lem-amb-unbounded-compact-support-comparisons` with the existing definition
  node `def-sf-etale-support-compositor`, exactly as requested. The latter's
  `existing: true` record owns `unboundedEtaleLowerShriekCompIso`. The theorem
  remains a proof dependency. This restores the original base statement
  dependencies and adds only the already-landed definition vocabulary; the
  natural-language statement and proof are unchanged.
- H3: replaced the copied generic composition equality and the generic
  evaluation compatibility by a square for `coefDualizingOpenLeftIso` itself.
  The new real-data helper `coefDualizingOpenLeftPlusIso` explicitly uses the
  bounded-below comparison to `(j, identity)`, identity direct-image
  normalization, and the canonical bounded-below compact-support compositor.
  The square conjugates by the bounded-below compatibilities of exact open
  extension and structural compact support. Thus it compares exactly the
  left identification claimed by this item. `coefDualizingOpenRightIso`
  remains the right-adjoint uniqueness comparison determined by that left
  identification and the specified evaluation adjunction. Its structural
  counit equality remains asserted at both coefficient levels.

The accepted hypotheses, geometric clause, coefficient-tensor isomorphism,
right-adjoint uniqueness construction and two structural counit equations
are unchanged. The empty open, identity open, m=n and arbitrary unbounded
input cases remain admitted. The new square quantifies only over the
bounded-below input category, without restricting the main unbounded functors.

The repair introduced no new independent notion or DAG node and no additional
postponed theorem. It used the existing dependency sources and signatures;
no additional broad search was needed. Compilation and the final dry run
are performed with the prescribed wrappers. The maintainer supplies the
independent second reading under the direct-delivery procedure.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
