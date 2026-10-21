## Worker report

The module `Sheaf.Paper.PointFiniteFreeSectionsTensor` states
`WeilConjectures.point_finite_free_sections_tensor`. Its sole postponed proof is
this theorem. Its conclusion is `Nonempty (PointFiniteFreeSectionsTensorData ...)`:
the structure is the fully expanded assertion, not an unspecified comparison.
All helper definitions have actual data. No basis, ring identification, or comparison
is defined by choosing data from this existence theorem.

The statement and every declaration signature are unchanged from returned head
`a12ed8e1fadd`. The theorem module changes only its completed-scalar import, after
the former published module disappeared from the live repository during this repair.
The H2 repair replaces the two theorem-node additions to `stmt_deps` with
`def-weil-completed-integral-scalar-data`, a definition-only ownership record for
the seven canonical helpers. The four completed-scalar constructions had to be
restored in its owning module after their former live module disappeared; the three
surviving integral helpers are reused without copying.
The surviving integral theorem module remains imported; its theorem is not a
statement input. The missing comparison module is replaced by the definition module.
The original mathematical proof plan and its `proof_deps` are unchanged (the two
returned theorem ids were not in that original list). The new ownership node depends
only on existing definitions and introduces no path back to this item.

Hypotheses and clauses, in the order of the node:

- The global finite-field datum is `(D : FiniteFieldDatum.{t})`, with the exact
  recorded fields, algebraic closure and characteristic convention. The prime is
  `(l : ℕ) [Fact l.Prime]`, and `_hl : l ≠ D.p` retains the required distinction.
- The fixed algebraic closure is `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
  [IsAlgClosure ℚ_[l] Ω]`. The two coefficient fields are
  `(E L : IntermediateField ℚ_[l] Ω)`, with their two `FiniteDimensional` instances
  and `(h : E ≤ L)`. Their inclusion is `IntermediateField.inclusion h`.
- `Spec (.of D.k)` is exactly s. `pointFiniteFreeFinal` is explicitly
  `op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))`, so sections always mean final-object
  evaluation. The site is `Type (t+1)` with morphisms in `Type t`; coefficients and
  module sections have universe `max u (t+1)`. No equality of t and u is imposed.
- `completedIntegralCoefficientSheafUnrestricted l E s` and its L analogue are
  precisely the recorded limits of finite quotient constant sheaves. None is
  replaced by the discrete constant sheaf of the integral ring.
- The fields `coefficientE`, `coefficientL` are ring equivalences from the actual
  rings `Padic.coefficientExtensionIntegers` to the section rings. `constantE` and
  `constantL` fix their values to `integralScalarConstant`, the published unique
  sections with the prescribed constant residues. `quotientE` and `quotientL`
  spell out compatibility with EVERY finite projection (Lean index n means
  exponent n+1). `coefficient_compatibility` is their compatibility with the
  actual completed inclusion and the actual integral-ring inclusion.
- The number d is `completedScalarRelativeDegree l E L ι`, whose definition is
  `Module.finrank E L` for the algebra structure induced by this inclusion.
  `basis : Fin d → O_L` and `integral_basis` assert bijectivity of the integral
  coefficient expansion `a ↦ ∑ i, inclusion (a i) * basis i`. This is exactly an
  O_E-basis, including existence and uniqueness of all coordinates.
- `sheafBasis` is an isomorphism from the restriction of the regular R_L-module
  to the d-fold product of the regular R_E-module. Finite products are also finite
  direct sums in this abelian category. `sheafBasis_inverse` specifies at EVERY
  site object U the sum of coefficients times `integralScalarConstant ... (basis i)`.
  Thus its columns are a single global sheaf basis, and evaluation at s identifies
  its global sections with the same integral basis through `coefficientL`.
- A sheaf F is any `integralTowerModules l E s`, with no finiteness, torsion,
  constructibility or completeness condition. `coordinates F` identifies the
  restriction of its ordinary extended sheaf with its d-fold product.
  `coordinates_tensor` is precisely the local rule `n ⊗ a ↦ (q_i(a) • n)_i`,
  where q_i is projection after `sheafBasis.hom`. `coordinates_inverse` is precisely
  `(n_i) ↦ ∑ i, n_i ⊗ b_i`, with the tensor factors reversed to match Mathlib's
  scalar-extension convention. Both are statements about the actual sheafified
  tensors `completedScalarTensorSection`, not about arbitrary tensors being
  sectionwise equal to presheaf tensors.
- `pointFiniteFreeEvaluation ... coefficientE` is the existing module evaluation
  functor followed by scalar restriction along the displayed ring equivalence.
  `pointFiniteFreeModuleTensor` is exactly `ModuleCat.extendScalars` for the
  recorded integer inclusion; it writes O_L tensor N, canonically the same
  ordinary commutative-ring tensor as the node's N tensor O_L.
- `comparison` is a natural isomorphism between these ordinary scalar-extension
  and sections functors, in `ModuleCat O_L`. Thus it is O_L-linear and natural
  in every F. `comparison_tensor` fixes its map on every pure tensor to the
  sheafified tensor with the constant-value scalar section, as required.
- `comparison_coordinates` says the element `∑ j, basis j ⊗ n j` maps, under the
  same sheaf coordinate map evaluated at s, to exactly the tuple n. Since the
  integral basis gives the usual coordinate isomorphism, this is the identity
  assertion between the two copies of Γ(s,F)^d. `comparison_inverse` gives the
  requested inverse finite sum for every section of the extended sheaf.
- `comparison_unique` states uniqueness among ALL O_L-linear maps on each F with
  the pure-tensor formula. This is stronger specification than merely choosing
  an abstract natural isomorphism: any two basis constructions satisfying that
  formula give this identical map. There is no basis hypothesis in the formula.
- The six fields `sheaf_additive`, `sheaf_limits`, `sheaf_colimits`,
  `module_additive`, `module_limits`, `module_colimits` are the exactness and
  additivity assertions for the two stated functors. In these abelian categories,
  finite limit and finite colimit preservation is the usual exactness condition.
  `restriction_detects_exactness` states, for every short complex of R_L-modules,
  exactness iff exactness after restriction to R_E.
- `complexes` is a NATURAL isomorphism on all cochain complexes indexed by ℤ.
  `complexes_hom` and `complexes_inv` specify both maps in every degree as the
  corresponding comparison maps for that term. Being morphisms of complexes
  includes the differential-commutation identities, so no extra chain hypothesis
  is substituted for the conclusion. There is no boundedness restriction.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  extension module: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public completion
  modules: `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`,
  `integralConstantToCompletionOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent specialization of `SheafOfModules`. `integralTowerModules`
  is the published completed-coefficient specialization, not a new category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, reexporting the actual sheafified tensor.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`:
  `integralScalarIntegerInclusion`, `integralScalarConstant`,
  `integralScalarFiniteConstant`, with their full signatures and residue
  characterizations. These reuse the constant-to-completion construction above.
- `Sheaf.Paper.CompletedIntegralScalarData` (formerly supplied by the now absent
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`): `completedCoefficientMap`,
  `completedOrdinaryScalarExtension`, `completedScalarTensorSection`,
  `completedScalarRelativeDegree`. The map is fixed by all finite quotient
  equations; tensor sections are the sheafification-unit images, transported
  through the canonical ordinary extension witness.
- Proof imports: `Sheaf.CategoryTheory.AdicBasisLimit` (`adic_basis_limit`),
  `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`
  (`AlgebraicGeometry.proEtale_finite_constant_sections`),
  `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis` (`Padic.exists_integral_basis`),
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` (`Padic.extension_integers_dvr`),
  `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
  (`spectralNorm_unique_field_norm_ext`, `spectralNorm.completeSpace`),
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`PresheafOfModules.sheafification`), and
  `Mathlib.CategoryTheory.Limits.HasLimits` (`limit`, `limit.π`).

Sources read: the node and its eight proof steps; every initial statement dependency
and its recorded declaration; the displayed dependencies' canonical map, tensor and
residue signatures; Bhatt--Scholze PDF p. 30 (Lemma 4.2.12) and pp. 58--59, Definition 6.8.1 and Lemma 6.8.2(1)
with proof; and the current blueprint's `def-weil-finite-coefficient-point.md`, including
its final stagewise-evaluation paragraph. The theorem docstring gives the whole
natural-language proof, combining the eight node steps into six paragraphs without
omitting an inference.

Edge cases checked before writing: E=L is allowed by `h : E ≤ L`, with degree one and
no strict-inclusion hypothesis. Ramified extensions use the actual completed inclusion
and cofinal quotient construction; there is no common-uniformizer assumption. Zero,
torsion and nonconstructible F are all included. Site objects U may be empty or
disconnected; the basis identities are sheaf identities and do not require their
sections to be O_E or O_L. Empty local objects have the zero section module, and all
coordinate formulas remain meaningful. Complexes can be unbounded in both directions.
The point Spec k itself is nonempty by its field hypothesis. Independent t and u keep
both large and small coefficient-field choices.

Searches actually run:

- `msearch.py ... leanfinder "Finite free coefficient sheaf global sections tensor
  comparison at a point"`: 8 hits, including `SheafOfModules.sectionMap_freeMap_freeSection`,
  `ιFree_mapFree_inv`, `map_ιFree_mapFree_hom`, and `freeHomEquiv`. These concern free
  sheaves; none states the normalized completed coefficient comparison.
- `msearch.py ... loogle "TensorProduct, Module.Basis"`: 12 hits, including
  `Module.Basis.baseChange`, `TensorProduct.equivFinsuppOfBasisLeft/Right`,
  `eq_repr_basis_left/right`, and basis tensor-product identities. These are useful
  ordinary coordinate facts, without the completed pro-etale coefficient assertion.
- `msearch.py ... grep "sections.*[Tt]ensor|[Tt]ensor.*sections"
  Algebra/Category/ModuleCat`: 0 Mathlib hits.
- `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` for point sections, sections
  tensor, finite-free comparisons, and the exact item id: no declaration for the
  item. `PointSectionsScalarExtension` supplies a related comparison and downstream
  derived claims but omits the full normalized coefficient, basis and local coordinate
  assertion here. It is deliberately not imported. `FiniteFreeCompletedScalarComparison`
  states finite freeness and a derived-completion comparison, not this sections and
  coordinate theorem. The internal-module `FiniteFreeScalarCoordinates` is a different
  category/interface and does not identify the integral coefficient section rings.

No statement correction or dependency-module repair is needed. The missing definition ownership is repaired below.
No `STATEMENT-DISPUTED` issue was found.

## Second reading by NY

The dispatcher assigns this single worker and explicitly prohibits starting other
agents; the maintainer performs the independent review after delivery. This section
records a separate self-audit, not a claim of an independent worker's reading.

I reread the node against the structure fields in the module: both field-ring
identifications are normalized and commute with every quotient; the integral basis and
sheaf basis use the same columns; tensor coordinates are specified locally in both
directions; the comparison is linear, natural, fixed on pure tensors and unique;
coordinate identity and inverse are explicit; both exactness assertions and detection
under scalar restriction are included; and the natural complex comparison is fixed
term by term in both directions. No hypothesis on F or boundedness was added.
The only notation difference is writing scalar tensor section, the actual Mathlib
change-of-rings convention. The source and target scalar actions are the displayed
constant-value actions. No downstream point-comparison theorem is used.

Validation: `scompile.py NY lem-weil-point-finite-free-sections-tensor
.../PointFiniteFreeSectionsTensor.lean` passed both sandbox and library-name compiles
with no compiler diagnostics, in 24.8 s and 26.2 s respectively, under the unchanged
60 s limit. The dependent structure disables automatic constructor-injectivity and
size-of-specification generation; these generated lemmas are not mathematical clauses
and no statement field is removed. This reduced elaboration time; the ordinary default
heartbeat limit is retained. A scalar-action ambiguity in the inverse formula was
resolved with `@id` at the coefficient-restricted module type, and the completed ring
map explicitly forgets commutativity. Neither changes the mathematical map.

## New nodes

`def-weil-completed-integral-scalar-data` owns the seven canonical definitions
requested by H2, plus the `completedScalarChangeData` witness used by the ordinary
extension. Its module is `Sheaf.Paper.CompletedIntegralScalarData`. It constructs
`completedCoefficientMap` directly as the limit lift of the compatible finite
quotient inclusions, retaining commutativity through the faithful forgetful functor.
It defines `completedOrdinaryScalarExtension`, `completedScalarTensorSection`, and
`completedScalarRelativeDegree` by the same canonical constructions used before.
The ordinary extension's objects AND morphisms are determined by the existing
`derivedChangeOfRingsIndependentCoefficients` witness, not either returned theorem.
It reexports `integralScalarIntegerInclusion`, `integralScalarConstant`, and
`integralScalarFiniteConstant` from the unchanged surviving module
`Sheaf.Paper.IntegralScalarExtensionWellDefined`. All data are real constructions;
the new module has no theorem, axiom, or sorry.

Initially this was an `existing: true` ownership record and passed the repaired dry
run at `278482fd60e`. During final delivery the live base advanced to `049907f6ae`
and preflight reported `Sheaf.Paper.FiniteFreeCompletedScalarComparison` absent.
The prescribed `scompile.py --source` confirmed the module unavailable; the refreshed
read clone also no longer has the module or its four completed-scalar definitions.
Thus the missing constructions are supplied here under their owning node, rather
than recording an absent module. Only the theorem module's import changes; no
statement, structure field, hypothesis, or formula changes.

The definition statement introduces prime l, finite coefficient fields and their
specified inclusion, the scheme and small pro-etale site, completed coefficient
sheaves, valuation-ring inclusion, projection-normalized completed map, ordinary
sheafified scalar extension, its actual sheafification-unit pure tensor, relative
degree, and finite and completed constant sections. These correspond, in order, to
`integralScalarIntegerInclusion`, `completedCoefficientMap`,
`completedOrdinaryScalarExtension`, `completedScalarTensorSection`,
`completedScalarRelativeDegree`, `integralScalarFiniteConstant`, and
`integralScalarConstant`. Its construction applies to an arbitrary scheme Y, with
independent site t and coefficient u, and makes no finite-freeness assertion.
Sources are Bhatt--Scholze Lemma 6.8.2(1), Proposition 6.8.14(1), and the ordinary
tensor convention of Stacks 03EK. The current blueprint's
`def-weil-finite-coefficient-point.md` final paragraph was reread for its role.

Searches made for this ownership repair:

- `msearch.py ... leansearch "Canonical map between completed integral coefficient
  sheaves, ordinary extension of scalars, and constant integral sections"`: eight
  hits (`constantSheafΓAdj`, `AdicCompletion.mkₐ`, `LocallyConstant.coeFnₗ`,
  `SheafOfModules.restrictScalars`, `AdicCompletion.of`,
  `ContinuousLinearMap.completion`, `AdicCompletion.mk`,
  `PresheafOfModules.toSheafify`). These are general ingredients, not the exact
  completed pro-etale coefficient interface.
- `msearch.py ... loogle "SheafOfModules.restrictScalars, Module.finrank"`: zero hits.
- `msearch.py ... grep
  "completedCoefficientMap|completedScalarTensorSection|integralScalarConstant"`:
  zero Mathlib hits.
- `rg` for all seven names in `lean/WeilConjectures` and `lean/Sheaf` found the exact
  published definitions in the two modules above and consumers. These exact
  declarations are reused. Searching `dag/nodes` found their theorem owners and
  consumers, but no definition node with this interface. In particular,
  `def-weil-pbc-finite-completed-coefficient-map` has the transported PBC
  `AlgebraicGeometry.Scheme.pbcCompletedScalarMap` interface and itself cites the
  well-definedness theorem, so it does not own the present seven constructions.
- `tools/blueprint_refs.py search 'completed scalar'`: one unrelated field-extension
  statement; search `'coefficient map'`: 27 blueprint matches, none this definition
  package. `ancestor` confirms `def-weil-finite-coefficient-point`.

Repair self-check: I reread all seven original full signatures and docstrings and
the surviving live dependencies. The completed map now uses the explicit limit
lift of the compatible quotient inclusions; the constants retain their locally
proved unique residue characterization. Neither uses either main sorry theorem. The ordinary extension uses the
canonical tensor witness, and the pure-tensor section explicitly passes through
its sheafification unit and canonical transport. The degree uses the algebra
induced by the specified inclusion. No arbitrary map or undetermined choice was
introduced. E=L, ramified extensions, empty site objects and arbitrary modules
remain included. The original clause-by-clause audit above still applies: the theorem module
changes only an import, and the constructions retain their canonical meanings.

Repair validation: the explicit `scompile.py` run passed sandbox and library-name
compiles without diagnostics (24.8 s and 26.2 s). The initial saved-packet dry run
also passed; the repaired packet is checked again before delivery.

Current repair audit: the only additional definition is the existing witness
specialization `completedScalarChangeData`, already implicit in the old construction.
Its DAG dependency `lem-pur-derived-change-of-rings` is cited explicitly. Its statement
specifies both the ordinary tensor objects and all maps, so the selected functor is
determined. The completed inclusion is now a direct limit lift and therefore no
longer needs a helper existence theorem. Finite quotient naturality is proved by the
already published `integralScalarQuotientMap_transition`. This is structure data,
not a new postponed mathematical lemma. No independent universe is collapsed.

Updated validation: `scompile.py` compiled both delivered modules cleanly, including
private overlay, sandbox, and library-name checks. The definition module took
8.7–13.1 s; the theorem module took 37.0 s and 36.2 s.

## Saved-packet repair validation (2026-10-21)

The required initial dry run of the retained packet passed as `a6c079716cd`:
both delivered modules compiled and the server preflight accepted the packet.
The current base comparison changes only the item's `lean` and adds the owning
`def-weil-completed-integral-scalar-data` to `stmt_deps`; no existing statement
dependency, mathematical statement, proof step, or proof dependency is removed.

A separate consumer importing only `Sheaf.Paper.CompletedIntegralScalarData`
passed sandbox and library-name compiles through `scompile.py`. Explicit `#check @`
commands resolved every recorded export: `completedCoefficientMap`,
`completedScalarChangeData`, `completedOrdinaryScalarExtension`,
`completedScalarTensorSection`, `completedScalarRelativeDegree`,
`integralScalarIntegerInclusion`, `integralScalarConstant`, and
`integralScalarFiniteConstant`. The additional returned name
`integralScalarQuotientSheafMap` also resolved through that single import.
The obsolete `completedCoefficientMap_existsUnique` is neither used nor recorded:
`completedCoefficientMap` is now the direct compatible-quotient limit lift and
needs no postponed existence theorem. The definition node is `existing: false`
and delivers its owning module, replacing the broken `existing: true` binding
identified in returned head `105846e5aa84`. The consumer check remained in the
sandbox scratch directory and is not a delivered library module.

## Returned-head repair self-check (2026-10-21)

The retained packet repairs the immutable-head `3ce998cc032c` return: the owning
node now has `existing: false` and delivers `CompletedIntegralScalarData.lean`.
The required first dry run passed as `5261d09cc2e`, with server preflight and
both delivered files accepted. The current-main comparison again found only
`lean` and the added owning definition in `stmt_deps` changed on the item;
its mathematical statement, proof and original dependencies remain intact.

The separate consumer `scratch/CheckCompletedScalarExports.lean` was recompiled
through `scompile.py`, together with the owning module. Both sandbox and
library-name checks succeeded without diagnostics. All nine checked names
resolved through the single public import, including every currently recorded
export and `integralScalarQuotientSheafMap`. The owning module compiled in
6.3–7.3 seconds; the consumer checks took 2.8 and 3.5 seconds.
`completedCoefficientMap_existsUnique` is obsolete: it is absent from both
the node's declarations and its construction. The completed map is defined by
an explicit compatible-quotient limit lift, so no existence theorem is needed.
This fixes the returned absent-declaration binding without introducing a
postponed theorem or changing any comparison formula. I reread both delivered
modules and the owning node record for this self-check and retained their
existing mathematical content, as instructed after a successful saved-packet
dry run.

## Immutable-head d3c85ff761ec repair validation (2026-10-21)

The required first dry run of the retained packet passed as `43ca15599ea`:
server preflight and both delivered module compiles succeeded. As instructed for a
passing saved packet, the Lean modules and node records are retained. Compared
with the current main node, the item changes only `lean` and adds
`def-weil-completed-integral-scalar-data` to `stmt_deps`; no original dependency,
mathematical statement or proof step is removed or changed.

The returned absent-declaration errors are repaired by the concrete owning module
and its `existing: false` record, rather than an `existing: true` reference to the
withdrawn module. A separate consumer importing only
`Sheaf.Paper.CompletedIntegralScalarData` was compiled again with that owning
module through `scompile.py`. All nine explicit `#check @` commands succeeded in
both sandbox and library-name mode: `completedCoefficientMap`,
`completedScalarChangeData`, `completedOrdinaryScalarExtension`,
`completedScalarTensorSection`, `completedScalarRelativeDegree`,
`integralScalarIntegerInclusion`, `integralScalarQuotientSheafMap`,
`integralScalarConstant`, and `integralScalarFiniteConstant` (all in namespace
`WeilConjectures`). The owning module compiled in 6.3–7.3 seconds and the consumer
in 2.8 and 3.5 seconds, without warnings or errors.

The other returned name, `completedCoefficientMap_existsUnique`, is obsolete and
is absent from the owning node's declarations: `completedCoefficientMap` now
constructs the limit lift directly from the compatible finite quotient maps.
There is no postponed existence theorem to export or use. The scratch consumer
is not part of the delivered library. I reread the owning module, the theorem
module and both node records for this self-check; the original clause-by-clause
and edge-case audit remains valid, including independent universes and the
canonical sheafification-unit tensor formula.
