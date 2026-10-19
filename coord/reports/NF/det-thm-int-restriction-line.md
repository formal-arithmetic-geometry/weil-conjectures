## Worker report

The module `Sheaf.SixFunctors.IntegralRestrictionLine` states all three clauses of
`det-thm-int-restriction-line`, with one postponed theorem `integralRestrictionLine`.
Its helper definitions construct actual functors and full-subcategory restrictions;
none chooses an unspecified object or contains `sorry`. The theorem docstring gives
all nine steps of the current DAG proof, including both triangle calculations.
No statement correction, new node, or dependency repair is needed.

Hypotheses and objects, in order:

- Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]` in the explicit section context.
- The finite extension inside the fixed algebraic closure is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. Its condensed valuation ring is
  `Profinite.padicIntegersRingObj ℓ E.val`, retaining its adic topology.
- The standing field is `(k : Type u) [Field k]`, with
  `[Fact (ringChar k).Prime]` expressing positive prime characteristic and
  `[Fact (ringChar k ≠ ℓ)]` expressing the required inequality.
- A separated finite-type k-scheme is `(Y : Scheme.{u})` with `Y.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  The two source schemes and their maps are the structural projective/affine
  projections over Y, so they canonically belong to the same setting; no extra
  source-scheme hypothesis is imposed.
- All natural dimensions are included by `(d : ℕ)`.
- P1 is `ProjectiveSpace (ULift.{u} (Fin 2)) Y`: projective homogeneous coordinates
  have cardinality two. Affine d-space is `AffineSpace (ULift.{u} (Fin d)) Y`.
  In both cases `... ↘ Y` is the recorded first projection.
- Dbc is exactly `constantModelBoundedConstructible`, using finite constant scalar
  models and bounded cohomology. L(T) is `IntegralCompactSupport.localizing`, namely
  `CategoryTheory.localizingClosure` of this same Dbc in the ordinary unbounded
  internal-module derived category. There is no completeness restriction.
- `tateLine` applies the inverse of the existing sectionwise module equivalence to
  `spSignedTwist X _ (spIntegralTwist X ℓ E) d`. Thus it transports the published
  signed powers of the specified inverse-limit integral Tate line into internal
  modules. It changes neither coefficients nor Tate line. `pullTwistShift` is the
  actual derived pullback, right derived tensor with that line in degree zero,
  then shift by `2 * (d : ℤ)`. This uses the internal-module derived tensor already
  employed by the Brown/projection-formula framework. The recorded
  `ProEtaleTateTwistsOfUniverses` is publicly imported and retains all original
  Tate-line constructors; the sectionwise `spComplexTwistOfUniverses` is not used
  on internal-module complexes of a different encoding.

Conclusion, clause by clause:

1. Existential `hq` and `hr` assert preservation of the actual localizing categories
   by q^*(1)[2] and Rq_*; these are the typing assertions implicit in the node's
   functor statement. `restrictedPull` and `restrictedPush` restrict only the
   codomains using these membership proofs. The first `Nonempty (... ⊣ ...)`
   states exactly the adjunction Rq_* to q^*(1)[2]. `brownComparison` then gives
   the natural isomorphism q^! ≅ q^*(1)[2].
2. `hp` similarly types p_d^*(d)[2d]; the second `brownComparison` states
   p_d^! ≅ p_d^*(d)[2d]. Brown's recorded declaration proves existence, without
   choosing a right adjoint in a definition. Consequently the comparison is
   universally quantified over a Brown right adjoint J together with its defining
   adjunction. It covers any chosen boundary compactification, in particular the
   fixed one. Compactification independence in the recorded proof identifies all
   these left functors; uniqueness of right adjoints identifies all J. This is
   the intrinsic meaning of the node's f^! isomorphism and adds no assumption.
   There is no vacuity: `exists_integralBrownAdjoint` supplies such adjoints on
   each boundary compactification for these standing morphisms.
3. The last two universal implications state preservation of
   `constantModelBoundedConstructible` under exactly the projective and affine
   `pullTwistShift` functors, respectively. These quantify over ambient complexes,
   equivalent to saying the functors take every object of Dbc into Dbc.

Dependency declarations read and used:

- `sk-def-sfb-dc-setting`: upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `compactificationOverField`, with its explicit standing scheme conventions.
  The current copied 51-module framework was read under `lean/WeilConjectures/`,
  together with `coord/pefw-upstream-framework.md`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `IsConstantModelConstructible` and `constantModelBoundedConstructible`.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`
  publicly exports the original `CategoryTheory.localizingClosure` used by
  `IntegralCompactSupport.localizing`. This keeps the same closure as Brown.
- `det-prop-int-brown-adjoint`: `Sheaf.SixFunctors.IntegralBrownAdjoint`,
  `IntegralCompactSupport.lowerShriek`, `brownAdjointAssertions`, and
  `exists_integralBrownAdjoint`. Its `Ambient`, `pull`, `push`, `image`, and
  `localizing` come from its public dependency `IntegralLocalizingCompactSupport`.
- `sk-def-sp-tate-twist`: `Sheaf.Paper.ProEtaleTateTwistsOfUniverses`,
  `spComplexTwistOfUniverses`, publicly retaining `spIntegralTwist` and
  `spSignedTwist`; the latter two give the canonical coefficient lines here.
- `def-nagata-projective-space-base-change`: upstream
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `ProjectiveSpace` and
  `ProjectiveSpace.over`, with the properness instance for the proof.
- `def-sbc-affine-space`: Mathlib `AlgebraicGeometry.AffineSpace` and
  `AffineSpace.over`, full signature and empty-index convention read in
  `Mathlib/AlgebraicGeometry/AffineSpace.lean`.
- `det-def-localizing-closure-ctf-equals-bc`:
  `Sheaf.Paper.LocalizingClosureCtfEqualsBc.localizingClosure_ctf_equals_bc`
  (declaration namespace `AlgebraicGeometry.ProEtale`), including its equality
  of the Dctf and Dbc closures.
- The canonical encoding transport is
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` in
  `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` (read with
  `scompile.py --source`); derived tensor is
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor` in the upstream
  `ModuleObject.Derived.Tensor`.

All currently recorded proof modules are imported, including integral tensor,
Cartesian coefficients, proper projection/base change, affine trace tower,
extension by zero, canonical ringed tensor comparison, and generic Mathlib
adjunction limits, mates, uniqueness, composition, and closed-immersion properness.
The following proof-only DAG nodes have no published Lean declaration and so add
no import: `det-lem-formal-closed-support-sheaves`, `det-prop-diagonal-tower-limit`,
`det-prop-diagonal-tower-coefficients`, `det-prop-diagonal-tower-trace`,
`lem-sfb-trace-base-change-first`, `lem-sfb-projection-section-normalization`,
`lem-sfb-trace-base-change-second`, `def-sfb-dc-open-lower-shriek-adjunction`.
They remain named in the proof docstring for stage 3. No new independent notion
is introduced by the actual functor restrictions or the Brown comparison predicate.

Edge cases checked before writing:

- d=0: `ULift (Fin 0)` is empty, so Mathlib's affine projection is a canonical
  isomorphism. The published signed twist at zero is the coefficient unit, and
  the shift is zero; the formula is the identity after the canonical identification.
- Empty Y: both source schemes are empty; no point, nonempty cover, or nonempty
  scheme hypothesis is required in any helper or conclusion.
- The zero complex belongs to the stated categories and is preserved; no
  nonzero-complex or torsion-free hypothesis is inserted.
- d=1 gives the expected affine line; P1 uses two homogeneous coordinates,
  rather than one. Ramified finite extensions E are allowed, without choosing
  a uniformizer; the published integral twist uses the cofinal ell-power system.
- Universe u is explicit everywhere, including `ULift.{u}` for coordinate types.
  The pro-etale site and coefficients retain their existing u+1/u conventions.
  No equality between different site or localization universes is imposed.

Searches made (the wrapper logs raw outputs in `searches.jsonl`):

- LeanFinder: "Integral adic exceptional inverse image for projective line and
  affine space is pullback with Tate twist and shift". Eight hits, all Proj
  affine-chart pullback isomorphisms; no matching cohomological statement.
- Loogle: `CategoryTheory.Adjunction, DerivedCategory`. Zero hits.
- Mathlib grep: `upperShriek|projectiveLine|tateTwist`, AlgebraicGeometry. Zero hits.
- LeanSearch: "For integral adic coefficients the projective line direct image
  is left adjoint to pullback twisted by one shifted by two". Eight hits on
  ordinary sheaf/module pullback adjunctions, not the exceptional adjunction.
- Ripgrep in the prescribed upstream `WeilConjectures` and side `lean/Sheaf`:
  `det-thm-int-restriction-line|integral.*[Rr]estriction.*[Ll]ine|integral.*[Pp]rojective.*[Aa]djoint`.
  No matching declaration (one unrelated compact-support docstring hit).
- Read/search of the existing Tate constructors, internal-module derived tensor,
  and source/affine/projective projections found exactly the interfaces reused.

The resolved repair note concerns the earlier stage-1 proof re-split. Its nine-step
route and theorem statement are unchanged. No STATEMENT-DISPUTED flag or node fault.

## Second reading by NF

A fresh manual pass matched the binders, both actual structural projections, all
three conclusion clauses, the ambient categories and each helper with the node and
its source text. It checked the transported integral Tate line, tensor ordering,
positive cohomological shifts, d=0, and the distinction between existence of a Brown
right adjoint and choosing arbitrary functor data. All helpers have concrete data
and all theorem proofs are `sorry`. The task forbids starting other agents; this
section records the worker's second pass, not an independent second worker review.
The maintainer's independent review is still required by the delivery contract.

Validation: the prescribed `scompile.py NF det-thm-int-restriction-line` compiled
both sandbox and library contexts cleanly (4.9 s and 6.4 s respectively), after
preparing current dependency overlays. No errors or non-sorry warnings occurred.
The only changed item field is `lean`; the recorded theorem signature matches the
source verbatim. Maximum Lean line width is 95 characters, and the only postponed
proof is the named main theorem. Final packet preflight and compile follow below.
