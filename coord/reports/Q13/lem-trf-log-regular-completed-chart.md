## Worker report

This delivery states `AlgebraicGeometry.exists_completed_chart_of_logRegular` in
`Sheaf.AlgebraicGeometry.LogRegularCompletedChart`. Its only theorem has proof `sorry`.
The three definitions contain real canonical constructions, with no `sorry` in their bodies:
`strictLocalRingStrictHenselizationIso` restricts the structure-ring stalk colimit to
initial affine pointed neighbourhoods; `EtaleLogStructure.sharpChartRingMap` composes
this isomorphism with the recorded log germ and structure map; and
`AddMonoidAlgebra.completedLocalModelMonomial` inserts the actual basis monomial into
the existing polynomial ring and then its adic completion. These are helper maps for
this node, not new notions or replacement definitions of existing rings.

Source checked: ILO, Exposé VI 1.6(i)--(ii), printed p. 70 (PDF page 76). It gives
completed strict-local charts over k, or over C(k) modulo f congruent to p modulo
nonzero monomials and the parameters. The module docstring and theorem docstring
retain the node's seven-step proof plan, including the dimension-based injectivity
argument, the domain input for the mixed-characteristic quotient, and boundary cases.
No natural-language statement correction is needed.

Hypothesis and clause correspondence:

- `(X : FineSaturatedLogScheme.{u})` is precisely the locally Noetherian fs log scheme:
  the recorded structure contains `scheme`, `locallyNoetherian`, `logStructure`, and
  `fineSaturated`. `_hX : X.IsLogRegular` is the recorded regular stratum quotient
  and rank/dimension condition, at every geometric point.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `t : Spec (.of Ω) ⟶ X.scheme`
  give the geometric point over its implicit underlying point x. No separate x
  is needed because the statement uses only its geometric strict localization.
- `Scheme.strictHenselizationRing t` is A, the dependency's actual affine
  pointed-neighbourhood colimit. `IsLocalRing.ResidueField` of that ring is k.
  The existential local-ring instance records the intrinsic local structure,
  rather than assuming it as an extra hypothesis. This is necessary because the
  colimit-ring API does not install a global local-ring instance.
- `X.logStructure.characteristic t` is P. It is multiplicative in the existing log
  interface, so `Additive (...)` is used in the existing additive monoid-ring API.
  Thus the additive zero in the model means the multiplicative identity of P.
- `W`, `w`, `β`, `_hβ`, and `_hident` render the initially chosen sharp chart of
  `lem-trf-log-regular-sharp-chart`: W is étale, w is its specified lift, β has values
  in actual log sections, `IsChart` is the recorded stalk-pushout property, and
  `Associates.mk (germ ... (β q)) = q` is the specified characteristic identification.
- The existential `W'`, `w'`, `β'`, `IsAffine W'.left`, `IsChart W' β'`, and its germ
  equality render the allowed replacement on an affine pointed étale neighbourhood,
  with the same P and same identification. No refinement relation to W is required
  by the node, and none is imposed. Local Noetherianity of W' follows from its étale
  morphism to the locally Noetherian X, so it is not an additional assumption.
- `∃ n : ℕ` renders the nonnegative integer n, chosen once before both alternatives.
- “A contains a field” is `∃ (K : Type u) (_ : Field K), Nonempty (K →+* A)`.
  A unital map from a field to a nontrivial local ring is injective, so this says
  exactly that A contains a subfield. Every such subfield has size at most A,
  making `Type u` sufficient, including u = 0. Its negation is the second case.
- The first case gives `e : CompletedLocalModel k (Additive P) n ≃+* AdicCompletion
  (maximalIdeal A) A`. This is the inverse orientation of the displayed isomorphism
  in the node, allowing the compatibility to read `e(z^q) = a(q)`.
- The second case supplies `p : ℕ`, `Nat.Prime p`, `CharP k p`, and `CharZero A`,
  spelling out the node's mixed characteristic (0,p). It supplies C with real ring
  and local-ring structures, `IsCohenRing p C`, and an isomorphism `C/(p) ≃+* k`.
  By the Cohen predicate's maximal-ideal equality this is exactly its residue field.
- `θ - p ∈ completedLocalModelBoundaryIdeal C (Additive P) n` is precisely the
  required congruence modulo `(z^q : q ≠ 0, t_i)` in the completed model ring.
  `e : (CompletedLocalModel C ... n ⧸ Ideal.span {θ}) ≃+* AdicCompletion ... A`
  gives the asserted hypersurface model.
- Both `∀ q` equations use the actual polynomial basis monomial, its completion map,
  the actual replacement chart ring map, and the canonical completion map from A.
  In the second case the monomial first passes through the quotient by `(θ)`.
  No arbitrary map, choice of an unspecified chart action, or bare isomorphism
  substitutes for monomial compatibility.
- A ring equivalence between these complete local rings is automatically local and
  continuous for their maximal-ideal-adic topologies: it identifies maximal ideals
  and every power. Thus `≃+*` renders the isomorphism of complete local rings without
  imposing extraneous topological structures or continuity assumptions.
- `CompletedLocalModel`, `localModelCompletionIdeal`, `localModelBoundaryIdeal`, and
  `completedLocalModelBoundaryIdeal` are reused unchanged from
  `Sheaf.RingTheory.LogRegularSaturationNormality`. They are the node's exact
  finite-sum monoid polynomial ring and completion at `(m_L,z^q,t_i)`.
  For a field m_L = 0; for a Cohen ring m_L = (p), as required.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogStructure.characteristic`,
  `EtaleLogStructure.IsChart`, and `EtalePrelogStructure.germ` / `stalkAlpha`.
- `Sheaf.AlgebraicGeometry.LogRegularSharpChart`:
  `AlgebraicGeometry.exists_sharp_chart_of_logRegular` (the original chart interface).
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing`, and its upstream affine-colimit
  definition in `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`.
  The canonical helper uses the representative equivalence and affine inclusion,
  the initiality supplied by `strictHenselization_properties`,
  `Functor.Final.colimitIso`, and the point's colimit cocone universal property.
  Compiler `#print` inspection confirmed that the published colimit diagram is
  named `strictHenselizationAffineDiagram` and is indexed by the small model;
  the checked-out source uses a newer abbreviation. The helper follows the
  published exact interface. Temporary inspection commands are removed.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, already contained
  in the fs log scheme data; `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` for the
  implicit underlying point; `Mathlib.CategoryTheory.Elements` and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: the pointed neighbourhood fibre.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing` (source read through
  `scompile.py --source`); `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`:
  `AdicCompletion` and its canonical algebra map; `.LocalRing` supplies local
  completion interfaces. `IsLocalRing.ResidueField` is the actual residue field.
- `Sheaf.RingTheory.LogRegularSaturationNormality`: all four existing model
  constructions above. Its already-landed node is added to `stmt_deps` because
  those definitions are now used in the statement; it was already in `proof_deps`.
- Proof-only imports retain the recorded plan: `FormalMonoidRingDimension`,
  `StrictHenselizationNoetherian`, `CompletionDimension`, `CohenPowerSeriesPresentation`,
  `PowerSeriesFieldCohenRegularComplete`, `AdicCompletionNoetherian`, and Mathlib's
  adic completion functoriality and completeness modules. Their theorem signatures
  were read from the node records and available source modules.

Edge cases checked mathematically before drafting:

- P trivial: `Additive P` is the zero monoid, so there are no nonzero monomial
  generators. No nontriviality assumption is placed on P.
- n = 0: `Fin 0` has no parameters; the existing polynomial and ideal constructions
  use the empty range. No positivity assumption on n is imposed.
- P trivial and n = 0: equal characteristic gives k itself; the mixed quotient
  congruence permits θ = p in C and gives k. The latter cannot arise for a log
  regular A of dimension zero with no subfield, but the model construction remains
  meaningful and no boundary case is artificially removed.
- Characteristic zero and positive equal characteristic both satisfy the first
  field-containment case; unramified and ramified mixed characteristic satisfy the
  second. The residue characteristic p is explicitly prime and is not fixed to 0.
- The empty scheme has no geometric point t, so the theorem is vacuous there,
  exactly as the source. The zero ring cannot be A with a local-ring structure.

Searches for existing declarations (2026-10-17 UTC):

- `msearch.py ... leanfinder` query: “A log regular local ring has a completed monoid
  chart in equal and mixed characteristic”. Eight hits included the characteristic
  split for local rings, BDeRham completions, and Henselian facts; no log chart theorem.
- `msearch.py ... leansearch` query: “A complete log regular local ring is a monoid
  power series ring over a field or a Cohen ring quotient”. Eight hits concerned
  ordinary power series and completions; no log-regular presentation.
- `msearch.py ... loogle '"CompletedLocalModel"'`: no hits in Mathlib.
- `msearch.py ... grep 'LogRegular|log_regular|CompletedLocalModel'`: no Mathlib hits.
- `rg` in upstream `WeilConjectures` for log regularity, completed charts, this
  node id, and the proposed declaration names found no matching theorem or helper.
- `rg` in `lean/Sheaf` found the exact model definitions in
  `LogRegularSaturationNormality`, the sharp-chart theorem, and the actual strict
  local ring and germs in `LogRegularPair`. These are reused rather than copied.
- `rg` in Mathlib, upstream, and `lean/Sheaf` found no occurrence of any of the
  four new full declaration names; the upstream-name index also had no match.

No new DAG nodes, unusable dependency repairs, or statement disputes were needed.
Compilation and delivery preflight results are recorded below after the final check.

Validation: the final `scompile.py Q13 lem-trf-log-regular-completed-chart` run
succeeded for both the sandbox compilation and the actual library module compilation,
with no errors or warnings. All variables and universes are explicitly bound, the
only `sorry` is the main theorem's proof, and every Lean line is at most 100 characters.
The delivery is also checked through the prescribed `deliver2.py --no-push` preflight
before the final delivery command.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
