## Worker report

The module `Sheaf.TraceFormula.LogChartStrictLocalTor` states
`AlgebraicGeometry.logChart_strictLocal_torOne_isZero`, with `sorry` as its entire proof.
It states first-Tor vanishing at any geometric point for an arbitrary fine saturated chart.
It defines no new object. The accepted stage-1 split is preserved. Its Q78 review was a
stage-1 review, not a Lean attachment: the live node had no `lean` or `reviewed_lean`.
This is the stage-2 handoff authorized by `coord/brief-stage2.md` section 0.

The source was read in the local ILO PDF: Expose VIII, printed p. 110 (PDF p. 116),
the proof of Lemma 3.4.3, asserting the monoid-ideal quotient Tor vanishing for a chart;
and Expose VI, printed pp. 70 and 75, the characteristic chart and group splitting.

Clause-by-clause correspondence:

* The locally Noetherian fs log scheme is `X : FineSaturatedLogScheme.{u}`.
  The bundle contains its scheme, `locallyNoetherian : IsLocallyNoetherian X.scheme`,
  actual etale log structure, and the fs chart property. `hlog : X.IsLogRegular`
  imposes exactly the regular quotient and characteristic-rank dimension formula.
* `A : Type u` with `[CommRing A]` is the stated commutative ring. The presentation
  `eA : X.scheme ≅ Spec (.of A)` renders `X = Spec A` up to scheme isomorphism,
  retaining the existing bundled log-scheme interface. It imposes precisely affineness.
* `P : Type u` with `[AddCommMonoid P]` is the additive chart monoid.
  `hP : IsFineSaturatedMonoid (Multiplicative P)` uses the recorded fs predicate:
  finite generation, injection into the group completion, and saturation.
* `α : Multiplicative P →* A` is the structural monoid map, with additive monoids
  converted to multiplicative notation by Mathlib's `Multiplicative` wrapper.
  `c` is the map into sections of the actual log sheaf on the identity etale object,
  and `hc : X.logStructure.IsChart (Scheme.Etale.mk (𝟙 X.scheme)) c` is exactly
  the logification/pushout chart condition at every geometric point.
* `hα` says that applying the actual log structural map to `c p` gives `α p`,
  expressed in global functions through `Scheme.ΓSpecIso` and the affine presentation
  `eA`. This supplies the assertion that α is the structural map of this chart;
  it is not an independent condition on an unrelated ring map.
* `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `t : Spec (.of Ω) ⟶ X.scheme`
  give every geometric point in the node's definition, not only closed points.
* The coefficient ring is exactly `Scheme.strictHenselizationRing t`:
  `chartStrictHenselizationMap` has this codomain, defined by the recorded small
  affine pointed-neighbourhood colimit. Its data is the chart germ, the structural
  map on log stalks, and the canonical cofinality isomorphism from the etale ring stalk.
  At the identity etale object the lift is `Over.homMk t (Category.comp_id t)`.
  The equality `hα` makes this the composite `z^p ↦ α(p) ↦ B` in the question.
* `H : Set P` and `hH : ∀ h ∈ H, ∀ p : P, h + p ∈ H` render exactly the
  monoid-ideal condition, with no nonempty or proper restriction.
* `Multiplicative.ofAdd '' H` merely transports the same subset to multiplicative
  notation. `LogChartFaceTor.ideal` is the existing ideal spanned by its monomials
  `MonoidAlgebra.single p 1`. Since H is stable under addition by P, this is
  precisely the direct sum of integer basis lines indexed by H: multiplying a
  generator by a monomial stays in H, and every basis line indexed by H is included.
* `LogChartFaceTor.tor` unfolds to
  `((Tor' (ModuleCat (MonoidAlgebra ℤ (Multiplicative P))) 1).obj (R ⧸ I)).obj B`,
  with the quotients bundled as module objects. Its `coefficients` restricts scalars
  along `MonoidAlgebra.lift` of the specified chart map, so it fixes the precise
  R-action on B. `IsZero` says that this Tor module is zero, the sole conclusion.
  No sharpness or characteristic-monoid identification appears in the signature.

Dependency declarations inspected and used:

* `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `FineSaturatedLogScheme.IsLogRegular`, `EtaleLogStructure.IsChart`, including
  their underlying `EtalePrelogStructure`, stalk/germ maps and fs-monoid predicate
  from `Sheaf.AlgebraicGeometry.LogRegularPair`.
* `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  used by the bundle's `locallyNoetherian` field.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric point is
  written inline as prescribed by `def-weil-geometric-point`. Its companion
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` was read.
* `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, the actual affine-neighbourhood colimit.
* `Mathlib.CategoryTheory.Monoidal.Tor`: `CategoryTheory.Tor'`, left derived in
  the first factor, used by the existing Tor abbreviation.
* `Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`:
  `EtaleLogStructure.chartStrictHenselizationMap` and
  `strictLocalRingIsoStrictHenselization`. Only these general canonical
  constructions are used, not its sharp-chart contraction theorem.
* `Sheaf.TraceFormula.LogChartFaceTorComparison`: `LogChartFaceTor.tor`, `ideal`,
  `coefficients`; its comparison theorem is a proof dependency. The first three
  definitions apply to any commutative chart monoid and coefficient ring.

The returned head `f11078752052` incorrectly cited the two theorem nodes in
`stmt_deps` merely because their modules contain these helper definitions.
The repair replaces those two theorem entries with
`def-trf-chart-strict-henselization-map` and `def-trf-monomial-quotient-tor`.
Both new definition nodes record the already landed helpers with `existing: true`.
The contraction theorem record and comparison theorem record are untouched;
`lem-trf-log-chart-face-tor-comparison` remains in `proof_deps`.
The item's statement, proof, proof dependencies and Lean signature are unchanged.
The item copy was refreshed from the current shared node, retaining only its saved
Lean attachment and adding these two definition dependencies. A fresh server-source
read through `scompile.py --source` agrees with both local helper modules.
No dependency module or replacement definition is introduced.

Recorded proof-dependency modules are imported without `public`, except where the
same module is also needed publicly for a statement construction. Imports include
the Kato sharp-chart vanishing, sharp-chart existence, fs face sharpening, strict
henselization local structure, affine pointed-neighbourhood cofinality, and geometric
stalks. `lem-trf-chart-face-localization-logification` and
`lem-trf-integral-monoid-free-sharpening-splitting` have no recorded module yet;
their imports are omitted and their mathematical uses remain in the proof docstring.

Edge cases checked against the statement and definitions:

* H empty gives the zero ideal and the free first argument R; first Tor vanishes.
* H equal to P gives the unit ideal and zero first argument; first Tor vanishes.
* H meeting the face of elements mapping to units is allowed: the associated sharp
  image ideal becomes total, matching the unit-localization comparison.
* P a group, including a finite torsion unit group, is allowed. Nonempty group
  ideals are total; no torsion-free hypothesis is imposed on P's full group completion.
* For P trivial the only ideals are empty and total. The usual N-chart on k[t]
  is also included. At the generic point its generator becomes a unit; at the origin
  it does not, so the arbitrary-chart distinction is retained.
* The empty affine scheme has no geometric point t; no artificial nonempty-scheme
  hypothesis is added. No characteristic or properness restriction is imposed.
* All universes and variables are explicitly bound; `autoImplicit` is disabled.
  There is one ambient size u, as in the dependency interfaces, and it is arbitrary.

Searches for existing statements and constructions:

* `msearch.py leanfinder`: "Tor one of a monomial quotient of an integral monoid
  algebra with the strict henselization at a geometric point of a log regular scheme
  vanishes for any fine saturated chart". Eight hits on smooth loci and cotangent
  homology, no matching arbitrary-chart theorem.
* `msearch.py leansearch`: "Tor vanishing for monoid ideal quotients over log regular
  scheme charts at strict henselian local rings". Eight unrelated ideal,
  localization and torsion results; no matching theorem.
* `msearch.py loogle`: `"Tor", "MonoidAlgebra"`. Twelve monoid-algebra map hits,
  no log-chart Tor theorem.
* `msearch.py grep`: `logRegular|log_regular|monomial.{0,12}Tor|Tor.{0,12}monomial`.
  Three unrelated monomial-generator hits, no log-regular definition or theorem.
* `rg` over `lean/WeilConjectures` for log regularity, monomial Tor and the proposed
  declaration, and `grep -rn` for the item id: no duplicate theorem.
* `rg` over `lean/Sheaf`: found `torOne_monoidIdeal_independence`, whose explicit
  equivalence with the characteristic monoid makes it a different statement;
  `LogChartFaceTor.tor`, whose actual construction is reused; and
  `chartStrictHenselizationMap`, whose canonical coefficient map is reused.
  The affine tensor-injectivity theorem has a different conclusion and coefficient
  ring and is not an exact existing match. The chosen declaration name is unused.

No statement dispute, node correction, hollow definition, or stronger assumption.
The server compile through `scompile.py` succeeded for both its sandbox probe and
the actual module, with no errors or warnings beyond the permitted sorry warning.

## Second reading by Q85

This is a separate reading pass by the same worker; no other agent was started.
The maintainer's independent delivery review remains separate. With the node and
module open, I rechecked affineness via eA, the bundle's locally Noetherian and fs
fields, log regularity via hlog, additive fs P, the global chart hc and its structural
identification hα, unrestricted geometric t, the prescribed affine-colimit ring B,
the action built from the actual chart germ, the ideal H including the empty set,
and precisely first Tor of R/I with B. Each is represented as listed above.
In particular, no characteristic-monoid equivalence from the Kato dependency is
imported as a hypothesis. The helper `chartStrictHenselizationMap` does not require
the sharpness hypothesis of its owning module's separate theorem, and
`LogChartFaceTor.tor` uses the first-factor convention required by the Tor node.
The global chart's pointed lift is the Over morphism with underlying map t.
No mismatch remained in this reading, and no statement change was needed.


## New nodes

`def-trf-chart-strict-henselization-map` records the existing canonical
`AlgebraicGeometry.EtaleLogStructure.chartStrictHenselizationMap` and its supporting
`AlgebraicGeometry.strictLocalRingIsoStrictHenselization` in
`Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction`. Its source is ILO VI
1.1--1.2, p. 69, and VIII 3.4.1 / proof of 3.4.3, p. 110. The new node introduces
exactly a scheme X, log structure M, geometric point x, pointed etale W,w, additive
commutative P and section homomorphism c. The Lean binders are `{X : Scheme.{u}}`,
`M : EtaleLogStructure X`, `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`, `x`, `W`, `w`,
`{P : Type u} [AddCommMonoid P]` and `c`. The definition's body composes c, the
monoid germ, `stalkAlpha` and the canonical ring-colimit isomorphism, exactly the
four arrows in its statement. The supporting isomorphism uses finality and the
specified representative-colimit comparison, so no arbitrary ring map is supplied.
The general construction needs no chart or log-regularity hypothesis. It applies
to the identity etale neighbourhood in the item. The node cites the definitions
of log structures, geometric points, strict henselization and geometric stalks.

`def-trf-monomial-quotient-tor` records the existing
`AlgebraicGeometry.LogChartFaceTor.ideal`, `.coefficients` and `.tor` in
`Sheaf.TraceFormula.LogChartFaceTorComparison`. Its source is ILO VIII, proof of
3.4.3, p. 110, and VI 3.7(a), p. 75. The binders `{P A : Type u} [CommMonoid P]
[CommRing A] (a : P →* A) (H : Set P)` give exactly a commutative monoid, ring,
structural homomorphism and arbitrary subset. `ideal H` is the span of the basis
monomials indexed by H; `coefficients a` restricts the ordinary A-module A along
`MonoidAlgebra.lift ℤ A P a`; `.tor` applies `Tor' ... 1` to the quotient first and
that coefficient module second. Thus the coefficient action and derived-factor
convention are fixed. For a monoid ideal the generated ring ideal is the integer
span of H by stability under monomial multiplication. Empty H gives the zero
ideal and total H the unit ideal. No fs, sharpness or local assumption is added.
The node cites `def-weil-pbc-tor-modules` and supplies no new Tor construction.

For each node, the `mathlib_searches` contain the literal outputs of fresh
`msearch.py` LeanSearch, LeanFinder (chart) / Loogle (Tor), and Mathlib grep
queries, followed by literal `rg` results from `lean/WeilConjectures`, `lean/Sheaf`
and `dag/nodes`. Chart queries: "Canonical structural map from a log chart to the
strict henselization using the geometric stalk"; "Log structure chart monoid map
to affine pointed etale neighbourhood strict henselization colimit"; and
`chartStrictHenselizationMap|strictLocalRingIsoStrictHenselization|strictLocalRing`.
Tor queries: "First Tor of quotient of integer monoid algebra by monomial ideal
with coefficients restricted along monoid map"; `"Tor", "MonoidAlgebra"`; and
`monomial.{0,30}[Tt]or|[Tt]or.{0,30}monomial|LogChartFaceTor`.
The Mathlib hits do not define these composites. Project searches locate exactly
the reused declarations; DAG searches find their helper-name entries only on the
two theorem records, whose conclusions are contraction and Tor comparison.
Definition-statement searches across the DAG find no existing definition node for
either composite. `tools/blueprint_refs.py search 'chart strict henselization'`
and `... search 'monomial quotient Tor'` find no blueprint node;
`... ancestor lem-trf-log-chart-strict-local-tor` gives
`lem-trf-local-term-locality`, used in both new nodes with the item's ancestry
prepended. Existing declarations are reused without copying modules or editing
landed theorem records, as the independent return specifically requests.

## Repair self-check by Q85

I reopened both new JSON nodes beside the unchanged helper definitions and the
item module. Each existing record's main signature is extracted verbatim from
its owning source; `lean.declarations` names precisely the supporting helpers it
owns. The item signature remains byte-identical to the returned packet. Its chart
map is now represented by the chart-map definition node, and its Tor/ideal/action
by the monomial-quotient definition node; neither of the removed theorem entries
is used as a hypothesis or through its conclusion. The comparison theorem remains
available for proof step 5 through the unchanged `proof_deps`. All original
hypothesis and edge-case checks in the second reading above still apply.
No new Lean file, theorem, proof, statement correction or axiom is introduced.
The first saved-packet dry run passed, but this ownership repair was still made
to address the independent finding H2/H12 rather than re-push the unchanged head.


The repaired-packet dry run requested the current node schema's `import_flags`
field; both new definition nodes now carry `import_flags: []`. Existing definition
signatures are recorded from the keyword `def` through their result type, omitting
the preceding `noncomputable` modifier, to agree with the server signature reader.
This changes neither declaration nor mathematics. The explicit server compile
of the unchanged item passed for both the sandbox and actual module (1.6 s each),
with no diagnostic. A separate dependency-closure check found 695 nodes and no cycle.
