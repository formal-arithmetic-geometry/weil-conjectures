## Worker report

The delivery states `WeilConjectures.adicSectionClosedSupport` in
`Sheaf.Paper.AdicSectionClosedSupport`, with `sorry` as its entire proof. Four real
helper definitions package the theorem's support and restriction clauses. There
are no new DAG notions, dependency repairs, statement corrections or disputed
statements. The natural-language statement and seven-step proof remain unchanged.
The already landed `def-weil-derived-pullback-tensor-hom` is added to `stmt_deps`
because the restriction clauses explicitly use its canonical pullback functors.

### Hypotheses and clauses

- Global finite-field datum: `(D : FiniteFieldDatum.{u})`; its fixed algebraic
  closure is `D.k`, with all structure instances inherited from the datum.
- Prime distinct from the characteristic: `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  Inverse instances required by the existing pullback API are constructed using
  `smoothQbarResidueInvertible D l hl`; no invertibility assumption is added.
- The specified coefficient closure: `(Qbar : Type v) [Field Qbar]
  [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]`. The coefficient and
  site universes remain independent. Common fibres have module universe
  `max (u + 1) v`, exactly as the recorded intrinsic fibre interface requires.
- A separated finite-type k-scheme: `(T : Scheme.{u})` with
  `[T.Over (Spec (.of D.k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of D.k))]`,
  `[QuasiCompact (T ↘ Spec (.of D.k))]` and `[IsSeparated (T ↘ Spec (.of D.k))]`.
  Finite type is locally finite type plus quasi-compactness. No model over k₀,
  properness, smoothness, connectedness, lissity, or Weil structure is assumed.
- Finite coefficients: every `L : Padic.FiniteCoefficientFields l Qbar` occurs.
  `AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L` is the recorded
  canonical small model of this actual subfield. Its embedding into Qbar is
  `sfAdicCoefficientEmbedding`. This is the project's finite-stage convention,
  not a restriction on which finite subextensions occur.
- Finite-stage heart object: `M : sfRationalHeart l (Coefficient ... L) T`.
  The section has type `rationalCohomologyCoefficient D l hl (Coefficient ... L) T
  ⟶ M.obj`. The source is the recorded rationalization of the completed regular
  coefficient sheaf, not a discrete non-torsion constant sheaf.
- Common-stage heart object: `M : sfCommonStageHeart l T Qbar`. The section
  has source `(GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
  (rationalCohomologyCoefficient D l hl (Coefficient ... L) T)` for any finite L, giving
  the coefficient unit in its actual finite-stage presentation. M need not have
  the same stage as this presentation; its arrow is an arbitrary quotient arrow.
- The support S(t): `∃ S : Set T` together with the equivalence in
  `A1RationalSectionSupport`: `(sfAdicRationalFiber ... x).map t ≠ 0 ↔
  (SpecToEquivOfField Ω T x).1 ∈ S` for every algebraically closed geometric
  field `Ω : Type u` and every `x : Spec (.of Ω) ⟶ T`. Thus it is exactly the
  nonzero-fibre set, and the equivalence holds simultaneously for every lift of
  every underlying point. No choice of one geometric lift is assumed.
- Zariski closedness: `IsClosed S` on the underlying scheme space.
- Restriction to the open complement: for every `U : T.Opens` with
  `(U : Set T) = Sᶜ`, `(a1RationalOpenRestriction ... U).map t = 0`.
  The helper is precisely `rationalDerivedPullback l E U.ι`, with the existing
  residue-field inverse instances supplied. Because S is closed, its open
  complement exists. This quantification is the same restriction assertion,
  independent of which equal `Opens` wrapper is used, and adds no conclusion
  about restriction to unrelated open subsets.
- Finite extension: for every `N` and `h : L ≤ N`, the SAME S satisfies the entire
  support-and-zero-restriction predicate for
  `(GeneralAlgebraicallyClosedCoefficients.transition l Qbar T L N h).map t`.
  This is the actual completed tensor scalar extension, including identity maps.
  Its source is the scalar-extended coefficient unit, canonically the unit at N;
  changing by that source isomorphism does not change zero or nonzero of maps.
- Passage to Qbar: the SAME S satisfies `A1CommonSectionSupport` for the image
  under `GeneralAlgebraicallyClosedCoefficients.inclusion L`. This is the actual
  common-stage inclusion, not a freely chosen functor.
- For arbitrary common-stage sections the second main conjunct gives a closed S
  with the same support and restriction assertions. Its fibre clause quantifies
  over every F satisfying `SfAdicCommonFiberSpec`. That predicate normalizes F
  naturally on every finite stage by the actual adic rational fibre followed by
  ordinary scalar extension along the actual field inclusion. Existence is the
  recorded `sfAdicCommonFiber_exists`; hence this is not a vacuous universal.
  All normalized functors have the same zero maps by the natural comparisons on
  common-stage representatives, so the assertion is independent of that
  presentation as well as of geometric lifts. No arbitrary fibre data is chosen.
- Common restriction is exactly `commonStageDerivedPullback l Qbar U.ι`, with
  the same derived inverse instances installed, and the equality is with the
  actual zero arrow. No new pullback construction is introduced.

### Dependencies read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including
  its fixed field and algebraic-closure structures, publicly re-exported through
  the coefficient and cohomology imports.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no
  declaration; the stated Mathlib properties `Scheme.Over`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` render its relevant clauses directly.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeart`, `sfCommonStageHeart`,
  and their intersection-of-standard-classes predicates, read with their full
  definitions and the t-structure and abelianity statements.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` publicly preserves
  `Sheaf.Paper.OrdinaryCompactCohomology`, whose `rationalCohomologyCoefficient`
  is the completed rational coefficient unit. The common-stage unit is its image
  under the recorded inclusion, exactly the scalar-extension construction in the
  node. The
  cohomology and Frobenius-bearing output functors are not used in this theorem.
- `Sheaf.Paper.AdicHeartIntrinsicFibres`: `sfAdicRationalFiber`,
  `sfAdicIntegralFiber`, `sfAdicCoefficientEmbedding`, `SfAdicCommonFiberSpec`,
  and `sfAdicCommonFiber_exists`, read with their normalization specifications.
  Its imported original `AdicHeartPullbackFibres` supplies the raw finite/common
  standard, pullback, fibre, scalar, and support interfaces. The intrinsic
  transport is used rather than defining another rational or common-stage heart.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback` and
  `commonStageDerivedPullback`, whose unique-descent specifications fix the
  completed integral action and the normalized common-stage representative maps.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `transition`,
  `stageSystem`, and `inclusion`, as re-exported by the preceding dependencies.
- `Sheaf.Paper.SmoothPurityQbar`: `smoothQbarResidueInvertible`, as re-exported
  through the recorded ordinary-cohomology interface, supplies only the
  canonical inverse of l in each residue field from `hl`.

The proof-only imports are `LocalizedTStructure`, `PbcRationalCategory`,
`PbcQbarCategory`, `EtaleSectionZeroOpen`, `PurLisseMorphismRigidity`, and upstream
`WeilConjectures.Mathlib.Topology.NoetherianSpace`. The recorded modules and the
relevant complete signatures/docstrings were read. The proof dependency
`lem-a1-integral-constructible-reduction-fibres` currently has neither a Lean
record nor a mathlib match and is not imported. It is needed only to prove this
node, not to type its statement; no duplicate or placeholder of that independent
lemma is introduced. The proof docstring retains its complete role in steps 2–5.

### Sources and edge cases

Read the local Bhatt–Scholze PDF at Propositions 6.8.4(1), 6.8.11, 6.8.14,
Definitions 6.8.6 and 6.8.10, and Remark 6.8.15. The source identifies the
constructible rational category with rationalization of the completed integral
one and describes finite-stage descent. The node explicitly identifies closed
support as the seven-step agent-formulated consequence of these results; it is
not a verbatim claim in the paper. The proof docstring includes all seven steps,
including ordinary integral quotients, torsion, the finite connected
stratification, and the two distinct stabilization/localization arguments.

Checked mathematically before writing: empty T (S is empty and its restriction
is zero); zero M and zero section (S empty); everywhere nonzero section (S all T,
empty complement); integral torsion sections (localization criterion removes
all torsion germs); non-lisse constructible M; identity finite extension; proper
finite extension; finite-stage source and arbitrary-stage target over Qbar;
independence of finite-stage representatives; unrestricted coefficient closure
universe. No freeness, concentration of derived reductions, or stabilization of
arbitrary increasing closed sets is asserted.

### Searches

All remote searches used the prescribed `msearch.py Q70
lem-a1-adic-section-closed-support` wrapper.

- LeanFinder query: “A section of a constructible rational adic sheaf has Zariski
  closed nonzero geometric fibre support”. Eight hits, principally
  `Scheme.IdealSheafData.isClosed_supportSet`, `supportSet`, and structure-sheaf
  section results; the returned signatures concern O_X-ideals or O_X-sections,
  not the adic coefficient heart or its section maps. No exact match.
- LeanSearch query: “A section of a constructible l-adic sheaf has closed nonzero
  stalk support”. Eight hits: ideal-sheaf support, `Scheme.zeroLocus_isClosed`,
  `RingedSpace.zeroLocus_isClosed`, `isClosed_tsupport` and related ideal-sheaf
  results. None have the coefficients or statement of this node; tsupport
  already takes a closure and would weaken the assertion. No exact match.
- Loogle query: `IsClosed, CategoryTheory.Functor`. Five hits concerning TopCat
  colimits, inverse limits of schemes, partial sections, and Galois automorphism
  topologies. No exact match.
- Mathlib grep query: `section.*support|support.*section` in AlgebraicGeometry.
  One hit, the `section support` heading in IdealSheaf/Basic. No exact match.
- Local project/source grep: `adic.*[Ss]ection|[Ss]ection.*[Ss]upport`, plus
  the exact node id in the upstream WeilConjectures source. No upstream adic
  section theorem with this statement. The side project has various ordinary
  and supported-section constructions, but no version of the present result.
- Name-collision search for `AdicSectionClosedSupport|A1RationalSectionSupport|
  A1CommonSectionSupport|adicSectionClosedSupport` in the upstream-name index,
  Mathlib, upstream WeilConjectures, and side Sheaf source returned no matches.

### Validation

The first scompile.py run found the older `qbarCohomologyCoefficient` helper
restricts the coefficient closure to `Type u`. Replaced its use by the already
recorded common-stage inclusion applied to the rational coefficient unit, the
canonical scalar-extension formula of the node. No new unit, universe equality,
or assumption is introduced. This also presents the source of an arbitrary
common-stage section in the exact same form as the finite-stage passage clause.
Final compilation and dry-run results follow below.

Final scompile.py passed with no errors or warnings: sandbox 8.2 seconds;
library-path confirmation 39.7 seconds. Only the named theorem uses `sorry`;
the four definitions have real data. The node signature was checked against the
file verbatim; the only changed fields are lean and the permitted added landed
statement dependency. All Lean lines are at most 100 characters.

## Second reading by Q70

Independent maintainer second reading, 2026-10-18. I did not author or previously
second-read this delivery. Reviewed the immutable snapshot at
8db029e8938e3066097539eed5746435402be358, starting with packet.md and reading
check-brief2.md in full. The mathematical statement and Lean module need no change.
This replacement report supplies the substantive second reading missing from the
delivered placeholder (delivery-errors H1/H11).

### Objects, hypotheses, and conclusions

1. The fixed finite-field datum is `D : FiniteFieldDatum.{u}`. Read its actual
   structure in FiniteFieldFiber: prime p, positive exponent, finite base field,
   and fixed algebraic closure. `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give
   exactly the coefficient-prime assumptions. The restriction helpers derive
   residue-field invertibility using `smoothQbarResidueInvertible`; they add
   no invertibility, smoothness, or properness hypothesis.
2. `T : Scheme.{u}`, its `Over` instance, `LocallyOfFiniteType`, `QuasiCompact`,
   and `IsSeparated` on its structure map express precisely a separated
   finite-type k-scheme. The scheme-properties dependency is a convention node;
   these are its specified Mathlib notions. No descent to k0 is required.
3. `Qbar : Type v` with the field, Padic algebra, and `IsAlgClosure` instances
   is the specified coefficient closure. All actual finite intermediate fields
   occur as `Padic.FiniteCoefficientFields l Qbar`. Their `Coefficient.{u}`
   models are canonically equivalent small models, not selected special fields.
   Site universe u and coefficient-closure universe v are independent.
4. `sfRationalHeart` and `sfCommonStageHeart` are the recorded full subcategories
   defined by intersecting the standard degree-zero classes. Read their
   definitions and t-structure specifications in SfConstructibleHeart. These
   are constructible adic hearts, with no lissity or freeness assumption.
5. Read `rationalCohomologyCoefficient` through the public imports of
   CommonStageCompactWeilCohomology and OrdinaryCompactWeilCohomology to
   OrdinaryCompactCohomology: it is `constantWeilRationalObject`, the
   rationalization of the completed integral unit. No Weil structure is asked
   of M or t. In the common-stage conjunct the source is the actual finite-stage
   inclusion of this unit, for every stage L and arbitrary common-stage target.
   This handles source and target represented at different finite stages.
6. `A1RationalSectionSupport` asserts `IsClosed S` and the equivalence between
   membership in S and nonzero image of t under `sfAdicRationalFiber`, for every
   algebraically closed geometric lift. Thus it describes the exact nonzero
   locus, not its closure, and gives independence of the lift. Geometric fields
   in Type u suffice: algebraic closures of all residue fields live there.
7. The last clause of each support predicate sets the actual open-pullback map
   to zero on every open whose underlying set is the complement of S. Closedness
   ensures such an open exists. Both restriction helpers are exactly the
   recorded `rationalDerivedPullback` or `commonStageDerivedPullback` at U.ι.
   Read their unique-descent specifications in DerivedPullbackTensorHom,
   including their integral object action and rational/common-stage arrow action.
8. The same existential S is used for every finite transition L ≤ N and for
   inclusion into Qbar. Read `GeneralAlgebraicallyClosedCoefficients.transition`
   and `inclusion`: these are completed rational scalar extension and the actual
   stage-system inclusion, respectively. Scalar-extended units are canonically
   units, so the generic-source support predicates introduce no stronger claim.
9. `A1CommonSectionSupport` quantifies over every fibre satisfying the recorded
   `SfAdicCommonFiberSpec`. Read this predicate, `sfAdicIntegralFiber`, the unique
   rational descent, the actual coefficient embedding, and
   `sfAdicCommonFiber_exists` in AdicHeartIntrinsicFibres. The specification is
   natural finite-stage normalization by actual scalar extension; its existence
   theorem makes the quantification nonvacuous. Its module universe is exactly
   `max (u + 1) v`. No arbitrary fibre functor or universe equality is assumed.

### Source and proof reading

Read the local Bhatt--Scholze PDF, printed pages 59--62: Proposition 6.8.4(1),
Definitions 6.8.6 and 6.8.10, Propositions 6.8.11 and 6.8.14, and Remark 6.8.15.
These give the integral constructible models and rational/common-stage categories;
the closed-support result is explicitly an agent-formulated consequence, not a
claim that every constructible sheaf has closed support. Also read Stacks
etale-cohomology.tex, labels lemma-zero-over-image and
lemma-support-section-closed (Tags 04FR/04FT, lines 3943--4052).

Checked all seven node proof steps against the module docstring and the statements
of the cited nodes. Step 1 uses the essential-image description of the localized
heart and localized Hom modules; one denominator suffices for the section.
Step 2 uses precisely the ordinary quotient, common stratification, transition,
and fibre-normalization clauses of lem-a1-integral-constructible-reduction-fibres.
It does not assert derived reductions are concentrated in degree zero. The finite
connected refinement follows from the recorded noetherian connected-component
results, read in the group clone's WeilConjectures/Mathlib/Topology/NoetherianSpace.
Step 3 uses etale_section_zero_open on the identity etale object and ordinary
finite-lisse morphism rigidity on each connected stratum; the strata remain
separated finite type, and the coefficients are exactly A/varpi^n.
Step 4 is elementary: an increasing family of unions of one finite set of strata
attains its union. It does not claim that noetherian spaces have stabilizing
increasing closed chains. Step 5 is the elementary localization criterion and
an arbitrary intersection of closed sets. Step 6 uses exactness and joint
conservativity on the heart via the image of the map; the open complement is
again finite type. Step 7 uses faithful field extension and finite common-stage
descent. These are the assertions supplied by the cited dependency statements.

The reduction-fibre lemma has no recorded Lean module yet. It is a proof-only
prerequisite: no object or map in this statement depends on an absent declaration.
Leaving its import absent is appropriate for this stage-2 sorry statement; this
is not a missing helper needed to type the theorem. No new node or dependency
repair is required. No statement correction or citer audit is required.

### Searches, edge cases, and maintainer gates

Ran independent msearch.py searches: LeanSearch for a section of a constructible
rational adic sheaf having closed nonzero geometric fibre locus (8 hits), and
Loogle `IsClosed, CategoryTheory.Functor` (5 hits). None matches: the returned
scheme/ringed-space zero loci and ideal-sheaf supports concern structure sheaves,
and the other results concern limits or Galois topology. Searched Mathlib's
AlgebraicGeometry and both project/source Lean trees for section/support terms
and the five delivered declaration names. Read the ideal-sheaf support signatures
and the upstream AffineLine/Endpoints context: neither states this general adic
section theorem. No duplicate notion or declaration was found. The support
predicates only package the item's clauses; the restriction helpers specialize
existing pullbacks rather than introduce a second construction.

Checked empty T, zero M, zero t, full support/empty complement, torsion integral
germs killed by rationalization, non-lisse constructible M, n=1 in the proof,
identity and proper finite coefficient extensions, different source/target
common stages, and independent u/v. No excluded edge case was found. The main
theorem does not retain the section's unused E variable as an extra parameter.
All variables and universes are explicit; autoImplicit and relaxedAutoImplicit
are false. Every declaration has source and blueprint documentation; the theorem
docstring contains all seven proof steps. The four definitions have real bodies,
and the sole theorem has exactly `by sorry`. All lines are at most 100 characters.
The item's lean.statement was compared programmatically with the signature in
the immutable module and is verbatim equal. All five declarations are recorded.

Read the route-pivot dropped list through the shared read-only Git ref. Its
intersection with the item's statement/proof dependencies is empty. The current
ref has no item repair-note file. The delivered proof and module introduce no
enhanced localization, model category, straightening, or operad machinery.
Ordinary finite-stage pair-category descent is not the dropped coherent-section
machinery. No pro-etale substitute is attached to a different target.

### Reproduced compiler evidence and disposition

Ran exactly:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q70 lem-a1-adic-section-closed-support snapshot/lean/Sheaf/Paper/AdicSectionClosedSupport.lean`.
Exit 0, no errors or warnings. The sandbox check took 7.9 seconds and the
library-path confirmation took 11.6 seconds. The installed wrapper explicitly
uses the server overlay and confirmation, despite older local-overlay wording
in the brief; it compiled the actual immutable file without any manual SSH or
live-library write. This independently confirms the worker's recorded clean
per-file result (its earlier timings were 8.2 and 39.7 seconds).

Disposition: FIX, report only. The delivered second-reading section was a
placeholder and did not satisfy H1/H11 or the explicit maintainer requirement
for a real section. This replacement retains the worker report verbatim and
supplies the independent reading. No mathematical, Lean, or JSON changes are
needed. No build, claim, delivery, merge, Git mutation, or project-clone edit was
performed. All review writes are confined to the authorized review directory.
