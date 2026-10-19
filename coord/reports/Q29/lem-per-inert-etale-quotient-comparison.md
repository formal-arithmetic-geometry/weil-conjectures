## Worker report

The module `Sheaf.AlgebraicGeometry.InertEtaleQuotientComparison` states this item's
scheme and log assertions. Its only definition, `AlgebraicGeometry.inertEtaleLocus`,
is the actual subset defined by equality of geometric stabilizers. All five theorem
proofs are `sorry`. Their docstrings give all fourteen DAG proof steps and sources.
No independent quotient construction, log structure, group action, or strictness
predicate is introduced. There are no new nodes or dependency repairs.

Hypothesis and clause correspondence:

- A finite group is `(G : Type v) [Group G] [Finite G]`; its universe is independent
  of the schemes' universe. Actions are `G →* Aut V` and `G →* Aut U`.
- The separated, locally Noetherian schemes are `[V.IsSeparated] [U.IsSeparated]`
  and `[IsLocallyNoetherian V] [IsLocallyNoetherian U]`. These are absolute scheme
  separatedness, not properness or separatedness over an additional chosen base.
- Invariant affine open covers are `haV` and `haU`: every point belongs to an affine
  open whose membership is preserved and reflected by each action automorphism.
- The map is `(h : V ⟶ U) [Etale h]`. `hequiv` is precisely the commuting action
  square. Geometric points are `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and maps
  `Spec (.of Ω) ⟶ V`; `t default` is their underlying point.
- In `inertEtaleLocus`, the biconditional for every `g` is equality of the two
  geometric stabilizer subsets, including nonfaithful actions. Quantifying all
  lifts over the same underlying point makes this an actual subset of V.
- `isOpen_inertEtaleLocus` asserts both `IsOpen` and invariance of membership.
  After this localization, `hinert : ∀ x, x ∈ inertEtaleLocus ...` is exactly the
  instruction to restrict to the inert locus, without imposing inertness on the
  original scheme when asserting openness.
- `qV`, `qU`, `hqV`, and `hqU` use the already landed
  `IsAdmissibleFiniteSchemeQuotient`: finite, invariant, quotient topology (hence
  surjective), underlying orbit fibres, and injectivity with image the invariants
  on every open. The already assumed invariant affine covers imply its
  orbit-in-an-affine condition. The underlying orbit condition and quotient
  topology also follow from the node's finite surjective geometric quotient
  assumptions. `horbitV` and `horbitU` retain the specified stronger, geometric
  orbit-fibre statement, on morphisms from each fixed algebraically closed field.
  No categorical quotient universal property is imposed as a new hypothesis.
- `inert_etale_quotient_comparison` produces `hb`, its normalization
  `hc : h ≫ qU = qV ≫ hb`, `Etale hb`, and `IsIso (pullback.lift h qV hc)`.
  Thus the asserted isomorphism is the canonical one with the two prescribed
  projections. The explicit action equation makes it equivariant for the action
  on the U factor and the identity on VQ. The final uniqueness clause specifies
  the induced map on quotients, rather than choosing an unrelated map.
- For the additional log clause, `V U : FineSaturatedLogScheme` packages precisely
  the original locally Noetherian schemes and their fs log structures. The
  actions are `FSLogGroupAction`; `h : EtaleLogHom V U` supplies its specified log
  map. `hstrict : h.toLogMap.IsStrictEtale`, together with the existing underlying
  étaleness, is the recorded strictness criterion. `hequiv : aV.IsEquivariant aU h`
  is the explicit source-based correction described below. `htV`, `htU` are
  `IsVeryTame`, including tame geometric inertia, trivial characteristic action,
  and trivial action on the strict local stratum. No freeness, log regularity,
  or invertibility of the whole group order is imposed.
- The log theorem takes `hb`, `hc`, and `hcart` already supplied by the scheme
  assertion. It therefore needs no second independent inertia hypothesis.
  `NV` and `NU` are arbitrary `EtaleLogStructure`s on the quotient schemes,
  with `dV : aV.InvariantDirectImage qV NV` and its U analogue. These identify
  sections, structure maps and restrictions with the actual invariant direct
  images. In particular, no fs hypothesis is added on either quotient.
- The conclusion produces `H : NV.HomAlong NU hb` with `H.IsStrictEtale`.
  The equality following it identifies the map after the injective invariant
  direct-image embeddings with the given pullback by h, on every relative test
  diagram. This is the induced quotient log morphism and its strictness, not a
  bare existential isomorphism. It also fixes its compatibility with all section
  restrictions and hence with iterated restriction/composition.
- `inert_etale_comparison_baseChange` is the actual equality of the canonical
  comparison maps after arbitrary quotient base change, including quotient
  opens, pointed étale neighbourhoods and their identity refinements.
  `inert_etale_comparison_comp` is the equality for two composable comparisons.
  These universal-property equalities do not require redundant inertness or
  quotient hypotheses: they apply, in particular, to the maps just constructed.
  Inertness itself composes because equality of stabilizers is transitive.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separatedness import:
  `AlgebraicGeometry.IsSeparated`, `Scheme.IsSeparated`; only separatedness is used.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `Mathlib.AlgebraicGeometry.ResidueField`: `IsAlgClosed`, `Scheme.SpecToEquivOfField`;
  the recorded inline geometric-point representation is used.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, through the recorded
  finite scheme quotient predicate.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its
  projections, `pullback.lift`, `pullback.map`, and `pullback.condition`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `FineSaturatedLogScheme`, `EtaleLogHom` and its actual relative section maps.
- `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`:
  `IsAdmissibleFiniteSchemeQuotient` (already landed definition node).
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`, `IsEquivariant`,
  `logInvariantTest`, `invariantLogSections`, and `InvariantDirectImage`.
- `Sheaf.AlgebraicGeometry.VeryTameFSLogAction`: `FSLogGroupAction.IsVeryTame`.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`: `EtaleLogHom.toLogMap`
  and `EtaleLogMap.IsStrictEtale`, retaining the fs map's data without a new copy.
- `Sheaf.AlgebraicGeometry.FineLogSchemeMorphisms`:
  `EtaleLogStructure.HomAlong` and `HomAlong.IsStrictEtale`, whose quotient
  endpoints need not be fs.

All recorded proof-dependency modules are imported without `public`; Mathlib
leaves use the files in their `mathlib_match`. No proof dependency is treated as
a statement hypothesis. The legacy `LogFanChartBlowup` source has no `module`
header in the compile environment, so its strictness interface cannot be imported
from this module. Using the already recorded strict-étale interface above avoids
that import and states the same strictness for the étale map in this item.

Sources read: Stacks `groupoids.tex`, lemma-etale (0DT9), with its hypotheses and
proof, and ILO VIII 5.3.6--5.3.7, 5.4.1--5.4.2, printed pp.124--127 (PDF
pp.130--133). This is a supporting node, not the blueprint unit's own statement.

Edge cases checked: empty schemes and empty inert locus give vacuous membership
and the usual empty quotient; the trivial group gives the original étale map;
nonfaithful actions and stabilizer equal to the whole group remain allowed; free
actions use trivial geometric stabilizers. Positive characteristic dividing |G|
is allowed in the scheme theorem. The log assumptions only invert geometric
stabilizer orders. The unit and zero-ring cases are not excluded. No characteristic,
connectedness, reducedness, quotient Noetherianity or quotient fs condition was added.
Geometric fields use the same universe as schemes, so the tests are not vacuous.

Searches (through the prescribed msearch wrapper):

- LeanFinder: “An inert equivariant etale morphism for a finite group induces an
  etale map on scheme quotients and a cartesian square, strict on log quotients”.
  Eight hits concerned étale morphisms, composition and base change; none supplied
  the quotient comparison or log clause.
- Loogle: `AlgebraicGeometry.Etale, CategoryTheory.IsPullback`: zero hits.
- LeanSearch: “inert equivariant etale morphism finite scheme quotient stabilizers
  invariant open locus”: eight ordinary étale/locus hits, no full match. Search
  services use `IsEtale` names from another Mathlib version; the pinned source's
  `Etale` class was read rather than copying the search result's signature.
- Mathlib grep: `inert|[Qq]uotient|stabilizer` in
  `AlgebraicGeometry/Morphisms/Etale.lean`: zero hits.
- `rg` in the named upstream source for the item id: no attachment. Searches for
  inertia found fundamental-group and prime-ideal inertia, not this comparison.
- `rg` in `lean/Sheaf` for `VeryTame`, `FSLogGroupAction`, quotient and strictness
  found the five existing definition nodes now cited by the item. Their modules,
  signatures and docstrings were opened and reused. Searches for
  `inertEtaleLocus` and `inert_etale_quotient_comparison` found no prior declaration.
- DAG grep and `tools/blueprint_refs.py search inert` found the existing item and
  its toric-chart citer; no duplicate full assertion or existing inert-locus definition.

## Statement corrected

The old statement is retained verbatim in the node's
`statement_change.old_statement`. Its log clause said only “h is strict, both
actions are very tame”; the earlier G-equivariance assertion applied to the
scheme morphism, before log structures were supplied. It did not require that
the specified log map commute with the log actions. The correction makes that
requirement explicit and cites existing definitions. The scheme hypotheses and
all conclusions remain unchanged. Only `statement`, `stmt_deps`, `lean`, and the
required `statement_change` record change; proof and proof_deps are untouched.

This is necessary, not an extra assumption introduced to ease the proof. For a
concrete diagnostic, take a characteristic-zero log point with stalk monoid
kˣ × N, with positive-degree elements mapped to zero. Give the underlying point
the trivial Z/2 action. One log action is trivial; the other sends (u,n) to
((-1)^n u,n). Both are very tame: the characteristic N and the stratum k are fixed,
and 2 is invertible. The identity log map is strict and its underlying scheme map
is equivariant, but it does not commute with these log actions. Pullback of an
odd-degree invariant section for the trivial action is not invariant for the sign
action. Thus the claimed induced log map cannot even be obtained from that map.
ILO VIII Proposition 5.4.2 explicitly assumes a strict inert lambda-equivariant
morphism of fs log schemes; the corrected clause is its equal-group étale case.

Complete citer audit, found by the prescribed grep and checked by actual
stmt_deps/proof_deps membership:

- `lem-per-gabber-abelian-stage-toric-chart`: holds. The comparison is a strict
  equivariant map of log pairs constructed from equivariant charts. The invariant
  enlarged boundary and its strict inverse image give log equivariance. Both
  its enlarged-quotient and retained-boundary uses still satisfy the corrected
  hypothesis. No citer file was edited.

## Second reading by Q29

I reopened the node and Lean file for a separate in-thread pass. This is not
claimed as an independent worker review: the dispatcher explicitly forbids other
agents, and the maintainer supplies the independent review after this delivery.

I checked the field-universe tests, the direction of h, both quotient maps, the
orbit biconditionals, and the Aut multiplication convention. The comparison is
`V → U ×_{UQ} VQ`, not the opposite projection or an arbitrary map. I checked
that absolute separatedness, invariant affine covers, and local Noetherianity
appear in the scheme assertions, and that no tame assumption leaks into them.
For the log clause I checked the definition bodies of `IsVeryTame`,
`InvariantDirectImage`, and both strict-étale predicates: they use actual log
sections, units and the nonunit-ideal stratum, and do not assume fs on the quotient.
The canonical section equation has target E over UQ and source F over VQ, with
both fibre-product projections fixing its lift. This fixes the direction of the
induced log morphism and forces the intended section pullback. The source-based
log-equivariance omission was corrected and its only citer audited above.

Compiler feedback found that the legacy general strictness module cannot be
imported from a module-system file; I replaced its interface with the existing
strict-étale predicate appropriate here. I also supplied the explicit targets and
commutativity certificates in the base-change and composition pullback terms.
No theorem proof was filled. A final compiler style warning was repaired by
wrapping the composition comparison line; clean validation is repeated below.
