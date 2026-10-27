## Maintenance handoff, 2026-10-25

The repeated preflight (c) blocker is fixed on authoritative sheaf-dag in server
commit e2289db2bb494e7ec081c6325853954b46ec17e3. Maintenance landed the already
accepted H2 ownership extraction separately: the two canonical definitions now
belong to def-trf-log-etale-restriction-stalk-comparison in
LogEtaleRestrictionStalkComparison. Both former theorem modules publicly import
it and their records cite the definition owner. The moved definitions are byte
identical except blueprint tags, and all remaining statements/proofs are unchanged.
The three shared modules compiled separately through tools/lean_file.sh with
60 seconds per file (3.9 s, 2.0 s, 2.3 s); incremental DAG validation passed.
Interface landing 20261024T201547-MAINTQ27-2791271 awaits normal global verification.

The six shared node/module copies have been retained beside their original paths
as *.maint-Q27-ownership-1792871880.bak and removed from delivery globs because
they are now on main. The active packet is only the item node, its module, and
this report. Keep the H7 proof_deps exactly as the base, ending in
lem-weil-pbc-basic-open-function; keep both theorem private imports absent.
Keep def-trf-log-etale-restriction-stalk-comparison and def-trf-log-regular-pair
in stmt_deps and the direct definition-module import. No statement correction,
new proof dependency, or additional mathematics is needed. The historical
BLOCKED entries below predate this fix. Run the normal deliver2.py --no-push,
then deliver normally on success for independent review of H7.

## Worker report

The new module `Sheaf.AlgebraicGeometry.FreeLogChartOrdinaryParameters` states
`AlgebraicGeometry.freeLogChart_ordinary_parameters`, with its sole proof `sorry`.
Four real helper definitions name the given chart's structural functions, their
ordinary and strict-local germs, and the increasingly ordered nonunit indices.
The H2 repair adds a definition node owning the two previously theorem-owned
canonical helpers. No statement correction or disputed statement is proposed.

Source read: ILO, Exposé VI 1.1--1.2 and 1.6--1.7, printed pp.69--70 (PDF pages
75--76). The node's seven proof steps are reproduced in the theorem docstring,
including the ordinary cotangent-space descent, not merely strict-local parameters.
The recorded definition dependencies and their actual Lean source signatures and
docstrings were read. The CompactObject example is now an empty withdrawn module;
this module follows the current module-mode header and public-section convention.

Hypothesis-by-hypothesis reading:

| Node | Lean |
| --- | --- |
| Locally Noetherian fs log scheme (X,M,alpha) | `X : FineSaturatedLogScheme.{u}`; its fields are the scheme, local Noetherianity, log structure with alpha and unit axiom, and fs chart condition. |
| X log regular | `hX : X.IsLogRegular`, the existing stratum quotient regularity and Krull-dimension equality at every geometric point. |
| Triviality locus U | `X.logStructure.trivialityLocus`, with no unrelated open or extra hypothesis. |
| Étale e:W -> X | `W : X.scheme.Etale`, with `W.hom` the specified morphism and `W.left` its source. |
| W affine and locally Noetherian | `[IsAffine W.left] [IsLocallyNoetherian W.left]`. |
| Inverse-image log structure | `N : EtaleLogStructure W.left` and `hN` identifying its full prelog structure, including alpha, with `X.logStructure.toEtalePrelogStructure.etaleRestrict W`. This names the stipulated object; it is not an independently constrained log structure. Étale inverse image is exactly slice restriction. |
| Free chart N^r, r >= 0 | `r : ℕ`, `β : Multiplicative (ULift.{u} (Fin r) → ℕ) →* ...`, and `hβ : N.IsChart (Scheme.Etale.mk (𝟙 W.left)) β`. ULift puts the finite index in the existing chart interface's universe without changing it. |
| Structural functions t_i and product f | `FreeLogChart.coordinate N β i` applies the existing alpha to the chart's i-th standard basis section; `∏ i, ...` is the actual product of these sections. |

Clause-by-clause conclusion reading:

| Node | Lean |
| --- | --- |
| The inverse-image structure is log regular | `∃ hfs : N.IsFineSaturated, FineSaturatedLogScheme.IsLogRegular ⟨W.left, inferInstance, N, hfs⟩`; fs is concluded, not assumed of N. |
| W is regular | `IsRegularScheme W.left`, the recorded locally Noetherian plus regular-stalks predicate. |
| e^{-1}(U) = D(f) | Exact equality of the preimage set under `W.hom` with the underlying set of `W.left.basicOpen (∏ i, coordinate ...)`. |
| Every w and geometric point above w | Universal `w`, `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, `t : Spec (.of Ω) ⟶ W.left`, and `ht : (Scheme.SpecToEquivOfField Ω W.left t).1 = w`. |
| B = O_{W,w} | `W.left.presheaf.stalk w`; `ordinaryCoordinate` uses the Zariski germ of the actual structural section. |
| A = B^sh | The recorded `Scheme.strictHenselizationRing t`, with all strict germs and the ideal transported by the existing `strictLocalRingStrictHenselizationIso W.left t`. This is the canonical affine-colimit object, not an arbitrary local ring or map. |
| J = the nonunit coordinate indices in B | Subtype `{i // ¬ IsUnit (ordinaryCoordinate N β w i)}` in the characteristic; the same predicate in `nonunitIndices` and the ideal-generating set. |
| Characteristic canonically N^J | `∃ E : N.characteristic t ≃* Multiplicative (J → ℕ)` plus its formula on EVERY chart monomial a: the class of the original log germ maps to the restriction `fun j ↦ a.toAdd j.val`. This fixes the canonical map, including the unit-coordinate face, rather than just asserting an unspecified isomorphism. |
| Nonunit log ideal in A is (t_j:j in J)A | Exact equality of `(N.nonunitIdeal t).map` along the canonical strict-henselization comparison with `Ideal.span {a | ∃ i, ¬ IsUnit (...) ∧ a = strictCoordinate N β t i}`. |
| Indexed list extends to parameters in A | Existential local/Noetherian structures for A and a completion list b, with `IsLocalRing.IsRegularSystemOfParameters ((nonunitIndices ...).map (strictCoordinate ...) ++ b)`. These structures are conclusions, not extra hypotheses. |
| Same assertion in B, on the given functions | A separate existential completion list b in the actual Zariski stalk and `IsRegularSystemOfParameters ((nonunitIndices ...).map (ordinaryCoordinate ...) ++ b)`. No associates, permutations or new étale neighbourhood are substituted. `nonunitIndices` filters the increasing `List.ofFn` enumeration of `Fin r`. |
| Empty J implies f is a unit in B | If every coordinate is a unit, `IsUnit (W.left.presheaf.germ ⊤ w ... (∏ i, coordinate ...))`. Universal unit membership is exactly emptiness of the displayed J. |
| Empty product is 1 | Explicit final clause `r = 0 → (∏ i, coordinate ...) = 1`. |

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure`, `EtalePrelogStructure.germ`, `EtaleLogStructure.IsChart`,
  `IsFineSaturated`, `characteristic`, `nonunitIdeal`, `trivialityLocus`,
  `FineSaturatedLogScheme.IsLogRegular` (public through the restriction module).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and its ordinary
  stalk Noetherianity instance; `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `Etale` and `Scheme.Etale` (publicly available through the dependencies).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `Scheme.strictHenselizationRing`, reached through the comparison module.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `strictLocalRing` and
  `strictLocalGerm`, explicitly owned by the added existing statement dependency
  `def-trf-log-regular-pair`.
- New node `def-trf-log-etale-restriction-stalk-comparison` owns
  `Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison`:
  `EtalePrelogStructure.etaleRestrict` and `strictLocalRingStrictHenselizationIso`.
  These are the same canonical definitions, now moved out of theorem modules.

Plain imports retain the existing statement's proof plan: ind-étale strict-local
invariance, the across-universes ind-étale definition, affine strict-local ring
comparison, strict-henselization Noetherianity, faithful flatness, regularity and
cotangent dimension, localization Noetherianity and the local Nakayama interface.
Other Mathlib proof leaves (affine stalk localization, regular-local cotangent
dimension, basic opens) are already available through the public dependency tree.

Edge cases checked before writing: r=0 gives the one-element chart monoid, product
1, empty nonunit list, and full triviality locus. At any point with J empty but r
positive, all functions are units and both empty lists extend by a whole parameter
system. Dimension zero forces J empty. At generic points, formerly nonunit global
functions can become units; J is recomputed in the ordinary stalk at each w, not
fixed at a distinguished chart point. The empty scheme gives vacuous local clauses
and the required equality of empty subsets. Repeated equal nonunit coordinates
cannot occur in a log regular free chart (their cotangent classes would be
independent by the asserted conclusion); they have not been forbidden by an added
hypothesis. Mixed characteristic, imperfect residue fields, nonclosed points and
arbitrary r are retained. No geometric coefficient field or universe equality
beyond the existing u-sized scheme/stalk interfaces is assumed.

Searches for an existing complete statement:

- `msearch.py ... leanfinder "In a log regular scheme with a free natural number
  monoid chart, nonunit chart coordinates extend to regular parameters in ordinary
  and strict local rings."`: eight hits, including StandardEtalePair and
  `LocallyRingedSpace.notMem_prime_iff_unit_in_stalk`; none states this theorem.
- `msearch.py ... loogle "IsLocalRing.IsRegularSystemOfParameters"`: no hits,
  unknown identifier in the remote search index; the actual project declaration
  was instead read directly and reused.
- `msearch.py ... grep "LogRegular|EtaleLogStructure|freeLogChart"`: no Mathlib hits.
- `msearch.py ... leansearch "regular parameters of a free logarithmic chart on a
  log regular scheme"`: eight unrelated hits (scheme constructors, free locus,
  smoothness, logarithmic derivative); no complete statement.
- `rg` of `EtaleLogStructure`, free-log-chart/parameter patterns and the exact
  node id in both `lean/WeilConjectures` and `lean/Sheaf`: no existing theorem
  matching this item; this located the existing restriction and canonical ring
  comparison helpers, both reused.
- `tools/blueprint_refs.py ancestor lem-trf-free-log-chart-ordinary-parameters`
  confirms the node's existing ancestry at `lem-trf-local-term-locality`.

Validation: the module compiled cleanly through scompile.py in both its sandbox
and library module names; all variables and universes are explicitly bound and
all lines are at most 100 characters. The only postponed proof is the item's
named theorem; each helper has real data, a source and the matching blueprint tag.

## Second reading by Q27

This is a separate self-audit pass with the node and final file open, not a claim
of an independent agent review: the dispatcher explicitly prohibits spawning
another agent and the maintainer independently reviews the delivery. I checked
each row above against the literal node and final signature. In particular, hN
identifies alpha as well as the monoid sheaf; N has no added fs assumption; E is
fixed on every original monomial; the ideal lives in the recorded A; both parameter
lists share the same ordered J and retain the given values; w is the point of the
specified geometric point; and the J-empty implication and r-zero identity are
both present. The maintainer found the dependency-ownership mismatch in the
returned version: two theorem nodes had been added only to obtain definitions.
This pass verifies their replacement by the new definition node, and the explicit
addition of def-trf-log-regular-pair for strictLocalRing and strictLocalGerm. The
item signature remains byte-for-byte the one the maintainer accepted. The moved
definitions have unchanged names, signatures and bodies; both theorem consumers
publicly import their new owner and retain all their statements and proofs.


## New nodes

`def-trf-log-etale-restriction-stalk-comparison` defines the restriction of a prelog
structure to an etale object by the slice-site equivalence and the canonical
comparison from its geometric structure-ring stalk to the affine-neighbourhood
strict henselization. Source: ILO VI 1.1--1.2, 1.6 (pp.69--70), VIII 3.3.8 (p.107),
with Stacks 00Y0 and 03EH for localization. This is an ownership extraction required
by the return, not a second construction: the exact existing declarations are
removed from the two theorem modules and moved into this module. Their docstring
blueprint tags now identify the definition node. Names, types and bodies remain
unchanged. The statement specifies both sectionwise restriction and the canonical
coprojection normalization of the colimit comparison; no arbitrary isomorphism or
Nonempty choice replaces it. Its definition dependencies include the existing fs
prelog interface, localized site, geometric stalk and affine-colimit strict
henselization nodes. Neither of the two theorem nodes is a statement dependency.

Searches before extraction: blueprint_refs.py searches for "etale restriction"
and "strict henselization" found no existing definition node that owns these two
helpers. Exact definition-id searches in dag/nodes and direct declaration searches
in Mathlib, WeilConjectures and Sheaf found no alternative definition owner; the
exact two declarations occur only in LogConditionFineChartLocality and
LogRegularCompletedChart. msearch leansearch for canonical prelog slice restriction
and geometric-stalk/affine-colimit comparison returned eight unrelated Zariski
restriction/global-sections hits. Leanfinder for the same constructions returned
eight ring-etale/standard-etale results. Mathlib grep for EtalePrelogStructure and
strictLocalRingStrictHenselizationIso returned zero hits. The new node records the
raw outputs and queries. The existing project's definitions are reused by moving
them, not duplicated. No local Noetherian or log-regular hypothesis is introduced
on these general constructions. Identity etale objects, empty schemes, arbitrary
prelog sheaves and all geometric points in the existing universe are included.

## Dependency modules

`lem-trf-log-condition-fine-chart-locality`: its record originally owned
EtalePrelogStructure.etaleRestrict, so citing it solely for restriction created an
unnecessary theorem statement dependency. The module now publicly imports
LogEtaleRestrictionStalkComparison and removes exactly that helper definition.
The lean record removes its name from declarations, with a repair note. The
unitSectionMap helper and all three theorem statements/proofs are unchanged.

`lem-trf-log-regular-completed-chart`: its record originally owned
strictLocalRingStrictHenselizationIso, so citing it solely for the canonical
comparison likewise created an unnecessary theorem statement dependency. The
module publicly imports the new definition owner and removes exactly the moved
definition. Its lean record removes that name, with a repair note. The chart ring
map, completed monomials, completed-chart theorem signature and proof are unchanged.
The module overview now describes the comparison as re-exported. Both consumer
modules are delivered and compiled separately as the required relocation repairs.
The item imports the definition owner directly and has no import or dependency
on either theorem node. Its proof_deps is exactly the base list.

## Repair of returned head 260b15ceef6c

H2 is repaired in all parts. The two theorem stmt_deps are removed relative to
the returned packet and replaced by the new definition node. The existing
`def-trf-log-regular-pair` is added to stmt_deps for strictLocalRing and
strictLocalGerm. One new module owns both extracted definitions, both former
owners publicly import it, and the item imports that definition module directly.
There is one declaration of each helper in the delivered source set. The item
signature and its four coordinate/list helper definitions are unchanged from the
returned delivery; the source-based statement is unchanged. Both theorem module
Lean records change only lean, and the new node has all required metadata.

The current main sources were checked directly with scompile.py --source for
both theorem modules before extraction: their declarations still matched the
local source used for the move. The delivery wrapper rebases the packet on the
current server main. All edits are in this sandbox. All four delivered modules
passed scompile.py per-file dependency-order compilation with no errors or warnings,
including the two existing consumers and the item importing the definition owner. The new definition
module compiled both in the private overlay and under its library module name.
The required delivery dry run and push are run after this consumer validation.
## Repair of returned head d88fff709c48

H7 is repaired exactly as requested. The item's proof_deps is restored to the
base list, ending in lem-weil-pbc-basic-open-function. The private imports of
LogConditionFineChartLocality and LogRegularCompletedChart are removed from the
item module. The accepted H2 ownership extraction, both theorem-module repairs,
the new definition node and def-trf-log-regular-pair statement dependencies are
retained. No mathematical statement, helper construction, or proof text changes.
The item's recorded signature remains identical to the accepted signature.

All four modules passed scompile.py per-file compilation with no errors or
unexpected warnings after this repair. The accepted signature and the exact
base proof fields were checked again before the delivery dry run.

## Delivery gate failure after H7 repair

The required deliver2.py --no-push run failed preflight before any push. Both
relocated-definition consumer modules are rejected under (c): "no node of the
delivery has it as lean.file". Both delivered JSON records do contain exactly
the matching lean.file. The gate also reports that these nodes are outside the
item's statement/proof prerequisite closure, now that the H7 correction removes
the two unauthorized proof dependencies. Thus the gate cannot package the H2
consumer repairs retained by the explicit H7 return. Restoring those dependencies
or private imports would contradict that return; dropping the consumer repairs
would undo H2. No tool is modified and no dependency is invented to bypass it.
All four modules compiled cleanly; nothing was pushed by the failed dry run.
## Retry after dispatcher continuation

Rechecked the retained H7 repair against the current read-only base: proof_deps
matches exactly and ends in lem-weil-pbc-basic-open-function; neither private
theorem-module import is present. The H2 definition extraction and both required
consumer repairs remain intact. Retried deliver2.py --no-push; after checking all
four Lean files it again failed preflight (c) on the same two consumer modules,
claiming no delivered node has their lean.file, despite both matching records.
The explicitly requested H7 repair is complete; the delivery gate still refuses
the required H2 edits outside the item's dependency closure. Nothing was pushed.

## Third delivery-gate attempt

Revalidated the H7 repair against the current base: proof_deps and proof text
match exactly, the two private imports are absent, and the mathematical statement
is unchanged. Both required consumer node records have matching existing lean.file
paths. Retried deliver2.py --no-push; it checked all four Lean files and again
refused both consumer modules under preflight (c), alongside the advisory that
their nodes are outside the item's dependency closure. This is the same gate
failure, not a compilation error or unfinished H7 repair. Nothing was pushed.

## Fourth delivery-gate attempt

Rechecked the retained repair against the current read-only node: the base proof
fields match exactly, both unwanted private imports remain absent, and accepted
H2 ownership changes remain present. Retried deliver2.py --no-push. The wrapper
checked four Lean files and again refused the two required consumer modules
under rule (c), despite matching lean.file records. It reported base 9bca5457f
and that sheaf-dag had moved on; the actual blocking reasons remain the same two
module-owner exclusions. The explicit H7 instructions forbid restoring the
spurious dependencies. No launcher script was modified and nothing was pushed.

## Fifth delivery-gate attempt

Verified once more against the refreshed read-only base that proof_deps is exactly
the base list ending lem-weil-pbc-basic-open-function, the proof and mathematical
statement are unchanged, and both private theorem imports remain absent. Both
consumer node records still specify their existing delivered lean.file paths.
Retried deliver2.py --no-push; after its four-file check and shared fetch it again
rejected only those two modules under preflight (c). It also explicitly classified
their nodes as outside the item's dependency closure. The requested H7 repair
and accepted H2 extraction are intact. The gate must permit these expressly
required relocation-consumer repairs without inventing theorem dependencies;
changing the launcher or undoing H7 is not authorized. Nothing was pushed.

## Latest continuation after fifth reported gate failure

Verified the retained H7 repair against the refreshed read-only base, including
exact base proof fields and removal of both private theorem imports. The accepted
H2 extraction, consumer repairs and mathematical signature are unchanged. The
prescribed deliver2.py --no-push again checked all four files and failed only on
preflight (c) for LogConditionFineChartLocality.lean and LogRegularCompletedChart.lean,
claiming no delivered node has their lean.file despite matching delivered node
records. Both nodes are explicitly reported outside the dependency closure.
Nothing was pushed; no tool was modified and no artificial dependency was added.
