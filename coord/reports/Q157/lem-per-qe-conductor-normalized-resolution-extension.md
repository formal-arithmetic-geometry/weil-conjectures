## Worker report

Stage 2 statement delivery for `lem-per-qe-conductor-normalized-resolution-extension`.
The live node is split and stage-1-reviewed for Q19, but has no Lean record or
reviewed_lean record. The current stage-2 brief §0 expressly permits this handoff.
The inherited previous ending was a stage-1 unchanged-split refusal, not a refusal
of a prepared stage-2 packet. The accepted statement and split are preserved.
No repair note for this item was present.

The item module is `Sheaf.AlgebraicGeometry.QEConductorNormalizedResolutionExtension`.
Its declarations jointly state the geometry, canonical regular base change, and
conductor-first extension clauses of the node. The only postponed proofs are the
three named theorems `qeConductor_geometry`, `qeConductor_regularBaseChange`, and
`qeConductor_normalizedResolution_extension`; all are clauses of this DAG node and
have source and full natural-language proof docstrings. Every definition has real
data. The preparation scheme is literally the existing normalized blowup of the
existing conductor ideal, with the composite rational structure map. Its proof
fields come from `qeConductor_geometry`, which determines this fixed construction's
properties; there is no choice of unspecified scheme from a mere existence proof.

The main theorem presents the extended assignment by existence together with an
exact construction specification, `IsConductorResolutionExtension`, at every input.
It specifies the entire given tail, every arrow and center, the length, and the
initial conductor stage or its omission. It does not replace the prescribed
construction by an arbitrary resolution or an arbitrary comparison map. The only
model freedom is the ordinary isomorphism freedom of scheme presentations.

The item node changes only in `lean` and the addition of the new definition node to
`stmt_deps`. There is no statement correction or STATEMENT-DISPUTED flag. The node's
own blueprint.is is null: this is a supporting input, not a unit statement.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Reduced Noetherian quasi-excellent rational inputs, without a finite-type hypothesis | `QEResolutionInput.scheme`, `.structureMap`, `.reduced`, `.noetherian`, `.quasiExcellent`; the latter quantifies over all affine opens using the recorded `IsQuasiExcellent`. |
| Noetherian means a finite affine Noetherian cover is available | Mathlib `IsNoetherian` extends `IsLocallyNoetherian` and `CompactSpace`; finite affine subcovers follow. No topologically-Noetherian-only replacement is used. |
| N is assigned on every normal input, including finite disjoint unions | The theorem parameter `N : RegularNormalizedResolutionRule NormalQEResolutionInput (fun X ↦ X.val.scheme)`; the normal subtype requires `IsDomain` and `IsIntegrallyClosed` of every stalk. It does not require an irreducible or nonempty scheme. |
| N gives finite normalized blowup towers starting at S | `N.tower X` has a natural-number length and the existing `Monoscheme.NormalizedTower`; `.initial` identifies level zero with S. `NormalizedTower.blowup` uses the existing normalized blowup, with its center. |
| Coherent centers with nonempty nowhere dense zero schemes and regular last scheme | `QENormalizedResolutionTower.coherent`, `.nonempty`, `.nowhereDense`, `.regular`, using `RingedSpace.IsCoherent`, set nonemptiness of the ideal support, the existing `HasNowhereDenseCenters`, and `IsDesingularization` / `IsRegularScheme`. |
| Every regular map, flat with geometrically regular fibers | `RegularNormalizedResolutionRule.comparison` takes `IsRegularSchemeMorphism h`, whose existing definition is flatness plus regularity after every finite extension of every residue field. No smoothness, finite type, quasi-compactness, separation or constant relative dimension of h is added. |
| Recursive pullback and precisely ordered unit-ideal deletion | `QENormalizedResolutionComparison.pulled`, `.initial`, `.lift`, `.cartesian`, `.centers`, `.arrows`, and `.contraction`; every pulled level is cartesian over the input, and every center equals the actual extended ideal. The existing contraction retains the ordered centers. `.unit_isIso` together with the existing `.deleted` iff makes deletion exactly equivalent to a unit center, not merely an isomorphism. |
| N comparisons respect identity and composition, and delete no stage for surjective h | Rule fields `.identityIndex`, `.identityMap`, `.compositionIndex`, `.compositionMap`, `.surjective_no_deletion`. `HEq` here only expresses equality of level maps whose sources are identified by the preceding index equality; it does not omit equality of maps. An injective surjective order contraction deletes no level. |
| N(empty) is trivial | Rule field `.empty` says length zero for every empty input. |
| Componentwise normalization nu | Existing `Scheme.reducedNormalization` and `Scheme.fromReducedNormalization`, imported through the recorded normalization and normalized-blowup dependencies. |
| D is Ann(coker(O_X → nu_* O_normalization)), annihilating all local sections | Existing `conductorCokernel` is the cokernel of `unitToPushforwardObjUnit`; existing `conductorIdeal` is the affine-section annihilator construction. Under the finite-normalization coherent-cokernel hypothesis supplied here, this is the quasi-coherent annihilator ideal, not an arbitrary subsheaf or selected section annihilator. |
| nu is finite; D coherent; its vanishing set exactly the nonnormal locus, nowhere dense; D unit iff X normal | `qeConductor_geometry X` yields `QEConductorGeometry.finite`, `.coherent`, `.support`, `.nowhereDense`, `.unit_iff`. The support condition uses negation of the normal-domain stalk conjunction. |
| P(X) = normalized blowup along D; normal, reduced, Noetherian, quasi-excellent, finite type over X | `conductorPreparedInput X` has scheme `(conductorIdeal X.scheme).normalizedBlowup` and structure map `(conductorIdeal X.scheme).normalizedBlowupMap ≫ X.structureMap`. Geometry fields `.normal`, `.reduced`, `.noetherian`, `.quasiExcellent`, `.finiteType`, `.quasiCompact` provide exactly these properties. Finite type is the recorded locally-of-finite-type plus quasi-compact conjunction. |
| H_N(X) prepends the conductor stage to N(P(X)), omitting it exactly when D is unit | `IsConductorResolutionExtension` identifies the tail by ordered level/stage embeddings and `tailIso`, `tailArrow`, `tailCenter`. Their values are i plus `conductorStageCount X`, and the length is the tail length plus that number. This number is the explicit classical if-D-unit-then-0-else-1 construction. `.unitBase` identifies the entire unshifted tail over X through P(X) → X; `.conductorStage` identifies both the actual first ideal and its morphism when nonunit. No extra or missing stage is possible. |
| H has coherent nonempty nowhere dense centers, regular endpoint, and is trivial on empty X | H is itself a `RegularNormalizedResolutionRule` with `QENormalizedResolutionTower` values; the same center, regularity and empty fields apply. |
| D_Y = D_X O_Y under regular h | First conjunct of `qeConductor_regularBaseChange`: `conductorIdeal Y.scheme = (conductorIdeal X.scheme).comap h`. `comap` on ideal-sheaf data is ideal extension. |
| Canonical P(Y) ≅ P(X) ×_X Y; P(Y) → P(X) regular and surjective if h is | The second conjunct supplies a unique k with `IsPullback k pY pX h`, `IsRegularSchemeMorphism k`, and `Surjective h → Surjective k`. `IsPullback` gives precisely the canonical isomorphism to the chosen fiber product and both projection equations. The uniqueness pins the canonical top map. |
| Resulting H comparisons preserve ordered ideals and identity/composition | H's rule fields give actual cartesian pullback/contraction comparisons and both index and map laws. The exact tail specification identifies H with the stated conductor assembly; uniqueness of normalized-blowup comparisons makes these the resulting comparisons. Preparation squares compose by their uniqueness, while ideal extensions compose by the existing `IdealSheafData.comap_comp`. |
| Every deletion is exactly unit, every deleted stage is an isomorphism, no deletion for surjective h | H's comparison has `.unit_isIso` and the existing `NormalizedContraction.deleted`, `.deletedMap`, `.keptMap`, `.keptCenter`; the rule has `.surjective_no_deletion`. A proper principal/invertible center remains a kept stage, even if its blowup map happens to be an isomorphism. |
| Finite disjoint unions are inputs | The input quantifiers range over every reduced Noetherian quasi-excellent rational scheme; no connectedness, equidimensionality or fixed component count is imposed. No independent resolution-per-component or synchronization choice is substituted. |

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (Noetherian + G-ring + J-2).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, the locally
  Noetherian plus regular-stalk predicate, rather than just the upstream stalk class.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, with
  `IsDomain` on stalks as the normal-domain form of def-weil-pbc-normal-ring.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, and its reduced integral component construction.
- `Sheaf.TraceFormula.ConductorSmoothBaseChange`: `conductorCokernel`, `conductorIdeal`.
  Its finite-type smooth theorem is NOT used as a substitute for this item's statement.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `.blowupMap`.
- `Sheaf.AlgebraicGeometry.NormalizedBlowup`: `.normalizedBlowup`, `.normalizedBlowupMap`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` and public
  `WeilConjectures.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `.toModules`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and its
  projections; `IsPullback` is the categorical pullback-square predicate used here.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: `IsNormalizedBlowup`,
  `NormalizedTower`, `NormalizedContraction`. Its `NormalizedPullback` requires smooth
  maps at every level and is therefore not used for an arbitrary regular map.
- `Sheaf.AlgebraicGeometry.NormalizedTowerDescentData`: `NormalizedTower.toFirst`,
  `.HasNowhereDenseCenters`; this module imports the published tower definitions.
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`: `IsRegularSchemeMorphism`.

All presently recorded proof-dependency modules are imported, privately when needed
only by the proof plan. The flat affine criterion, tensor exactness and surjective
base-change Mathlib matches are imported through their recorded modules as well.
The three proof nodes without a recorded declaration (regular tower pullback,
finite-type quasi-excellence stability, and reduced Noetherian blowup geometry) are
not invented or replaced: their arguments are documented in the theorem docstrings
and they remain proof dependencies of this statement-only delivery. No missing
statement object depends on a theorem that has not been supplied.

Source check: read the live item and all thirteen original statement dependencies,
their records, signatures and docstrings, the added tower/regular-morphism interfaces,
and ILO VIII 2.2.1--2.2.9, 2.3.2--2.3.5 and 2.3.9--2.3.12 in the locally held PDF
(printed pp.90--94). In particular 2.2.9 treats regular, not just smooth, base change,
and 2.3.12 explicitly discards any requirement that normalized centers be regular.
The conductor-prepending construction is the node's explicit refinement; the report
does not claim ILO states its conductor formula verbatim.

Edge cases checked before writing and again against the compiled signatures:

- Empty input: normality is vacuous; the unique ideal is unit; the length shift is
  zero; N(empty) has length zero; the exact specification gives H(empty) length zero.
- Length-zero tail on a nonnormal input: its one conductor stage is still present;
  the endpoint is the prescribed regular P(X). Both index types and embeddings allow
  this case. No inhabitedness of an empty stage index is assumed.
- Unit conductor: no first stage is introduced, but the whole tail is identified
  over X through the preparation isomorphism, not by replacing N(P(X)) with N(X).
- A conductor that becomes unit after a nonsurjective regular pullback: the index
  contraction can collapse that first stage, and its unit-isomorphism proof is required.
- Proper invertible centers: their support is nonempty; isomorphism of the blowup
  does not authorize deletion. The conjunction in the existing contraction's deletion
  criterion plus the explicit unit-isomorphism field enforces this distinction.
- Surjective maps, including empty-to-empty: the contraction's injective index
  forbids stage deletion without adding a nonempty-source assumption.
- Disconnected normal schemes: stalkwise normal-domain normality allows them; the
  definition is not `IsIntegral` or a single function-field normalization.
- Arbitrary regular maps, including non-finite-type localizations and completions:
  no smoothness or finite-type binder has been introduced. In the proof, regular
  base change 07C1 is applied along the finite-type preparation, never along h.
- Universes: all schemes and finite residue extensions are in the same explicit u;
  input records live in Type (u+1). The family index universe v is explicit in the
  generic rule. No independent smaller test universe or forced universe equality
  narrows the geometric objects. Auto-implicit binding is disabled in both modules.

Searches (real wrapper records are retained in searches.jsonl and copied verbatim
as JSON into the new node's mathlib_searches):

- LeanFinder: “Extend a regular functorial normalized resolution from normal
  quasi-excellent schemes by blowing up the conductor of normalization first”:
  eight ordinary normalization hits; no extension theorem.
- Loogle: `AlgebraicGeometry.Scheme.IdealSheafData.normalizedBlowup,
  AlgebraicGeometry.conductorIdeal`: no hits; the project-specific name is unknown
  to Mathlib's index.
- Mathlib grep: `conductor|NormalizedTower|normalizedBlowup`, AlgebraicGeometry:
  zero hits.
- LeanSearch: “regular functorial normalized blowup resolution rule on reduced
  Noetherian quasi excellent rational schemes with ordered unit center contraction”:
  eight ordinary normalization hits, no resolution assignment or contraction rule.
- LeanFinder: “finite normalized blowup tower contracted regular pullback identity
  composition unit ideal centers”: eight ordinary normalization hits, no rule.
- Mathlib grep: `NormalizedResolutionRule|QEResolutionInput|RegularFunctorialNormalized|conductor`,
  AlgebraicGeometry: zero hits.
- Project/upstream rg with the expected names and with conductor/resolution/tower
  concepts found the existing toric smooth finite-type rule and the reusable tower,
  contraction, conductor and regular-morphism definitions, not this item. The exact
  item id has no declaration in either source tree. `blueprint_refs.py search
  'normalized resolution rule'` returned zero blueprint nodes. DAG concept search
  found the smooth finite-type conductor extension and the current quasi-excellent
  extension as distinct statement nodes, neither having a Lean record.

Validation: scompile.py compiled both delivered modules separately in dependency
order against the published live library. The final run was clean, with no errors
or warnings (new definition module 2.5 s; final module 6.1 s after its first sandbox
elaboration at 29.2 s). The first compile exposed a missing public toModules import;
the next exposed a missing Decidable instance for the conductor branch. These were
repaired by importing the owning public module and defining the explicit classical
zero/one stage count, without a file-local instance or notation.

## New nodes

`def-per-qe-normalized-resolution-rule` supplies the absent notion used by the
item's hypothesis. Its module is `Sheaf.AlgebraicGeometry.QENormalizedResolutionRule`.
It defines the exact quasi-excellent rational input class and its normal subtype,
then a based resolution tower, a cartesian regular-pullback/ordered-unit-contraction
comparison, and a simultaneous regular-functorial rule with the stated identity,
composition, surjectivity and empty-input laws. It imports and reuses the existing
normalized towers, contractions, recursive composite, regular scheme morphism,
coherence, normality and quasi-excellence notions. Sources are ILO VIII
2.2.3--2.2.9, 2.3.2--2.3.5 and 2.3.9--2.3.12. The searches above found no duplicate.
The smooth toric rule is finite type and smooth-functorial; RationalResolutionInput
is finite type; SmallSingularLocusPair requires an auxiliary Cartier divisor and
its presentation. None states this notion. No dependency module or statement
correction is needed.

Preflight repair: the current server requires `import_flags` on a new node; the
initial dry run identified that missing key. Added the empty list, without changing
mathematical content. The non-enforced route-pivot advisory names the two normalization
proof imports already present in the accepted node’s proof dependencies and expressly
approved as generic inputs in its current stage-1 review; they remain proof-only imports.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
