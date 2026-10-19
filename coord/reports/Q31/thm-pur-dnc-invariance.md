## Worker report

The delivery states `WeilConjectures.PurityFiniteSetting.Dnc.existsUnique_dncInvariance`
in `Sheaf.Paper.PurityDncInvariance`. Its proof is `sorry`. The actual pro-etale section
objects are used, and the normal cone and DNC are the published extended-Rees
constructions. Neither an arbitrary normal bundle datum nor arbitrary fibre
identifications are hypotheses. The two fibre identifications are constructed from
the canonical exceptional base-change map, the adjunction mate of inverse compact-support
base change. The finite comparison uses the comparison adjunction unit and the actual
inverse-image comparison, not a choice of a nonempty isomorphism.

The current node already contains the stage-1 finite-type domain repair. This delivery
does not correct or weaken its statement. `aV = g ≫ aB` is the induced k-structure on V;
separatedness and finite type follow from those of g and aB. This formulation includes
every V with the k-structure required by the node, since g is a k-morphism.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed finite coefficients A=O_E/(varpi^n), n≥1, ell≠p, k=algebraic closure of the finite field | `P : PurityFiniteSetting.{u}` and `P.Coefficient`, the existing ULift of the actual quotient; positivity and characteristic conditions are fields of P. |
| B and V separated finite type over k | `aB`, `[IsSeparated aB]`, `[LocallyOfFiniteType aB]`, `[QuasiCompact aB]`; the induced structure `g ≫ aB` on V has the same properties by composition. |
| Smooth g of pure relative dimension d≥0 | `d : ℕ`, `[SmoothOfRelativeDimension d g]`; the existing theorem `SmoothOfRelativeDimension.smooth` supplies smoothness. |
| g separated finite type | `[IsSeparated g]`, `[QuasiCompact g]`; locally finite type follows from smoothness. Compactifiability is derived by `compactifiable`, not assumed. |
| Closed section | `s`, `[IsClosedImmersion s]`, `hs : s ≫ g = 𝟙 B`. This also makes s a k-morphism. |
| Actual DNC gtilde and stilde | `Scheme.Hom.deformationSpaceProj g s` and `s.deformationSpaceSection` on `s.ker.deformationSpace`; this is the relative spectrum of R[t,I/t], equivalently the specified blowup open. |
| Actual normal bundle and zero | `s.ker.normalCone`, `Scheme.Hom.normalConeProj g s`, `s.normalConeZeroSection`; the normal cone is R[t,I/t]/t, canonically gr_I R, and the augmentation kills positive degree. `PurityNormalCone` supplies the conormal/symmetric-algebra description for regular immersions. |
| Family F and two section objects | The actual finite family is `purityDncFamily`. At the finite stage the statement uses the canonical etale presentation `familyEtale` in its normalization equation, and its isomorphism is between `sourceSection` and `normalSection`, actual pro-etale `Ls* Rg!` objects. Both section objects unfold directly to the currently recorded `P.sectionInvariant`. |
| Unique isomorphism Cg≅CN | `∃! α : sourceSection ... ≅ normalSection ...`. |
| Identity in etale coordinates near the section | `fibreOne`, `fibreZero`, and the `sectionRestrictionIso` equation: read a family trivialization `e` at 1 and 0 and require the induced comparison to be their ratio. For the standard x=t*u family, these are the same standard section object, so this is exactly the identity. Coordinates are needed only near the section, not globally on V. |
| Etale localization in the stated domain | The equation is quantified over all separated finite-type B' and every k-morphism b, hence in particular the etale coordinate covers; open/etale source localization gives their family trivializations by the published geometry. |
| Every possibly nonflat k-base change | `∀ B' aB' [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB'] b (_hb : b ≫ aB = aB')`; no flatness, smoothness or etaleness of b is assumed. |
| Compatibility with independently reconstructed base-changed data | The displayed equation for every restricted family trivialization, together with the actual extended-Rees base-change theorem, is the fibrewise description of the corresponding normalized comparison after base change. The canonical mate fibre maps commute with this base change, including the identity. This formulation also avoids selecting coordinates or a trivialization as extra hypotheses of the theorem. |

The quantification over trivializations `e` is a normalization/naturality *predicate in
the conclusion*, not a hypothesis restricting the input pair. The geometry supplies such
trivializations etale-locally. Requiring the equation for every such reading is equivalent
to coordinate normalization: existence and uniqueness of the family comparison normalized
at 1 give all the readings, and a covering of standard readings determines the morphism.
The pro-etale equation is conjugated only by the explicitly constructed canonical
`sectionComparison` and `pullComparison` maps.

Dependencies read and reused:

- `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`: actual finite coefficients.
- `Sheaf.Paper.PuritySectionInvariant`, `WeilConjectures.PurityFiniteSetting.sectionInvariant`:
  the currently recorded actual finite Ls* Rg! object, used directly.
- `Sheaf.Paper.FiniteTypeExceptionalInverseImage`,
  `WeilConjectures.PurityFiniteSetting.dualizing`, `exceptionalBoundedBelow`, and
  `noetherian`: the currently recorded finite exceptional functor, with its
  Noetherian bounded-below interface and no ambient pro-etale adjoint assumption.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Hom` and `UpperLowerStar`:
  currently recorded actual finite coefficient operations.
- `WeilConjectures.AlgebraicGeometry.DeformationToNormalCone`,
  `Scheme.Hom.deformationSpaceProj`, `deformationSpaceSection`, `normalConeProj`,
  `normalConeZeroSection`, the two fibre pullback squares, and `normalConeData`.
- `WeilConjectures.AlgebraicGeometry.DeformationSpace.Coordinates`,
  `exists_etale_coordinates_deformationSpace` and `nonempty_deformationToNormalConeData`:
  the current server source constructs the actual Rees space and its coordinates.
- `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange`: the actual induced Rees
  map and the arbitrary-base-change pullback theorem for smooth sections.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`,
  `dualizingComplexBaseChangeMap`; `SmoothDuality`,
  `isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`.
- The published pro-etale derived comparison, unit comparison, exact derivation comparison,
  and pullback comparison. The small site keeps object universe u+1 and morphism universe u.
- Mathlib `SmoothOfRelativeDimension`, `IsClosedImmersion`, `Etale`, `IsSeparated`,
  `IsProper`, `LocallyOfFiniteType` and `QuasiCompact`. A morphism-properties convention
  node needs no artificial structure parameter.

Edge cases checked: d=0 (normal bundle rank zero and the section neighbourhood is etale);
empty B and empty V (the section/pullback identities and unique isomorphisms still make
sense); disconnected B (normalization is local and no connectedness is added); positive
coefficient level without a ramification-index divisibility assumption; identity b;
arbitrary nonflat b between finite-type schemes; coordinate charts containing the section
but not all of V; and the small site object universe u+1 and morphism universe u. No constant sheaf orientation
or freely chosen normal-cone datum is assumed.

Searches: LeanFinder on the full DNC-dualizing statement returned unrelated normalization
lemmas; Loogle `"normalCone"` returned no hits; Mathlib grep
`normalCone|normal_cone|sectionInvariant|dualizing` returned no hits. Project and shared Lean
rg searches found the older etale Nonempty theorem and arbitrary normal datum, which are
insufficient. `scompile.py --source` was then used for the current geometry, canonical-map,
and smooth-duality sources. The current ordinary-etale DNC theorem includes normalization
and naturality but accepts fibre isomorphisms as arguments and does not itself state this
finite pro-etale theorem. It is therefore reused as a proof interface, not recorded as an
exact existing statement. The comparison-node searches and their service-unavailable
LeanSearch result are recorded verbatim in `searches.jsonl` and its node. Blueprint and
DAG searches found no existing assembled finite section comparison.

## New nodes

`def-pur-finite-section-comparison` defines the explicit finite comparison from the
recorded `P.sectionInvariant` to its etale presentation. `comparisonUnit` applies Rnu_*
to the canonical coefficient-unit comparison and inverts the comparison adjunction
unit, which is invertible on bounded-below objects. `sectionComparison` then applies
the etale exceptional functor and the actual derived inverse-image comparisons.
Only `etaleUnitPlus` is postponed, with its matching proof plan. The source is the
finite etale/pro-etale transport in the DNC fibre argument. LeanSearch was unavailable
and that result is recorded verbatim; Loogle, Mathlib grep, project rg, the current
server source and `blueprint_refs.py search 'section comparison'` found no assembled
comparison. No primitive functor is redefined.

## Dependency modules

`def-pur-dnc-section-family` was unstated. `Sheaf.Paper.PurityDncFamily` defines the
actual extended-Rees DNC, projection, and augmentation as k-objects and uses the
currently recorded finite `P.sectionInvariant` for F. `purityDncDomain` and
`purityDncCompactifiable` state precisely the derived finite-type and compactification
facts needed to type it. Their docstrings contain the affine/Noetherian domain proof.
The fixed finite coefficient setting is the one explicitly required by the conventions.

`def-pur-normal-bundle`: the recorded relative-spectrum presentation supplies no
identification with the published extended-Rees quotient in the DNC geometry.
`Sheaf.Paper.PurityNormalCone` supplies the same associated-graded cone through that
actual quotient, its unique closed-immersion factorization to Z, the actual tensor
pullback conormal, and the symmetric-algebra bundle and augmentation identities.
`purityNormalProjection_eq` identifies its projection with the exact `normalConeProj`
used in the statement whenever i is a section. The affine chart theorem specifies
gr_I R including its structural map, so this is
an equivalent concrete presentation, rather than an arbitrary normal-cone datum.
The regular-immersion theorem retains the finite-type field domain and checks both
the projection and zero section of the bundle identification.

`lem-pur-dnc-section-geometry`: its recorded `nonempty_deformationToNormalConeData`
interface does not expose the canonical exceptional fibre maps. The current published
Rees geometry, its coordinate and arbitrary-base-change modules, and smooth duality
are reused in `Sheaf.Paper.PurityDncComparisons`. `sectionBaseChange` is explicitly
the pullback-composition comparison followed by the adjunction-mate dualizing map.
`fibreOne` and `fibreZero` apply it to the actual Rees pullback squares. The finite-type
domain and coefficient-exponent interfaces are named theorems, not new hypotheses.
The source/normal section definitions only install the derived compactification
instance before applying the recorded `P.sectionInvariant`; there is no second formula.

Current-source refresh (2026-10-16): the earlier attempt's integral/rational/common-stage
packet and duplicate finite section definitions were removed after reading the newly
recorded finite dependency modules with `scompile.py --source`. Existing node metadata
was refreshed from the shared DAG; the dependency changes are confined to `lean`.
The source blueprint item and its containing unit were read in the launcher literature
checkout, and their normalization and arbitrary-base-change clauses agree with the
statement here. No statement correction is made.

## Second reading by Q31

I read the delivered node, its five proof steps, the blueprint item and containing
`sk-thm-dnc/_section.md`, the dependency nodes and declarations, and all five delivered
modules. The node already has the reviewed stage-1 finite-coefficient/finite-type domain
repair. There is no stage-2 `statement_change`; neither its mathematical statement nor
the unit statement is changed in this reading.

The following is my object/hypothesis/conclusion inventory, in the order of the node.

| Node item | Lean rendering and verdict |
| --- | --- |
| Fixed finite stage A=O_E/(varpi^n), n≥1, ell≠p, k the fixed algebraic closure | `P : PurityFiniteSetting.{u}`. I opened `PurityFiniteSetting`, `Ring`, and `Coefficient`: the level has `level_pos`, the extension is the finite subextension of the coefficient datum, and `Coefficient` is the ULift of that actual quotient. No arbitrary finite ring or extra ramification divisibility is substituted. Pass. |
| B and V separated finite type over k | `aB` with `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. The structure on V is `g ≫ aB`; smoothness gives local finite type of g, and separatedness/quasi-compactness compose. Explicitly specifying a separate aV and equality to this composite would add redundant data. Pass. |
| g separated finite type, smooth of pure dimension d≥0 | `d : ℕ`, `SmoothOfRelativeDimension d g`, `IsSeparated g`, `QuasiCompact g`. I opened Mathlib's smooth and relative-dimension classes and its `smooth` implication. No missing smooth instance is made an assumption. Pass. |
| Closed section with g∘s=id | `s : B ⟶ V`, `IsClosedImmersion s`, `hs : s ≫ g = 𝟙 B`. Its k-linearity follows by composition. Pass. |
| Actual DNC, projection, and augmentation section | `s.ker.deformationSpace`, `Scheme.Hom.deformationSpaceProj g s`, `s.deformationSpaceSection`; `purityDncSource`, `purityDncMap`, and `purityDncSection` install precisely these maps over k. I read the published extended-Rees and fibre-square signatures. No arbitrary deformation datum is an input. Pass. |
| Actual normal cone/bundle and zero section | `s.ker.normalCone`, `Scheme.Hom.normalConeProj g s`, and `s.normalConeZeroSection`. The repaired `PurityNormalCone` imports the recorded `PurityNormalBundle`, and `purityNormalCone_comparison` identifies the Rees cone with its relative spectrum, preserving projection and augmentation. `purityNormalProjection_eq` identifies the projection used in the main theorem. Pass after repair below. |
| Exceptional operations only in the finite-type constructible domain | `sourceSection`, `normalSection`, and the family use the recorded `P.sectionInvariant`, which is actual pro-etale Ls* applied to `P.dualizing`. I opened that definition and `exceptional`, `dualizing`, `exceptionalBoundedBelow`, and `noetherian`. Compactifiability is supplied by named consequences, not assumed as new input; no ambient pro-etale right-adjoint datum occurs. Pass. |
| F and C(g,s), C(N,0) | `purityDncFamily` is the finite pro-etale F; `familyEtale` is its ordinary-etale presentation. `sourceSection` and `normalSection` install compactification proofs and then use the recorded section invariant directly. `sectionComparison` is the explicit comparison via the adjunction unit and derived inverse-image comparison. Pass. |
| Unique isomorphism C(g,s)≅C(N,0) | `∃! α : sourceSection ... ≅ normalSection ...`. The predicate follows the existential, so it asserts uniqueness of the normalized isomorphism. It does not assert all isomorphisms coincide. Pass. |
| Identity in standard coordinates near the section | The ratio of the `sectionRestrictionIso` at 1 and 0, using `fibreOne` and `fibreZero`, is conjugated by `sourceComparison`, `pullComparison`, and `normalComparison`. In the standard x=t*u family the two readings of e are the same standard object; the equation is the identity under those coordinate identifications. The coordinate neighborhoods need not identify all of V with affine space. Pass. |
| Etale localization | The conclusion quantifies all finite-type base charts b and all their family readings e, so in particular the affine etale charts supplied by the geometry lemma. Etale source localization around the section supplies these readings by the open/etale exceptional comparisons, as explained in proof step 3. There is no global-coordinate assumption. Pass. |
| Every k-morphism B'→B in the stated domain, including nonflat maps | The explicit `∀ B' aB' [IsSeparated aB'] [LocallyOfFiniteType aB'] [QuasiCompact aB'] b (_hb : b ≫ aB = aB')` has no flatness, smoothness, etaleness, or surjectivity binder on b. Pass. |
| Compatibility with the reconstructed primed comparison | The same equation holds for every reading of the restricted family. I read `exists_isPullback_deformationSpace_baseChange`: it identifies the actual reconstructed primed Rees family and section with this restriction for arbitrary b. The canonical mate fibre maps commute with this identification. Consequently both the pulled-back and reconstructed normalized comparisons have the same displayed local readings; uniqueness identifies them. This is the fibrewise formulation of the node's compatibility clause. Pass. |

The quantification over C₀ and e is in the conclusion, not an assumption on (g,s).
It is not vacuous: the geometry supplies the standard family readings on an etale
cover, with finite-type affine sources. It does not strengthen coordinate normalization:
after cancelling the common twist and shift, automorphisms of the rank-one sheaf on
A1 have identical readings at 0 and 1. I compared the precise equation with the current
published `Etale.exists_iso_sectionInvariant_normalCone` and
`Etale.leftDerivedUpperStar_mapIso_iso_sectionInvariant_normalCone`; those use the same
restriction-ratio formulation. They are not exact matches for this item: they use
ordinary-etale objects, deformation data and fibre-isomorphism arguments. The delivered
finite pro-etale theorem fixes those fibre maps canonically.

Edge cases: d=0 is admitted, without a positive-codimension predicate; the empty base
and empty source are admitted without Nonempty or surjectivity assumptions; a nonempty
base with empty V is correctly excluded by existence of s. Disconnected bases are
admitted. The coefficient level may be any positive integer, including a level not
divisible by the ramification index. Identity, empty, etale, and nonflat b are all in
scope. On affine normal-cone charts J=0 and J=R are included. Every variable and universe
is bound: schemes use u, coefficients/module values u+1, and the small pro-etale site
keeps object universe u+1 and morphism universe u. No universe equality or field-size
restriction was added.

Independent searches: LeanFinder query “Specialization of a smooth relative dualizing
complex along a closed section to its normal vector bundle” returned normalization,
smooth-function sheaf, and Kaehler retraction declarations, not this theorem. Loogle
`"sectionInvariant"` returned no hits. The Mathlib grep query
`specializ|normal.?cone|dualiz` returned specialization/topology results, not DNC
invariance. LeanSearch for “Comparison of the section pullback of a relative dualizing
complex between the etale and pro-etale sites” returned general module-sheaf pullback
and adjunction comparisons, not the assembled section comparison. I inspected the
returned names/types. Project/source rg searches for `sectionInvariant`,
`sectionComparison`, `purityNormalCone`, and comparison/section combinations found the
ordinary-etale theorem and unrelated section/cohomology comparisons. Blueprint search
`section comparison` found no node. The primitive functors and comparisons are reused.

New-node reading (H12): `def-pur-finite-section-comparison` is an assembled canonical
comparison absent from the searched DAG/project, rather than a replacement functor.
Its source is the finite comparison needed in the node's fibre argument. Its statement
and `sectionComparison` agree: `comparisonUnit` maps the coefficient-unit comparison by
Rnu_* and inverts the bounded-below comparison adjunction unit; then the actual
exceptional and inverse-image functors are applied. `etaleUnitPlus` postpones only the
asserted bounded-below property. The new node has the required definition kind, ancestry,
chapter/unit, searches, empty proof fields, creation and Lean records, and is cited by
the item. Definitions have explicit data throughout.

Dependency readings (H13): `def-pur-dnc-section-family` uses the actual Rees construction
and actual finite `sectionInvariant`; its domain and compactification facts are named
statements. `lem-pur-dnc-section-geometry` imports the published coordinate, punctured,
standard-pair and arbitrary-base-change geometry and supplies the missing canonical
fibre maps as the compact-support-adjunction mates (`sectionBaseChange`, `fibreOne`,
`fibreZero`). The exponent and compactification interfaces are consequences, with no
new hypotheses on the main theorem. Their proof docstrings spell out these consequences.

Mismatch repaired (H4/H13): the first normal-cone dependency independently introduced
`purityConormal` and restated the regular vector-bundle assertion, although the recorded
`PurityNormalBundle` and `ConormalGradedAlgebra` already supply them. Its affine-chart
assertion alone also left the relation to the recorded cone implicit. I removed that
second conormal definition and the redundant zero/bundle statements, imported
`Sheaf.Paper.PurityNormalBundle`, and added `purityNormalCone_comparison`, an existence
statement identifying the actual Rees cone with that recorded cone and preserving both
projection and zero section. Its proof plan specifies the homogeneous representatives
and localization gluing. No definition chooses an isomorphism from that existence
statement. The original regular bundle and conormal data remain the single definitions.
The dependency `lean.note` and declaration list now describe this bridge. This supersedes
the earlier worker-report paragraph describing a separately supplied bundle description.

I also copied all five main signatures literally, including their line breaks, into
the respective `lean.statement` fields. The main theorem signature was preserved.
All postponed proofs remain whole `sorry` proofs of public named theorems; each is part
of its owning node's stated construction/property and has source, blueprint tag and
natural-language proof. No proof was filled and no target or unit was altered.

Validation: all five final modules compiled individually through the prescribed
`scompile.py` pipeline used by `deliver2.py`, with no errors or warnings. The required
`deliver2.py Q31 thm-pur-dnc-invariance --no-push` printed OK and passed server preflight.
The independent normal-cone Loogle query `"normalCone", "Iso"` also returned no hits.
