## Worker report

The delivery states `AlgebraicGeometry.Elkik.intrinsic_formal_resolution` in
`Sheaf.AlgebraicGeometry.IntrinsicFormalResolution`. Its only theorem proof is `sorry`.
The two definition modules supply real constructions and predicates, with no postponed data.
The original item's statement and proof are unchanged; two definition-node dependencies
are added. No dependency module or statement correction is needed.

Clause-by-clause correspondence:

- An affine finite-type scheme over a characteristic-zero field is `AffinePair.ring`,
  `.field`, `.isField`, `.charZero`, `.structureMap`, `.finiteType`, `.quasiCompact`.
  `generator` and `nonZeroDivisor` give precisely a principal non-zero-divisor ideal.
  `singularSupport` uses absolute stalk regularity, not relative smoothness.
- `Pair.presentation` gives the finite disjoint union of those affine pairs and identifies
  the actual extended ideal on each piece. It is an existence proposition: no selected
  field, generator, or decomposition becomes an argument on which the rule can depend.
  Single affine pairs occur with one summand. The empty union occurs with zero summands.
- `Pair.fibre t` is the actual closed subscheme `V(I^t)` from the published
  `adicThickeningDiagram`; `Pair.fibreIdeal` is extension along its closed immersion.
  In affine coordinates this is precisely Spec(A/I^t) with I(A/I^t).
- `IsVarietyUnion` expresses the domain of F as finite disjoint unions of finite-type
  schemes over possibly different characteristic-zero fields, generically reduced.
  For these Noetherian schemes generic reducedness is equivalent to having a dense
  reduced open. Separation and a dimension bound are not assumed. F is indexed by all
  schemes so it does not carry a selected field/decomposition; values outside this
  predicate have no conditions and are irrelevant. Any rule on the predicate extends
  by the zero-length identity tower elsewhere, so this adds no hypothesis.
- `IsStrongRegularRule` is exactly the explicitly assumed strong regular functoriality:
  coherent nonempty regular centers, every center over the original nonregular locus,
  regular last scheme, and `OrdinaryResolutionComparison` for every regular map between
  variety unions. This uses the published contracted pullback interface, preserving
  extended ideals and deleting precisely unit ideals. There is no equation over a field,
  no finite-type condition on those morphisms, and no hidden functoriality conclusion.
- `staggeredLevel A n i` has order n(n-i); `staggeredCenter` is its restricted center.
  `staggeredTransition` includes the thinner fibre then restricts the ordinary arrow.
  It does not impose the erroneous off-center isomorphism on unequal-thickness arrows.
  All levels restricted further to a common t are `levelDiagram A i |>.obj t`; ideal
  powers and quotient inclusions identify iterated restriction with this expression.
- The theorem's first conjunct quantifies `∀ X, ∃ r, ∀ F, ... ∀ Y, ∃ N`.
  Thus r depends only on the target pair, not on F, Y, n or h. N is chosen after F and Y;
  `max ... < N` and `N ≤ n` give n greater than both tower lengths. Every regular thick
  scheme map h at order n²+r is quantified. Exact preservation of its distinguished
  ideal is the explicit equation following `IsRegularSchemeMorphism h`. It need not
  lift to a map of ordinary pairs and has no field-linearity hypothesis.
- `FiniteComparison ... (n*(n-max pX pY)) h` contains h_t for every
  `t ∈ Set.Icc 1 T` and `base_fac`, specifying the restriction over h via the monic
  canonical inclusions. T≤n²+r holds arithmetically in this application; `base_fac`
  takes the corresponding t≤m proof to avoid adding a tautological arithmetic conjunct
  to the target theorem. No arbitrary substituted base map is used.
- `Comparison.cartesian` states the isomorphism to pullback at each retained/repeated
  level. `count`, `retainedStage`, `count_before`, `count_after`, `deleted_level`,
  `count_zero`, `count_last` preserve every order and contract the empty stages.
  `retained_ideal` is equality of ideals (hence of closed center subschemes), and
  `deleted_iff_unit` deletes exactly empty centers. `naturality` compares all arrows.
  `precision` states restriction compatibility at every smaller positive t. No finite
  comparison is asserted unique or a subsingleton.
- `CompletedMap` is a compatible natural transformation of all actual thickenings,
  with exact distinguished-ideal equality at every order. Such a map is equivalent to
  a continuous ideal-preserving map of the complete Noetherian formal rings: applying
  the ringed-space colimit yields `CompletedMap.formalMap` with inverse-limit sheaf.
  `CompletedMap.IsRegular` reuses the published regularity predicate on complete formal
  affine section rings, which uses `RingHom.IsRegular`. The second theorem conjunct
  asserts a `CompletedComparison` for every such regular completed-pair map.
- `CompletedComparison` is `Comparison` at all t≥1, with one common contraction count
  and maps compatible at every order. It thus compares the actual completed levels,
  ordinary arrows completed along the extended distinguished ideal, and full completed
  center ideals, rather than blowups of finite quotient rings. The compatible cartesian
  squares give the pullback in adic formal schemes; chartwise inverse limits recover the
  formal ringed spaces and center sheaves.
- `CompletedIso` fixes an identification of completions with their distinguished ideals.
  The third theorem conjunct gives `Nonempty` and `Subsingleton` of the centered completed
  tower comparisons over this fixed identification. Consequently the count, order and
  maps are uniquely determined, independently of algebraization and fields. This
  uniqueness applies to the completed centered comparison, never arbitrary finite
  nilpotent-tower automorphisms.
- All three conjuncts quantify over `Pair`, so finite disjoint unions and their mixed
  fields are included throughout. F is applied to `X.scheme` on the whole union, with
  one length, one retained-stage embedding and one count; no componentwise application
  discards stage synchronization.

Dependency declarations inspected and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`: `AlgebraicGeometry.IsRegularSchemeMorphism`
  (flatness and all finite residue-field extensions).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `WeilConjectures.Blowup.Gluing`: `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and
  `.blowupMap`, used through the exact published `OrdinaryBlowupTower`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the recorded coherent interface;
  `WeilConjectures.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies `.toModules`.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and
  `Algebra.IsGeometricallyRegular`, used by the recorded formal-affine regularity predicate.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, with the completed affine ring and quotient-limit constructions.
- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `OrdinaryBlowupTower`, `.toBase`,
  `OrdinaryResolutionComparison`. No private replacement of the ordinary tower is made.
- `Sheaf.AlgebraicGeometry.AdicFormalGeometry`: `adicThickeningDiagram`,
  `adicThickeningMap`, `adicFormalCompletion`, `IsRegularOnAdicFormalAffines`.
- `Sheaf.AlgebraicGeometry.RigRegularFormalGeometry`: `affineFormalIdeal`.

Proof imports: `WeilConjectures.RingTheory.RegularBaseChange` supplies
`RingHom.regular_base_change`; `Mathlib.RingTheory.AdicCompletion.Completeness` supplies
`AdicCompletion.pow_smul_top_eq_ker_eval` (the recorded Mathlib match of the quotient node).
The three Elkik proof prerequisites (smooth-span lifting, rational smooth models and
supported blowup precision loss) have no Lean record or Mathlib match on the read base;
no module import exists to add. They are proof-only prerequisites, not notions needed to
state this item; their full proof uses are recorded in the theorem docstring.

Edge cases checked: n=0 is excluded only by the specified sufficiently-large condition;
r=0 is permitted. The comparison's S=Icc 1 T is nonempty for the actual n>P inputs.
P=0 gives T=n² and length-zero towers, with no precision loss. Empty union, unit principal
ideal, empty closed fibre, nonproper/nonseparated variety inputs and different fields are
not excluded. All rings, fields and schemes share a single arbitrary size universe u;
this allows every finite union and both fields at a common upper size without a bounded
universe of test fields. The dependency's regularity test retains its full universe.
The non-zero-divisor condition is not weakened to a mere nonzero generator. Centers
with isomorphic blowup arrows remain retained unless their ideal is actually unit.

Searches (actual msearch.py calls and project/DAG searches):

1. LeanFinder: "Regular maps of sufficiently thick Elkik pairs determine the ordered
   desingularization tower compatibly with formal completion and regular morphisms".
   Eight unrelated smoothness, normalization and spreading-out hits; no theorem match.
2. Loogle: "AdicCompletion, AlgebraicGeometry.Scheme.IdealSheafData.blowup".
   Zero hits; the project-specific blowup identifier is unknown to Mathlib Loogle.
3. Mathlib grep: "FormalScheme|formalCompletion|Elkik|Desingularization" in AlgebraicGeometry.
   Zero hits. A second grep "Elkik|staggered|CenteredDiagram|TowerComparison|desingularization"
   also has zero Mathlib AlgebraicGeometry hits.
4. LeanSearch: "Compatible pullback comparisons at every precision of ordered centered
   blowup towers with exactly empty centers deleted". Eight generic categorical
   pullback-comparison or sheaf matching-family hits, no ordered tower notion.
5. LeanFinder: "Elkik pair is an affine finite type scheme over a characteristic zero
   field with a principal non zero divisor ideal containing the nonregular locus".
   Eight smooth-algebra/locus hits, no Elkik-pair definition.
6. Further LeanSearch and LeanFinder searches combining the two new notions are recorded
   verbatim in each new node's mathlib_searches, from the wrapper's actual results.
   They returned principal-ideal, formal-smoothness and standard-etale declarations,
   none the requested definitions. Their query logs are in the sandbox searches.jsonl.
7. rg over `lean/WeilConjectures`, including the literal item id: no item declaration;
   desingularization hits concern Popescu ring approximation, not geometric towers.
   rg over `lean/Sheaf` found the reusable ordinary, formal and supported tower modules;
   these were read. `dag/lean_names_upstream.json` has no Elkik or target name hit.
8. rg over dag/nodes for Elkik/principal singularity pairs finds the item and its
   theorem prerequisites, not a notion node. `tools/blueprint_refs.py search Elkik`
   reports zero blueprint nodes. Supported-centered tower and formal-system nodes were
   inspected: these encode actual formal blowups; they are not the centered diagrams
   of finite nilpotent fibres, whose arrows need not themselves be blowups.

Source read: Temkin arXiv:0904.1592v2 at the node's URL, especially printed pp.23--25,
Proposition 3.3.5, the ratio calculation in Lemma 3.3.3, and §3.4.1. The current blueprint
ancestor and unit were opened in literature/blueprint/latest. This is a lemma below a
unit; no blueprint/unit statement is changed. No STATEMENT-DISPUTED or new node fault.

Validation: all three modules compiled individually through scompile.py in dependency
order against the live published library, with no errors or non-sorry warnings. The first
dry run requested the current schema field `import_flags` on each new definition node;
both records now carry the required empty list.

## New nodes

`def-per-elkik-pair-geometry` owns `ElkikPairGeometry.lean`: the finite unions of affine
principal singularity pairs, actual thick fibres, and the explicit strong all-regular
functoriality hypothesis. Source: Temkin §§2.3.1--2.3.6, 3.2.3--3.2.4, 3.3.1, 3.3.8.
The three types of search above found no duplicate composite notion. It reuses the
published ordinary tower, coherent, regular and formal-affine predicates.

`def-per-elkik-tower-comparison` owns `ElkikTowerComparison.lean`: the actual common-order
and staggered centered diagrams, contracted cartesian comparisons with ideal equalities,
restriction coherence and completed maps/comparisons in infinitesimal-system coordinates.
Source: Temkin §§3.3.4--3.3.8 and 3.4.1, with the stage-1 common-precision repair retained.
The Mathlib and project/DAG searches found no duplicate. OrdinaryResolutionComparison
cannot be applied directly to truncated diagrams: its levels must be actual blowups,
whereas these are restrictions of blowups. Formal resolution rules add regularity/open
center/blowup data and do not construct these truncated diagrams. Only this missing
comparison interface is introduced; no second ordinary blowup or formal completion.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
