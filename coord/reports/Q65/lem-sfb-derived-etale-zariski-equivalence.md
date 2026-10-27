## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence` states
`AlgebraicGeometry.Scheme.Modules.derived_etale_zariski_equivalence`. Its proof is
`sorry`. The conclusion is existence of simultaneous, canonically normalized
witnesses (`Nonempty DerivedEtaleZariskiSystem`). The structures merely package
this node's witnesses; no independent mathematical notion or arbitrary map is
introduced. Definitions have real data: the two structure maps are Mathlib's
adjoint structure maps, and the two ordinary pullback helpers apply the recorded
functor termwise.

Hypothesis and clause correspondence:

- Any scheme: `data : ∀ T : Scheme.{u}, ...`; any morphism: `square : ∀ h : U ⟶ T, ...`.
  No separatedness, Noetherian, affine, finite-dimensional or boundedness hypothesis
  occurs on schemes or pullback morphisms.
- Canonical ringed-site epsilon, restriction and tensor extension: `context` is the
  recorded `ZariskiEtaleModuleContext`. Its `extension`, `restriction`, `adjunction`
  and underlying structure sheaf are used unchanged. The context contains only
  continuity and right-adjoint-existence proofs, not arbitrarily chosen functors.
- Size convention: independent explicit universes `u w`; the small étale site
  retains object size `u+1`, Hom size `u`, and actual `u`-sized section modules.
  The two families of `HasDerivedCategory.{w}` choose localizations only. Each
  Zariski localization is explicitly on `SheafOfModules (moduleRings ...)` to
  avoid accidentally choosing the separate default localization of `T.Modules`.
- Unbounded derived categories: `DerivedCategory`, `DerivedCategory.Qh`, and
  homotopy categories of `.up ℤ` throughout. No degree bound or termwise
  quasi-coherence condition is imposed.
- Quasi-coherence: `schemeDerivedQCohProperty` on the Zariski side; on the étale
  side the clause `∀ n : ℤ, (homologyFunctor ... n).obj K |>.IsQuasicoherent`
  is Mathlib's existing site-local presentation predicate. These are precisely
  the objects of the full subcategories in the node, with ambient morphisms.
  The preliminary explanation of perfect objects is terminology, not an
  extra hypothesis or conclusion of this node.
- Exactness and faithfulness on all modules: `exact_limits`, `exact_colimits`,
  and `faithful` of `DerivedEtaleZariskiEquivalenceData`. Finite limits and
  finite colimits express exactness for these additive abelian module categories.
- Derived extension: `extension_factors` identifies epsilon extension with the
  termwise exact functor after localization, on all unbounded complexes.
- Quasi-inverse R epsilon_*: `restriction_derived` is its right-derived universal
  property; `restriction_injective` records the K-injective computation.
- Equivalence with the canonical comparisons: `extension_qcoh` and
  `restriction_qcoh` restrict the functors to the full cohomological QCoh
  subcategories. `adjunction_normalized` identifies the derived Hom bijection
  with the ordinary adjunction and the derived unit on representatives.
  `unit_iso` and `counit_iso` make precisely this adjunction an adjoint
  equivalence there. This is the adjoint formulation of the equivalence, not
  an unconstrained existence of some equivalent category.
- Every h pullback comparison: `comparison` is a natural isomorphism
  `derivedPullback h ⋙ dU.extension ≅ dT.extension ⋙ pullback`.
  `pullback_derived` fixes Lh_et^*, and `zariski_derived` uses the existing
  Zariski `derivedPullback`. `zariski_normalized` pins its otherwise variable
  derived counit to `canonicalSchemeDerivedAdjunction`.
- Canonical ringed square and tensor normalization: `ordinary_right_sections`
  identifies the ordinary right square on every open with restriction along
  `gabberPreimageEtaleIso`. `comparison_representatives` equates the derived
  square followed by its counits to localization of the recorded ordinary
  `zariskiEtalePullbackComparison`. That comparison is the adjoint mate of
  this specified ring-compatible right square, hence is iterated scalar
  extension identified with scalar extension along the composite. The equation
  holds on all homotopy representatives, including the flat-term K-flat ones.
- QCoh pullback preservation: `pullback_qcoh`; Zariski preservation is the
  recorded `derivedPullback_cohomology_over_affine` used by the proof.
- For qcqs h: `pushforward_qcoh` and `pushforward_comparison_iso` take exactly
  `QuasiCompact h` and `QuasiSeparated h`. No global qcqs condition on T or U.
  `pushforward_derived`, `pushforward_injective`, and `adjunction_normalized`
  fix R h_et,* and its adjunction. The displayed invertible map is the actual
  counit mate: etale unit, inverse pullback comparison, image of the pinned
  Zariski counit. Naturality follows from these natural transformations.
- Composition: `ordinary_right_comp_sections` is restriction along Mathlib's
  canonical fibre-product comparison. `ordinary_left_comp_mate` pins the
  ordinary tensor compositor to its adjoint mate; `homotopy_comp_representatives`
  records it in every degree, and `derived_comp_normalized` fixes its derived
  comparison by the universal counits. `comparison_comp` is the commuting
  composition diagram against the existing `canonicalDerivedPullbackComposition`.
- Identity: `ordinary_right_id_sections` uses the canonical pullback-identity
  graph, `ordinary_left_id_mate` is its mate, and the homotopy and derived
  normalization fields identify it with multiplication. `zariski_id_normalized`
  uses the pinned ordinary Zariski adjunction and `pushforwardId`;
  `comparison_id` is the requested identity compatibility.
- Structure modules and scalar insertion: both `structure_iso` fields use the
  canonical `pullbackObjUnitToUnit` maps (the Zariski side uses the recorded
  `tensorPullbackObjUnitToUnit`). `structure_compatibility` states the commuting
  ordinary structure-module square. `comparison_representatives` localizes
  this same square on the structure module in degree zero. The adjunction
  normalization fixes scalar insertion on all modules: its transpose is the
  specified ordinary adjunction map, not an arbitrary automorphism. Composition
  is fixed by those same mates and their section formulas.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Qh`; homology via `DerivedCategory.HomologySequence`.
- `def-weil-size-convention` is a recorded metatheoretic convention, with no
  module or declaration; its explicit universes are rendered above.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  reusing Mathlib `SheafOfModules.IsQuasicoherent` and the slice instances.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: `IsQuasiCoherentFiniteType` is
  the dependency's recorded conjunction. Here only its first notion,
  `SheafOfModules.IsQuasicoherent`, is needed; finite type is not assumed.
- `Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare`:
  `zariski_etale_functor_comparison_square`, with its public canonical contexts
  from `SchemeZariskiEtaleQuasiCoherentEquivalence` and their full signatures.
- Added already-landed statement dependencies: `def-pc-derived-category`
  (`schemeDerivedCategory`, `schemeDerivedQCohProperty`), `def-pc-derived-pullback`
  (`derivedPullback`), `def-pc-derived-direct-image` (`schemeDerivedDirectImage`),
  `def-sfb-canonical-scheme-derived-adjunction-composition`
  (`canonicalSchemeDerivedAdjunction`, `canonicalDerivedPullbackComposition`),
  and the live `def-sfb-tensor-pullback-structure-sheaf-map`
  (`tensorPullbackObjUnitToUnit`). Their modules are the recorded upstream
  WeilConjectures modules, read directly. The first is the new definition-node
  owner requested by the return; the second is an already landed owner. Neither
  the mate-evaluation theorem nor the structure-map-isomorphism theorem is a
  statement dependency. No existing dependency node is changed.

Sources checked: Stacks `spaces-perfect.tex` labels `lemma-epsilon-flat`,
`lemma-derived-quasi-coherent-small-etale-site` (including both adjunction maps),
`remark-match-total-direct-images`; `descent.tex` label
`remark-change-topologies-ringed-sites`. The current blueprint unit was read
under `literature/blueprint/latest/`; no unit or source correction is needed.
The ten-step natural-language DAG proof is included verbatim, reflowed, in the
main theorem's docstring. All available recorded proof-dependency modules are
imported; unstated geometric-stalk, acyclic-basis and coproduct prerequisites
have no module to import. Mathlib point exactness, stalk detection, algebraic
closures, site localization and K-injective definitions supply their existing
foundational interfaces where recorded.

Edge cases checked mathematically before drafting and on the finished signature:
empty schemes (zero module categories and vacuous stalk tests); zero complexes;
all positive and negative shifts; genuinely unbounded complexes; arbitrary
non-quasi-coherent modules in exactness/faithfulness; identity and repeated
compositions; non-qcqs schemes with qcqs morphisms. No cohomological bound,
nonemptiness condition, characteristic or finite-type restriction is introduced.
The identity square uses the actual unit normalization, not a merely existing
isomorphism. No STATEMENT-DISPUTED issue or statement correction.

Searches (prescribed `msearch.py`, Q65 and this item):

- LeanFinder, “Unbounded derived categories of quasi-coherent modules Zariski
  etale equivalence compatible pullback pushforward”: eight ordinary adjunction
  and pseudofunctor hits; no derived QCoh comparison.
- Loogle, `DerivedCategory, Functor.IsEquivalence, SheafOfModules.IsQuasicoherent`:
  zero hits, unknown identifier `Functor.IsEquivalence`.
- Mathlib grep, `Zariski.*[Ee]tale|[Ee]tale.*Zariski|epsilon.*[Qq]uasi`,
  `AlgebraicGeometry`: three hits on topology ordering and Zariski locality of
  weakly étale maps; none states this result.
- LeanSearch, “The canonical pullback from Zariski modules to etale modules is
  exact and faithful and induces an equivalence on unbounded derived categories
  with quasi-coherent cohomology”: eight ordinary pullback/adjunction/free-module
  hits; no derived equivalence.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`: existing ordinary
  context/comparison and affine derived realization found and read; the latter
  concerns Spec A and derived global sections, not arbitrary T with this square.
  `grep -rn` for the node id in WeilConjectures returned no hits.
- `rg` over both libraries, Mathlib and `dag/lean_names_upstream.json` for the new
  declaration names returned no collisions.

## Worker cross-check

A second worker-side pass matched each field with the node and Stacks source.
It found and repaired the accidental default localization selected through the
`T.Modules` alias: every localized Zariski map now uses the explicit shared
`SheafOfModules` localization in universe w. It also replaced a naive identity
on complexes by the actual ordinary tensor-pullback identity mate before
localization. The final statement retains all-module exactness, the genuine
unbounded adjoint equivalence, the representative-normalized pullback square,
qcqs (not separated) direct images, and identity/composition/structure maps.
No source statement change or dependency interface repair was needed. The H2
repair below adds definition-node ownership without changing the Lean module.
This is a worker-side cross-check, not an independent reading.

## Second reading by Q65

No second reading by a worker: the dispatcher requires direct delivery and forbids
starting other agents. The maintainer's independent review is the delivery review.

## Validation

Every compiler invocation uses the prescribed `scompile.py` wrapper, with module
mode, explicit universes and no global build. The only postponed proof is the
main theorem. Final compiler and dry-run results are recorded below.

The full-import compilation initially hit the 60-second limit. Profiling isolated
unneeded generated constructor-injectivity lemmas for the witness structures.
`set_option genInjectivity false` omits these generated auxiliary lemmas; it does
not change a field, definition, hypothesis or conclusion. Diagnostic profiling
options were removed from the delivered module.

Final `scompile.py` completed with exit 0: sandbox 53.6 seconds, final module
50.0 seconds, with no errors or warnings. Both runs retain the prescribed
60-second limit, nice 19 and two threads.

`deliver2.py Q65 lem-sfb-derived-etale-zariski-equivalence --no-push` returned
`OK (dry run)` for commit `fc87155adcf`: server preflight and compilation pass;
nothing was pushed by the dry run.


## Repair of returned head 736671499d51

H2 is repaired in both requested places. The item now cites the live definition
node `def-sfb-tensor-pullback-structure-sheaf-map` in place of
`lem-weil-pbc-module-pullback-structure-sheaf`, and the new definition node
`def-sfb-canonical-scheme-derived-adjunction-composition` in place of
`lem-pc-scheme-derived-mate-evaluation`. These own exactly the plain definitions
used by the statement. Neither associated theorem is asserted as a statement
dependency. The Lean source is unchanged (SHA256
`cebc14640b089f058e272a3ecf06d9749709b22601fc0d47c27dcffb43958b12`).
The saved packet was compared field by field with the current base: before repair
only `lean` and the five added `stmt_deps` differed; the accepted statement, proof,
proof dependencies and all other fields agree. The initial saved-packet dry run
returned `OK (dry run)` at `976509b820c`; the returned H2 dependency ownership
issue was repaired even though that mechanical check passed.

## New nodes

`def-sfb-canonical-scheme-derived-adjunction-composition` owns the two existing
plain definitions `AlgebraicGeometry.canonicalSchemeDerivedAdjunction` and
`AlgebraicGeometry.canonicalDerivedPullbackComposition`, both in
`WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation`, read with their
complete signatures, docstrings and bodies at lines 41–63. It is `existing: true`
and adds no Lean module. The primary signature is copied verbatim. The second
signature and the ambient explicit universe/localization binders are recorded in
`lean.note`. Its three statement dependencies are precisely
`def-pc-derived-pullback`, `def-pc-derived-direct-image` and
`def-pc-module-pullback`, as the maintainer requested.

The definition node names arbitrary schemes and morphisms, a common localization
universe, the fixed simultaneous derived counits, the adjunction selected with
those counits and the recorded right-derived unit, and the compositor selected
from that same family. Thus it records the existing constructions with their
normalization rather than postulating an arbitrary adjunction or isomorphism.
`canonicalSchemeDerivedAdjunction` is the literal choice from
`exists_schemeDerivedAdjunction` evaluated on the counits from
`exists_derivedPullbackComposition`; the compositor is the literal choice in
that same family. The representative Hom formula in the new node is the formula
of `exists_schemeDerivedAdjunction`; its compositor is the comparison induced by
the counits and the ordinary adjoint mate of `pushforwardComp`. There is no new
claim of mate evaluation. Sources read: cohomology.tex Tag 0D5S,
`lemma-derived-pullback-composition`, and Tag 08HY, `remark-base-change`.
Edge cases: identity, zero complexes, arbitrary shifts and non-qcqs schemes all
retain the same constructors; the localization instances add no geometry.

Searches for this new owner were run on this repair, and their actual search-log
records are copied into `mathlib_searches`:

- LeanSearch, “Canonical adjunction between derived pullback and derived
  pushforward of scheme modules and canonical composition isomorphism of derived
  pullback”: eight ordinary pullback/adjunction/composition hits, no normalized
  derived scheme construction.
- Loogle, `canonicalSchemeDerivedAdjunction, canonicalDerivedPullbackComposition`:
  no hits; the service reports the first name as an unknown identifier.
- Mathlib grep, `canonicalSchemeDerivedAdjunction|canonicalDerivedPullbackComposition`
  in `AlgebraicGeometry`: no hits.
- `rg` in the DAG, `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`
  and `lean/Sheaf`: found the two upstream definitions and their consumers.
  A JSON-field audit of every `lean.declaration` and `lean.declarations` found no
  existing node owner. Existing theorem/definition nodes merely mention or use
  these constructions in other maps.
- `tools/blueprint_refs.py search 'derived pullback'` and
  `search 'derived adjunction'`: 78 and 28 hits respectively, no owner of these
  fixed scheme-module choices. `ancestor` reports `None` for this item's
  synthetic blueprint ancestry; the new node copies that ancestry and prepends
  this item to `via` as required.

No definition or theorem is duplicated. The already landed structure-map owner
was read with its full `lean` record and upstream map definition; it is cited
without a dependency-record edit. The review's mathematical acceptance and its
advisory about the dispatcher-mandated second-reading section remain applicable.


Repair validation: the explicit `scompile.py` run completed with exit 0, sandbox
53.6 seconds and library module 50.0 seconds, without diagnostics. The worker
self-check verified the two H2 replacements, unchanged Lean SHA256, exactly one
`sorry`, the primary signatures verbatim, new-node citations, and node field/JSON
isolation. It also checked the conventional composition order in the new node's
representative formula: `Q_X(t) ∘ epsilon_f(M)` matches Lean's
`epsilon.app M ≫ Qh.map t`.


The repaired-packet dry run compiled both files and reached preflight. It required
`import_flags: []` on the new definition node; that required field was added.
Its existing-declaration signature check also strips the `noncomputable` modifier,
so the primary `lean.statement` now starts with the verbatim `def` keyword, as in
the live structure-map owner's record. No Lean declaration or mathematical clause
changed in this mechanical repair.
