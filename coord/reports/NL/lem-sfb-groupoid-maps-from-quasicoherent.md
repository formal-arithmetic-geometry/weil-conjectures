## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidMapsFromQuasicoherent` states Tag 076S as
`CategoryTheory.GroupoidModuleHom.restriction_equiv_compatible`. It reuses the landed
literal algebraic-space restrictions and canonical tensor comparisons from
`Sheaf.AlgebraicGeometry.FibredFppfSpaceModuleComparisons`. The only postponed
theorem in this delivery is the main theorem; every definition has real data.
The natural-language node statement is unchanged. No statement correction or dispute.

Hypotheses and clauses, individually:

- The universe convention is `universe u v w`: schemes have universe u, the total
  category has independent morphism/object universes v/w, and module carriers and
  the canonically lifted regular-function rings have universe max (u+1) v w. There
  is no equality imposed between site universes and no smallness premise on H.
- The base is `{S : Scheme.{u}}`; U and R are `{U R : AlgebraicSpace S}`.
- The groupoid maps are `s t : R ⟶ U`, e, i and c on the underlying presheaves,
  with c's domain `pullback s.hom.hom t.hom.hom`. The parameter P is the existing
  `SpaceGroupoidQuotientPresentation` of these very maps. Its `groupoid` field
  expresses all test-scheme groupoid laws with composition first the second arrow;
  its `arrows` field supplies the canonical source-target two-isomorphism.
- The quotient is the total based category C with canonical map x. P's `stack`,
  `fully_faithful`, `locally_surjective` and `composition` fields are precisely the
  existing presentation interface for the fppf stackification. This does not assume
  a replacement presentation equivalence or an arbitrary descent functor.
- The big fppf site and structure sheaf are the recorded `moduliFppfTopology C`
  and `moduliModuleRings C P.stack.1`, with regular-function restriction maps.
- Flatness is `hs : MapIsFlat s` and `ht : MapIsFlat t`; local finite presentation
  is `hslfp : MapIsLocallyOfFinitePresentation s` and the t analogue. These are
  the recorded étale-chart extensions of the Mathlib scheme properties, not the
  stronger representability-by-schemes versions of those properties.
- The quasi-coherent source is `F : (SheafOfModules.isQuasicoherent
  (moduliModuleRings C P.stack.1)).FullSubcategory`, the full subcategory
  for Mathlib's local-free-presentation predicate. H ranges over ALL
  `ringedSiteModules` on the total ringed site, with no predicate attached.
- F_U and H_U are `(spaceTestModuleRestriction P.stack.1 x).obj F.obj` and its H
  analogue. The existing restriction evaluates the original sheaf at `x.obj V.obj`
  for every étale scheme chart V; the existing based-test ring map gives the canonical
  scalar identification. On maps it is the existing `(spaceTestModuleRestriction P.stack.1 x).map`.
- F_R and H_R use the source test `(discreteModuliMap s.hom.hom).comp x`.
  `sourceComparison` uses the identity two-isomorphism; `targetComparison` uses
  P.arrows to land in that SAME source-test restriction.
- Both comparisons use the existing `spaceTestModuleComparison`, selected by
  its chart tensor existence-and-uniqueness property, which characterizes it
  on every tensor b tensor m as b times the ORIGINAL module restriction of m
  along the based test two-isomorphism followed by the target chart map.
  The ambient tensor pullback is the adjoint to
  the normalized compatible-chart-section direct image, with its unit retained.
- Invertibility of the F comparisons comes directly from the quasi-coherent comparison clause of
  `fibred_fppf_space_module_comparisons`, applied with only F and its
  quasi-coherence proof. `sourceComparisonIso` and `targetComparisonIso` use
  those existing IsIso proofs and `asIso`, retaining the exact forward maps.
  There are no duplicate invertibility theorems or extra sorry helpers.
- The first conjunct of the main theorem is `Function.Injective` of the actual
  `(spaceTestModuleRestriction P.stack.1 x).map` on Hom(F,H).
- The equivalence E has target `{a // Compatible P F H a}`. Its displayed forward
  normalization is exactly restriction, so it states both necessity and sufficiency
  of the image equation, with no arbitrary Hom equivalence.
- `Compatible` is, in Lean's diagrammatic order, `(c_s^F)⁻¹ ≫ s^*a ≫ c_s^H =
  (c_t^F)⁻¹ ≫ t^*a ≫ c_t^H`. Both sides have the common F_R-to-H_R type.
  No comparison of H is ever inverted.
- Naturality: the final universally quantified clause covers every source map
  `a : F'.obj ⟶ F.obj`, every target map `b : H ⟶ H'`, and every compatible z.
  Whenever z' is its restricted pre/postcomposition, the inverse extensions obey
  `(E F' H').symm z' = a ≫ (E F H).symm z ≫ b`. Together with the normalized
  forward map and equivalences this is naturality of the bijection in both slots.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its full-category morphisms, EtaleSite, etaleForget and regular-function structure.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and the unchanged Mathlib predicate
  `SheafOfModules.IsQuasicoherent` (local coproduct presentations).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the morphisms are exactly Mathlib's sectionwise linear `SheafOfModules.Hom`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction`, publicly imported for the
  recorded tensor-pullback dependency. The small étale tensor functor here is its
  site counterpart in the next dependency, not Zariski restriction of H.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description` is imported;
  its general stackification interface is specialized by the already landed
  `SpaceGroupoidQuotientPresentation`, not copied or replaced by new axioms.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, including its
  big slice, is used through the quotient and moduli-site interfaces.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`: `moduliFppfTopology`,
  `moduliModuleRings` and the slice sheafification instances.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- Added recorded dependency `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat` and
  `MapIsLocallyOfFinitePresentation`; these keep the scheme properties exact.
- Added recorded dependency `def-sfb-space-groupoid-quotient-presentation`, module
  `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`:
  `CategoryTheory.SpaceGroupoidQuotientPresentation`.
- `def-trf-space-etale-module-functors`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: the existing
  `ModuleChart`, `moduleChartTarget` and `moduleChartPost` are reused unchanged.
  Its live record is left untouched; the item does not reassign its declarations.
- `lem-sfb-fibred-fppf-space-module-comparisons`, module
  `Sheaf.AlgebraicGeometry.FibredFppfSpaceModuleComparisons`, is now a statement
  dependency as well as the original proof dependency. The signature uses its
  `ambientModuleTensorPullback`, `spaceTestModuleRestriction` and
  `spaceTestModuleComparison`. The comparison
  isomorphisms use its main theorem
  `CategoryTheory.fibred_fppf_space_module_comparisons`, quasi-coherent
  comparison clause. I read the
  full signatures and docstrings of the ambient chart diagram, direct-image
  model, unit, tensor section, restriction, comparison formula and its unique
  realization. Their normalization is precisely that required by the item.
  A module-index probe identifies the compiled restriction/comparison owner as
  `Sheaf.AlgebraicGeometry.SpaceTestModuleRestrictionComparison` and the ambient
  pullback owner as `Sheaf.AlgebraicGeometry.AlgebraicSpaceAmbientModuleOperations`;
  both are exposed transitively by the landed comparison module. These are
  existing compiled declarations; neither owning module is supplied or overridden
  by this delivery. The source reader currently lacks those split module files,
  so the compiled signatures and real definition bodies were inspected with
  module-mode #print probes.
- `lem-sfb-stack-quasi-coherent-scheme-restriction` remains a proof dependency,
  with a plain proof import of `StackQuasiCoherentSchemeRestriction`. Its theorem
  gives the section interpretation used in proof step 2. Its `ModuliQCoh`
  abbreviation is no longer used: the full subcategory is written literally,
  using `SheafOfModules.isQuasicoherent` and `moduliModuleRings`. The sheafification
  instances needed for that predicate come from `StackQuasiCoherentAlgebra`.
- `lem-sfb-stackification-module-equivalence` currently has no recorded module
  to import. It is cited in the complete main proof docstring. No new hypothesis
  for that proof theorem is imposed.

Edge cases checked before writing: U and R may be empty; P's local covering
condition then also covers the empty quotient and forces the correct local-empty
objects. No Nonempty atlas or test set is imposed. Zero F and zero H remain in
scope, as do non-quasi-coherent H and H with noninvertible nonétale comparisons.
No finite generation, finite presentation of modules, separatedness, or characteristic
assumption is introduced. Identity/groupoid arrows keep their original restriction
maps, and the inverse comparison is taken only for F. The module universe permits
arbitrarily large targets relative to the scheme universe.

Searches (2026-10-24):

- msearch.py leanfinder: "Maps from quasi coherent modules on a flat groupoid
  quotient into arbitrary sheaves of modules". Eight hits, all local presentations
  or quasi-coherence data; no Tag 076S Hom-descent theorem.
- msearch.py leansearch: "Sheaves of modules restriction along a groupoid
  presentation maps from a quasi coherent module to arbitrary modules". Eight
  hits (Tilde, local presentations, scheme open restriction); none is this statement.
- msearch.py loogle: "SheafOfModules, IsQuasicoherent". No hits; remote Loogle
  does not recognize the unqualified IsQuasicoherent identifier.
- msearch.py grep: `descent.*[Hh]om|[Hh]om.*descent`, CategoryTheory/Sites.
  Eighteen hits, including DescentData morphisms. These describe maps already in
  a descent-data category, not maps into an arbitrary big-fppf module.
- rg over `lean/WeilConjectures` for the item id, groupoid maps and 076S: no match.
  rg over `lean/Sheaf` found the consumer StackLqcCoherator proof docstring and
  the existing quotient-presentation/module-operations interfaces, but no theorem.
- The earlier ambient search predates the landed N7 interface. On this repair
  I read the local and server source of `FibredFppfSpaceModuleComparisons`: its
  ambient module universe is exactly max(u+1,v,w), its chart-limit model retains
  every projection, and its comparison formula is the original section
  restriction. These existing declarations supply all formerly duplicated data.
  The compiled ambient ring uses the canonical regular-function ULift and
  the module universe remains max(u+1,v,w); independent site sizes are preserved.
  Module-mode #print probes resolved the published interface when the source
  reader returned an older revision: restriction is a functor named
  `spaceTestModuleRestriction`, comparison is `spaceTestModuleComparison`, and
  the quasi-coherent theorem takes K and its IsQuasicoherent instance.

Validation: the remaining module compiled cleanly with scompile.py against the
live published library (sandbox and library checks); the complete packet is
then checked by deliver2.py --no-push.
No additional modules or dependency-node overrides are delivered.

## Second reading by NL

I compared the repaired file with the unchanged Tag 076S node and the full landed
`FibredFppfSpaceModuleComparisons` source. The presentation P and all four
flatness/finite-presentation hypotheses are retained. F uses the literal full
subcategory for Mathlib's quasi-coherence predicate; H remains arbitrary.
The reused restriction has the original module sections and section maps with
the canonical regular-function identification. The reused tensor comparison
has an existence-and-uniqueness characterization on every chart tensor, so this
repair introduces no arbitrary map. Its source specialization uses the identity
two-isomorphism; its target specialization uses P.arrows, both with the source
test as common target. The compiled existing theorem applied to F and its
quasi-coherence instance gives F invertibility without flatness or finiteness; the two `asIso` definitions retain the actual maps.
I checked the equation in Compatible, the injective restriction map, normalization
of the equivalence's forward map, and inverse naturality in both F and H.
Empty charts, identity arrows, zero modules and non-quasi-coherent H are covered.

The mismatch found in the returned packet was duplicated ownership of ambient
operations. I removed the entire ambient module and its proposed definition node,
and also removed duplicate test/comparison helpers and invertibility theorems.
The final six declarations specialize existing canonical maps and state the item.
No declaration was renamed to hide a duplicate. The natural-language statement,
its hypotheses and its proof outline are unchanged.

## Returned-delivery repairs

The immutable returned head is 4c581992bb7d. Relative to it, this repair removes
`AlgebraicSpaceAmbientModuleOperations.lean` and
`def-sfb-space-ambient-module-operations.json` from the packet. All 16 collided
ambient names are reused through the imports of `FibredFppfSpaceModuleComparisons`,
including
`AmbientModules`, `AmbientModuleDirectImageModel`, the chart scalar/maps/diagram,
the normalized direct image and its unique universal property, and the tensor
pullback/adjunction/sections. The existing test restriction, comparison and
quasi-coherent invertibility are reused as well. The node's lean.declarations now
contains only the six declarations actually delivered, and stmt_deps cites the
landed comparison node. The old module-operations dependency record remains
untouched. The earlier H2 repair is retained: scheme restriction stays only in
proof_deps, and the full subcategory is inline. The second-reading section records
the current clause checks rather than the superseded ambient construction.

Compared with current main, the item's only field changes are stmt_deps and lean;
there is no alteration of its mathematical statement, proof, source or other metadata.

## Returned fix-file format repair

The return for immutable head 6aef9e45469c reports an `--apply-fixes` input
format error, not a Lean or mathematical mismatch. I read the stage-2
`merge_delivery.py` fix parser and the prescribed `deliver2.py` wrapper.
They require different inputs: the worker wrapper reads the full node from
`dag/nodes/sec-six-functors-basics/lem-sfb-groupoid-maps-from-quasicoherent.json`,
whereas the reviewer's `--apply-fixes` accepts only the item's lean record under
`lem-sfb-groupoid-maps-from-quasicoherent.lean-record.json`. A full item JSON
named `lem-sfb-groupoid-maps-from-quasicoherent.json` is rejected by that parser.

The sandbox now has a separate `review-fixes` directory containing exactly:

- `GroupoidMapsFromQuasicoherent.lean`: the delivered module.
- `lem-sfb-groupoid-maps-from-quasicoherent.lean-record.json`: only the lean object,
  not the whole DAG node.
- `lem-sfb-groupoid-maps-from-quasicoherent.report.md`: this report.

The worker packet retains the full node at the required DAG path, and this
report records the corrected reviewer input packaging. No new definition node
or statement-change file is needed. When applying reviewer fixes, use only the
three supported filenames above, or merge the reviewed delivery without
`--apply-fixes` if no reviewer change is needed. Do not put the whole item node
in the fix directory. This follows the exact parser branches in
`tools/merge_delivery.py` and changes no launcher or maintainer tool.

I compared the retained module and record with the returned version: the Lean
signature and all six declarations are unchanged. Compared with current main,
the only node deltas remain stmt_deps and lean. The module passed scompile.py
again, both sandbox and library checks, with no errors or unexpected warnings.
The report and supported fix-package format are the repair in this delivery.
