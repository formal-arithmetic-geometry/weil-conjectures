## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.SchemeFppfFlatLfpAffineAcyclicity` as
`AlgebraicGeometry.Scheme.scheme_fppf_flat_lfp_affine_acyclicity`. Its proof is `sorry`.
The original statement, proof and proof dependencies are retained. The only item
changes are the Lean record and addition of the canonical-comparison definition node
to `stmt_deps`.

Read source: `literature/stacks-project/descent.tex`, lines 3755–3880, especially
Tag 0756, `lemma-quasi-coherent-and-flat-base-change`. Its hypothesis (2) is exactly
the restricted comparison class in this item. Its conclusion for id_U, together with
affine quasi-coherent etale acyclicity, is the item. The kernel/cokernel argument and
module/abelian comparison are reproduced in the main docstring in five steps.

Hypothesis and clause correspondence:

- The universe convention is explicit `universe u`. `U : Scheme.{u}` uses schemes
  in the fixed bound. `Over U` has objects in u+1 and arrows in u. Structure rings
  stay in u; module sections and their injective resolutions live in the common
  universe u+1. This does not identify the site universes or add essential-smallness
  assumptions. The coefficient extension `sfbModuleULift` is actual ULift on sections,
  with the same ring action, rather than a chosen module or an arbitrary functor.
- Affineness is `[IsAffine U]`, the existing equivalence-to-spectrum predicate.
- The site is exactly `fppfTopology.over U` on `Over U`; no replacement topology.
- `G : ringedSiteModules.{u+1} (sfbFppfRings U)` is an arbitrary module sheaf, with
  section rings Γ(V,O_V) and pullback of functions, as already constructed by
  `SchemeBigFppfQuasicoherentEquivalence`. No quasi-coherence of G is assumed.
- `M : U.Modules` and `[M.IsQuasicoherent]` give an arbitrary quasi-coherent Zariski
  module; no finite-type condition is used. Its carrier lift is necessary because
  Mathlib's quasi-coherence predicate uses the ring and module universe together,
  while the big site and its resolutions require the larger common universe.
- `_het : Nonempty (...)` is precisely the module isomorphism between restriction
  `sfbFppfEtaleRestriction U` and the associated etale module, the canonical tensor
  extension `sfbZariskiEtaleExtension U` of the carrier-lifted M. The existing
  Zariski/etale equivalence identifies this extension with the tensor-section
  formula Γ(V,v^*M), with ULift of the section carriers. Orientation of the
  isomorphism is immaterial and `Nonempty` asks only that an isomorphism exists.
- `_hcomp` quantifies over every `V : Scheme.{u}` and every `g : V ⟶ U`, guarded
  by `Flat g` and `LocallyOfFinitePresentation g`. Its conclusion is `IsIso` of
  the actual adjunction-transpose comparison, not an arbitrary arrow and not a
  noncanonical isomorphism. No surjectivity, affineness, separation, finite type
  or comparison hypothesis is imposed on these test schemes or other morphisms.
- `q : ℕ` and `_hq : 0 < q` are all the positive cohomological degrees.
- The conclusion is `IsZero (((sfbFppfModuleGlobalSections U).rightDerived q).obj G)`.
  Global sections are evaluation at `Over.mk (𝟙 U)` in abelian groups. The source
  of `rightDerived` is the category of structure-module sheaves, so its resolutions
  are injective MODULE resolutions. It is not cohomology of a chosen underlying
  abelian resolution or a Čech complex.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` (via the imports).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, `fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation of Mathlib `SheafOfModules`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`;
  `Morphisms.Etale`: `Scheme.Etale`, `Etale.forget` and `Scheme.Hom.Etale`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` exports
  `SheafOfModules.IsQuasicoherent`; its finite-type conjunction is deliberately
  not used, since the node requires quasi-coherence alone.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Modules.tensorPullback`, `tensorPullbackSectionAdjunction` and the normalized
  section/composition maps used by the existing associated-sheaf conventions.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective`;
  `...Injective.Resolution`: `InjectiveResolution`.
- `Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`:
  `sfbGlobalFppfRings`, `sfbFppfStructureSheaf`, and `sfbFppfRings`, now owned by
  `def-sfb-scheme-big-fppf-structure-rings`. The equivalence theorem remains only
  a proof dependency of the acyclicity theorem, not an owner of these definitions.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Modules.smallEtaleModuleRing` and `zariskiEtaleOpenRingMap` belong to
  `def-sfb-scheme-zariski-etale-module-constructions`. `smallEtaleModuleRingMap`
  and `smallEtaleModulePushforward` are now owned by
  `def-sfb-scheme-small-etale-module-direct-image`. The extension uses the named
  `sfbOpenEtaleContinuous U`, never a context chosen from the equivalence theorem.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`:
  `SheafOfModules.pullback`, `pushforward`, `pullbackPushforwardAdjunction`.
  The helper supplies the universe-general right-adjoint existence property,
  then uses these existing functors without copying them.

All stated proof-dependency modules are imported without `public` visibility,
including the normalized big-fppf equivalence, Zariski/etale equivalence, module
adjunction, exact forgetful functor, long exact sequence, affine associated-sheaf
acyclicity, and module/abelian evaluation comparison. Two proof-only DAG nodes
have no declaration at this reading: `lem-sfb-big-fppf-zariski-ringed-comparison`
and `lem-sfb-fppf-flat-lfp-zero-cohomology`; their imports await their own statements.
Neither is required to type the item. The module docstring names their exact use.

Edge cases checked before writing:

- U empty, including the spectrum of the zero ring: no nonempty or nontrivial
  hypothesis is present; sheaf gluing over the empty cover forces zero sections.
- M = 0, G = 0, arbitrary infinite modules: there is no finite-generation binder.
- Identity and open-immersion g are included. The canonical comparison is defined
  for all g, and no invertibility is assumed outside the flat lfp class.
- A non-flat test map is left unrestricted; kernel/cokernel need only vanish on
  flat lfp objects, so the statement does not accidentally require G cartesian.
- Positive degree starts at 1; degree zero is intentionally not asserted zero.
- Arbitrary characteristic and non-Noetherian affine bases are admitted.
- Site objects u+1 and arrows u are retained; rings u and module carriers u+1
  are independent as required by the common-universe convention.

Searches actually run via msearch.py:

- LeanFinder: “Fppf cohomology of an affine scheme vanishes for a module sheaf
  with quasi coherent etale restriction and flat locally finitely presented
  comparison isomorphisms”. Eight hits about affine limits, ordinary module
  categories, cotangent cohomology and formal smoothness; no exact theorem.
- Loogle: `"fppf", "cohomology"`: zero hits.
- Mathlib grep: `fppf.*cohom|cohom.*fppf|flat.*comparison`, AlgebraicGeometry:
  zero hits.
- LeanSearch and LeanFinder: “Canonical comparison from pullback of the small
  etale restriction of a big fppf module sheaf to its restriction after base
  change”. Generic pullback, pullback adjunction, pullback of free modules and
  tensor constructions; no specialized canonical comparison.
- Mathlib grep: `fppf.*[Ee]tale.*[Mm]odule|[Ee]tale.*[Ff]ppf.*[Cc]omparison`,
  AlgebraicGeometry: zero hits.
- The same regex in `lean/WeilConjectures` gives no scheme specialization;
  in `lean/Sheaf` it finds the separate algebraic-space comparison presentation.
- Exact item-id search in upstream Lean gives no declaration; the affine
  associated-sheaf acyclicity result is weaker than this arbitrary-G statement.
- DAG title/statement search finds the existing scheme Zariski/etale definition
  node and the separate algebraic-space comparison. Neither defines this map.
  `blueprint_refs.py search 'fppf etale comparison'` gives zero matches; ancestor
  returns None, as recorded on the item itself.

No statement dispute or source correction is needed.

## New nodes

`def-sfb-scheme-fppf-etale-module-comparison` defines the missing canonical
scheme comparison of Stacks 03FH and 0756(2). Its module constructs the two
restriction functors on the existing rings, the actual first-projection arrow,
the linear section map induced by G's restriction, and its adjunction transpose.
It also supplies common-universe Zariski extension, the explicit carrier ULift,
module evaluation, and the proof-only continuity, right-adjoint, linearity,
sheafhood, enough-injectives and additivity facts needed to type these definitions.
Each postponed fact is a named theorem with its proof in its docstring and its
matching property in this definition node. Definitions contain real data only.
Its searches are the actual logged results summarized above. No scheme comparison
definition node already exists; the algebraic-space interface uses a different
presented-site construction and is not a duplicate at this site.

`def-sfb-scheme-big-fppf-structure-rings` records existing declarations in
`Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence`: the ambient
regular-function ring sheaf (`sfbGlobalFppfRings`), its commutative slice sheaf
(`sfbFppfStructureSheaf`), and the latter with commutativity forgotten
(`sfbFppfRings`). Each restriction is pullback of functions. This is precisely
Stacks 03DU(1); no equivalence assertion is part of this definition node.
LeanSearch for the big-fppf regular-function sheaf returned generic structure
sheaves; Loogle `"fppf", "Sheaf"` and the Mathlib name grep returned zero.
Repository and DAG searches located these definitions only in the existing
module and theorem record; no definition node owns them. The node therefore
uses `existing: true` and copies no Lean data. Empty schemes and arbitrary
base schemes require no added hypotheses.

`def-sfb-scheme-small-etale-module-direct-image` records the existing
`Modules.smallEtaleModuleRingMap` and `Modules.smallEtaleModulePushforward` in
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`. Its arbitrary
scheme map is the binder `a : U ⟶ T`; its base-change functor is `a.Etale`; its
ring map is `etaleStructurePresheafToPullback a` with commutativity forgotten;
its module direct image is exactly `SheafOfModules.pushforward` along that map.
The first projection is the same one used in the canonical comparison. These
are Stacks 03LC and the base-change direct-image formula in Topologies,
`lemma-morphism-big-small-etale`(2). LeanSearch returned generic module
pushforward, scheme pushforward, and the small-etale topology; LeanFinder
returned general etale declarations. Loogle `"smallEtale", "Ring"` and Mathlib
grep returned zero. The existing Zariski/etale constructions definition node
omits exactly these two names; the DAG name scan found no definition owner.
This node also uses `existing: true`. It admits every scheme map, including
identities and non-flat maps, with no new flatness or affineness assumption.
All searches above are stored verbatim in the new nodes' `mathlib_searches`.

## Returned-delivery repair

The immutable returned delivery was d39475f505f0. This repair addresses each
part of its H12/H2 return:

- (a) The new regular-function structure-rings definition node owns all three
  named ring declarations. The canonical-comparison node cites it in place of
  `lem-sfb-scheme-big-fppf-quasicoherent-equivalence` in both its text and
  `stmt_deps`.
- (b) The new small-etale direct-image definition node owns both omitted
  declarations. The comparison node cites this node directly. The published
  Zariski/etale constructions node is not modified.
- (c) `sfbOpenEtaleContinuous` is a named sorried theorem with a source and full
  cover-preservation proof description. The comparison definition node now
  explicitly states continuity of the open-subscheme inclusion and lists the
  theorem among its declarations. `sfbZariskiEtaleExtension` uses its proof
  directly; there is no `Classical.choose` of the equivalence theorem.

The Lean change is confined to this continuity theorem, its docstring, and the
extension's continuity proof. All other Lean declarations, in particular the
item's full theorem statement, retain the returned mathematics. Node records
were rebuilt from the current read-only main node and its unchanged statement,
proof and proof dependencies. The two new existing-definition nodes were checked
against the current source declarations and existing definition-owner records.
No statement correction or dependency module is needed.

## Second reading by Q104

A separate manual rereading was made by the same dispatcher worker; the brief
forbids starting another agent, so this is not represented as an independent
second agent's review. The maintainer's delivery review remains independent.

I reopened the node, Stacks 0756 and both complete files. The affine hypothesis
is exactly IsAffine, the G binder has no cartesianness hypothesis, quasi-coherence
is required only for M, and the comparison quantifier has exactly Flat and
LocallyOfFinitePresentation as guards. The conclusion derives module evaluation
at id_U only in q > 0. The comparison is the transpose of restriction along
pr_1, including the pulled-back scalar action; no arbitrary arrow is supplied.
The ULift explicitly raises M's section carriers for the common module category;
it leaves the mathematical module, scalar ring, and quasi-coherent condition
unchanged. During this pass I replaced a composite overMap definition by direct
restriction along Etale.forget V followed by Over.map g: it has the same sections
and maps, while avoiding an expensive scalar-transport elaboration. The final
code has explicit universes and binds every variable, with autoImplicit false.

Validation: both delivered modules compiled cleanly through scompile.py, including
separate private-overlay and final module-name checks. The prescribed deliver2.py
--no-push dry run passed preflight and per-file compilation (313b68261a1).

Repair rereading: I checked both existing-definition nodes against the complete
recorded declaration signatures and docstrings. Their clauses select only regular
functions, the actual base-change ring map, and its module direct image. I checked
that the comparison's `stmt_deps` now cites both owners and that its new continuity
clause matches `sfbOpenEtaleContinuous`. The extension retains the same canonical
ring map and tensor pullback. No clause of the acyclicity theorem was changed.

Repair validation: scompile.py compiled both delivered files against the live
published build, including private-overlay, sandbox and final module-name checks,
with no errors or unexpected warnings. The two existing-definition nodes add
no Lean files and use the published declarations in place.

Repair dry run: deliver2.py --no-push passed the server preflight and all per-file
compilation checks at efb1c638c02. The packet includes the corrected comparison
module, the unchanged item module, all four node records, and this report.
