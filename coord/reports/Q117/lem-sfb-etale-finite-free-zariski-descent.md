## Worker report

Item: `lem-sfb-etale-finite-free-zariski-descent`.
Module: `Sheaf.AlgebraicGeometry.EtaleFiniteFreeZariskiDescent`.
Declaration: `AlgebraicGeometry.Scheme.Modules.etale_finite_free_zariski_descent`.
The delivery states both directions in one theorem, with its single proof `sorry`.
It defines no new notion, changes no dependency, and leaves the node statement unchanged.

Sources read: `literature/stacks-project/descent.tex`,
`lemma-equivalence-quasi-coherent-properties` (05VG),
`lemma-finite-locally-free-descends` (05B2), and
`proposition-equivalence-quasi-coherent` (03DX), part (2).
The finite-locally-free clause of 05VG applies without the locally Noetherian
qualification that its separate coherent-module clause needs. Tag 05B2 imposes no common
rank. Its proof descends finite presentation and flatness.

### Hypotheses and conclusions

* A scheme T: `(T : Scheme.{u})`, with no additional scheme assumptions.
* A quasi-coherent module on its small étale ringed site:
  `(F : SmallEtaleModules T) [F.IsQuasicoherent]`. The abbreviation is exactly
  `SheafOfModules.{u} (smallEtaleModuleRing T)`, with regular functions as its ring sheaf.
  Quasi-coherence is Mathlib's local free-presentation predicate, also used by
  `def-trf-space-quasi-coherent-module`, not a private replacement.
* Restriction F_Zar under the recorded equivalence: `c.restriction.obj F`.
  `ZariskiEtaleModuleContext.restriction` is evaluation on open subschemes with the
  canonical regular-function scalar map, not a chosen inverse functor.
* An arbitrary étale family: `(ι : Type v) (U : ι → Scheme.{u})`
  `(e : ∀ a, U a ⟶ T) [∀ a, Etale (e a)]`. The independent index universe allows
  arbitrary families; there is no finiteness or nonempty-index hypothesis.
* Joint surjectivity: `∀ x : T, ∃ (a : ι) (y : U a), e a y = x`.
  This is the underlying point-surjectivity condition for an étale covering family.
* Tensor pullback along each e_a:
  `(smallEtaleModulePullback (e a) (hp (U a) (e a))).obj F`.
  This is the existing canonical ringed-site pullback from the scheme equivalence
  module, constructed by Mathlib's module pullback and sheafification.
* Locally finite direct sums after each pullback: the hypothesis
  `∀ a, SheafOfModules.IsFiniteLocallyFree (...)`. The upstream predicate requires
  local generators whose free maps are isomorphisms and whose individual generator
  types are finite. It permits different cardinalities on different covering members.
* Zariski conclusion: `(c.restriction.obj F).IsFiniteLocallyFree`.
  On the site of opens, its covering local finite free frames say exactly that every
  point has a neighbourhood on which the module is a finite sum of the structure module.
* Converse: the second conjunct is independently quantified over `(H : T.Modules)`
  and asserts `H.IsFiniteLocallyFree → (c.extension.obj H).IsFiniteLocallyFree`.
  It therefore applies to every Zariski finite locally free module, without requiring
  the original F or any covering data. Such an H is already quasi-coherent.
* No constant-rank or Noetherian hypothesis: neither appears in the signature.
  There is also no quasi-compactness or separatedness restriction on T or the family.

The initial existential `c` contains only the continuity and right-adjoint-existence
proofs in the recorded `ZariskiEtaleModuleContext`; its functors have fixed definitions.
The existential `hp` likewise supplies right-adjoint-existence proofs for the recorded
scheme étale direct images. These are conclusions, not extra hypotheses. Their existence
is supplied by `scheme_zariski_etale_quasiCoherent_equivalence` (including its arbitrary
scheme-morphism clause). Both are proof data: no object, module, functor, action or
comparison is freely chosen. They avoid adding otherwise necessary API proof parameters
as mathematical assumptions. There is no choice from an existence theorem to define data.

### Dependency declarations read and used

All six statement-dependency nodes and their records were read, followed by the actual
declarations and docstrings. Their modules are publicly imported.

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`; the actual predicate it specializes is
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation for the same `SheafOfModules` used here.
* `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`,
  `SmallEtaleModules`, `smallEtaleModuleRing`, `ZariskiEtaleModuleContext`,
  its `restriction` and `extension`, `smallEtaleModulePushforward`, and
  `smallEtaleModulePullback`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicGeometry.AlgebraicSpace.ModuleDirectImageModel`, `moduleDirectImage`,
  `moduleTensorPullback` and `moduleTensorAdjunction` were read. That record supplies
  general algebraic-space operations; for this scheme statement the equivalence's
  existing `SmallEtaleModules` and `smallEtaleModulePullback` supply the canonical
  scheme-site presentation. No second operation or category is defined in this delivery.

Finite local freeness itself is reused from
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
`SheafOfModules.IsFiniteLocallyFree`, not `IsFiniteLocallyFreeOfRank`.
Its defining `LocalGeneratorsData.IsLocallyFreeData` and `IsFiniteType` were read.

Every recorded proof-dependency module is imported (ordinary imports unless already
public). These are `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
(`isQuasicoherent_pullback`),
`Sheaf.AlgebraicGeometry.EtaleExtensionFreePresentationsHom`
(`etaleExtension_free_presentations_hom`),
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
(`tensorPullback`, `tensorPullbackSectionAdjunction`, composition comparison),
`Mathlib.AlgebraicGeometry.Sites.Etale` (`smallEtaleTopology` and
`ofArrows_mem_smallEtaleTopology_iff`), the already public morphism-étale module
(open immersions, `etale_comp`, `Etale.of_comp`),
`Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` (`fpqcCover_of_smallEtaleCover`),
`WeilConjectures.AlgebraicGeometry.Descent` (the recorded descent declarations,
especially `isFinitePresentation_of_toDescentData_iso` and
`isLocallyFree_of_toDescentData_iso`),
`Sheaf.AlgebraicGeometry.CoherentFiniteType` (the quasi-coherent predicate), and
`Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`
(`restrictFunctorIsoTensorPullback`, `restrictFunctorIsoTensorPullback_unit`).
The theorem docstring contains all five natural-language proof steps and their node ids.

### Edge cases

* Empty T: all point-local assertions are vacuous; an empty covering is allowed.
* Empty index type over nonempty T: joint surjectivity fails, as required.
* Zero module and rank-zero frames: the finite index type can be empty; neither
  `Nonempty` on a generator type nor a positive-rank restriction occurs.
* Varying and unbounded ranks, including across disconnected components: finiteness is
  imposed separately on each frame. There is no globally prescribed natural number.
* Non-Noetherian and non-quasi-compact schemes: no instance excludes them.
* Identity étale cover: the hypothesis reduces to étale finite local freeness of F,
  so restriction has the claimed Zariski property.
* The converse is outside the first conjunct's F/family quantifiers, so it does not
  disappear when no F or cover has been supplied.
* All universes and binders are explicit; `autoImplicit` and `relaxedAutoImplicit`
  are disabled. No equality of object and morphism universes is imposed.

### Searches and validation

Ran the prescribed `msearch.py Q117 lem-sfb-etale-finite-free-zariski-descent` searches:

* `leanfinder`: "A quasi coherent module on the small etale site which is finite
  locally free on an etale cover is finite locally free on the Zariski site".
  Eight hits concerned local finite presentation/generators; none was this comparison.
* `loogle`: `SheafOfModules.IsFiniteLocallyFree` returned zero hits with an unknown
  identifier message, because that declaration is an upstream extension of Mathlib.
* `grep`: `IsFiniteLocallyFree|IsLocallyFree` in
  `Algebra/Category/ModuleCat/Sheaf` returned five Mathlib locally-free-data hits;
  the finite predicate was then found by direct upstream source search.

Direct `rg` searches of both `lean/WeilConjectures` and `lean/Sheaf` for
`etale.*[Ff]inite.*[Ff]ree`, `[Ff]inite.*[Ff]ree.*[Ee]tale`,
`IsFiniteLocallyFree`, and `zariski.*[Ff]ree` found the reusable variable-rank
predicate, the equivalence/free-presentation modules, and unrelated coefficient-sheaf
and finite-morphism results. No existing declaration states this node. Exact searches
for the item id, module and declaration name, including `dag/lean_names_upstream.json`
and the prescribed upstream `grep -rn` item-id search, found no duplicate.

The first compile caught a line-break syntax error in field notation; the statement
now uses the fully qualified predicate application. The corrected module passed
`scompile.py Q117 lem-sfb-etale-finite-free-zariski-descent` in both sandbox and library
module modes, each in 2.6 seconds, with no errors or warnings. No local compiler or
global build was run. The JSON changes only `lean`, with the signature copied verbatim.
No statement fault or disputed assertion was found.

## Second reading by Q117

Read-back check by the assigned worker, with the source node and completed module open;
the dispatcher forbids starting other agents, and independent delivery review belongs
to the maintainer. This section records the worker's check, not an invented independent
review.

Checked the scheme and quasi-coherent small-étale module binders, the family of étale
maps, and the pointwise joint-surjectivity hypothesis against the node. Checked that
the pulled-back module is tensor pullback by the recorded construction and that its
local predicate has finite, individually varying frame ranks. Checked that the first
conclusion is restriction to Zariski opens, not another module equipped with an
unspecified comparison. Checked that the second conjunct covers all finite locally
free Zariski modules independently of the descent input. Inspected the existing
finite-locally-free definition to confirm that zero rank and varying ranks are included.
The existential API witnesses contain only proof fields and introduce no new mathematical
hypotheses. The node needs no correction or dependency repair. The read-back found no
remaining mismatch; the only implementation repair was the field-notation line break
reported above.
