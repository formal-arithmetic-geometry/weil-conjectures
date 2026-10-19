## Worker report

The module states the complete node, using the adjoint-equivalence criterion on the two quasi-coherent full subcategories. The statement of the node is unchanged. All definitions contain explicit data or a canonical left adjoint selected by its universal property. All theorem proofs are `sorry`.

The constructions in this module are the specialization needed for this node: the regular-function ring sheaf on the scheme's existing small étale site; the existing inclusion of opens; its regular-function structural map and module restriction; canonical module tensor pullback; the scheme-base-change site functor, structural ring map and module direct image; and the canonical comparison maps. They do not replace any of the dependency definitions. In particular, the existing associated abelian sheaf is retained and the theorem specifies the natural, scalar-compatible identification with the underlying sheaf of the module extension.

Clause-by-clause correspondence:

- Every scheme is `T : Scheme.{u}`, with no finiteness, separation, Noetherian or characteristic hypothesis. The family of proof contexts `c` supplies continuity and existence of the canonical left adjoint for each actual inclusion of opens. These are conclusions, not additional hypotheses, and contexts contain no rings, modules, morphisms or functors.
- Ordinary quasi-coherent modules are `F : T.Modules` with `F.IsQuasicoherent`, using the existing Mathlib predicate. Étale quasi-coherent modules are `G : SmallEtaleModules T` with the same general-site `SheafOfModules.IsQuasicoherent`, interpreted on the actual small étale ringed site.
- `smallEtaleModuleRing` has precisely `Gamma(V,O_V)` as its section ring; its restrictions are the existing `Scheme.etaleStructurePresheaf` restrictions. Only the proof of its ring-valued sheaf condition is postponed.
- The existing `AlgebraicGeometry.gabberOpenEtale` sends an open to its inclusion. `zariskiEtaleOpenRingMap` uses `Scheme.restrictFunctorΓ.inv`, the canonical identification of functions on an open with functions on its open subscheme. `zariskiEtaleModuleRestriction` is module precomposition and this scalar restriction, so its section groups are exactly `G(W -> T)`.
- `zariskiEtaleModuleExtension` is Mathlib's canonical `SheafOfModules.pullback` for that specific ringed-site map, with its `pullbackPushforwardAdjunction`. This is the ringed-site tensor inverse image `O_et tensor_(epsilon^-1 O_Zar) epsilon^-1(-)`, represented in Mathlib by module-presheaf inverse image followed by sheafification. It is not the abstract *scheme* module pullback prohibited in the brief. The context supplies only the right-adjoint-existence proof; the universal property determines the left adjoint up to its unique adjunction-compatible isomorphism.
- The first two conjuncts assert preservation of quasi-coherence in both directions and that the actual adjunction unit and counit are isomorphisms on these full subcategories. This is exactly an adjoint equivalence with the specified restriction inverse, rather than an equivalence with an unspecified inverse or functor.
- `e T F` identifies the underlying additive sheaf of this extension with the existing `etaleTensorSectionsSheaf F`, whose objects and restrictions are the dependency's actual tensor-section formula. The scalar equation makes this identification linear over `Gamma(V,O_V)`. Its naturality equation identifies every module map with `Gamma(V,u^* f)`.
- The unit equation on each open `W` composes the unit with `e` and the existing `tensorOpenSectionIso` and obtains the identity. The counit equation uses the inverse open-section coordinates and obtains the identity on `G(W -> T)`. Its proof argument `h` only supplies the already asserted quasi-coherence of the restricted module to the dependent family `e`; it introduces no new mathematical condition.
- The rank-one clause is `F.IsInvertible` if and only if, locally in the small étale topology, the restriction of the extension is isomorphic to the unit ring module. The displayed covering-sieve formula is precisely the line-module condition of `def-trf-algebraic-space`, specialized to the scheme's existing small étale site. It is written directly, without defining a second line-module predicate or constructing a second algebraic-space model of a scheme. The next clause explicitly asserts that every site line module is quasi-coherent and its open restriction is invertible. Thus the full subcategories of line modules are identified in both directions, including lines not supplied with a quasi-coherence proof beforehand.
- For every `a : U -> T`, without a quasi-compactness or separation restriction, `smallEtaleModuleRingMap a` is the existing pullback of functions along `V times_T U -> V`. The pushforward uses `a.Etale`, the actual base-change site functor. The theorem supplies the existence proof of its canonical tensor left adjoint.
- The natural isomorphism `r` compares the two composites of module direct images. At every open its map is explicitly the restriction along the existing `AlgebraicGeometry.gabberPreimageEtaleIso`, the canonical identification `a^-1 W = W times_T U`. This pins down `r` on all sections and all module maps.
- `zariskiEtalePullbackComparison` is the canonical left-adjoint mate of this `r`, using the recorded unit-normalized ordinary tensor adjunction and the two ringed-site module adjunctions. Its type is the natural isomorphism `tensorPullback a >>> extension U ~= extension T >>> smallEtaleModulePullback a`. Thus the required pullback comparison is supplied by actual data, not a bare existential isomorphism or an arbitrary map. This construction already makes sense on all modules, and its quasi-coherent restriction is the node's comparison.
- Only the last block assumes `QuasiCompact a` and `IsSeparated a`. These are the ordinary scheme meanings of the properties in the source and the scheme specialization of the algebraic-space locality dependency. For every quasi-coherent `H`, it asserts quasi-coherence of both direct images and invertibility of `zariskiEtalePushforwardComparison`.
- That direct-image comparison is explicitly the counit mate of the already fixed pullback comparison: insert the étale unit, use the inverse pullback comparison, and apply the ordinary module counit. The penultimate equation states naturality in `H`. The final equation says that after restriction and the canonical `r`, it is the direct image of the ordinary extension unit. The preceding open-section unit identities therefore say exactly that it is identity on `Gamma(a^-1 W,H)` under the two section identifications.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-sc-etale-qcoherent-module`: `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`, `Scheme.Modules.etaleTensorSectionsSheaf`; its unchanged additive sheaf is the target of `e`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` imports the existing Mathlib `SheafOfModules.IsQuasicoherent`. The finite-type conjunction is not asserted by this node and is not used in place of quasi-coherence.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, retaining its existing sectionwise tensor, sheafification and change-of-rings construction.
- `def-trf-space-quasi-coherent-module`: the Mathlib match `SheafOfModules.IsQuasicoherent`, `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`; no missing Lean record was invented for this Mathlib leaf.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `Scheme.Modules.IsInvertible`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, including its small-site local-unit condition `AlgebraicSpace.IsLineModule`. The theorem uses the same local-unit formula directly on the already given scheme site.
- `def-pc-module-pullback`: `WeilConjectures.AlgebraicGeometry.TensorPullback`, `Scheme.Modules.tensorPullback`. The current module was also read through `scompile.py --source`; its maps are inverse image followed by the existing change of rings.
- `lem-trf-space-qc-separated-etale-local`: `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`, including the scheme-test diagonal and quasi-compact atlas predicates and their étale locality theorem.

All already recorded proof-dependency modules are imported. Proof dependencies without a recorded module are left for stage 3: `lem-trf-zariski-etale-tensor-sections`, `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, `lem-trf-space-etale-module-pushforward-restriction`, and `lem-pc-separated-quasi-separated`. Their interfaces are not assumed as extra theorem hypotheses. The main proof docstring records all ten proof steps and their use. The existing flat-base-change record only exposes a cohomology finrank theorem; stage 3 will require its full canonical degree-zero comparison interface, not merely that numerical consequence.

The slice sheafification helpers are needed because the scheme's small étale site has objects in `u+1` and morphisms in `u`, whereas the dependency's tensor-section sheaf has section groups in `u`. They state the usual additive sheafification and locally-bijective criterion using the affine étale basis, rather than changing either section universe or site. Their full construction arguments are in their docstrings. No universe equality or size hypothesis is added to the node.

Edge cases checked before drafting: the empty scheme and empty open subscheme (the empty cover forces the zero section module); the zero module, including the fact it is a line module only on an empty ringed scheme; arbitrary, not necessarily affine schemes; arbitrary module sizes within the fixed universe and arbitrary small presentation index sets; identity morphisms; open immersions; non-étale arbitrary pullback maps; and quasi-compact separated morphisms that are not finite type or proper. No condition excludes any of these. The morphism comparison is stated before the quasi-compact/separated block, so it covers every scheme morphism.

Searches for an existing statement (2026-10-17 UTC):

- `msearch.py`, LeanFinder: "Quasi coherent Zariski modules and small etale modules are equivalent compatibly with pullback and direct image". Eight hits, primarily the general quasi-coherence predicate and scheme module pseudofunctor; none states the equivalence.
- `msearch.py`, Loogle: `"IsQuasicoherent", "Equivalence"`. Zero hits.
- `msearch.py`, grep in Mathlib/AlgebraicGeometry: `etale.*[Qq]uasi|[Qq]uasi.*etale`. Four unrelated étale/quasi-finite or flat descent hits; no comparison theorem.
- `msearch.py`, LeanSearch: "Quasi coherent modules on a scheme and on its small etale site are equivalent categories". Eight hits for the quasi-coherence infrastructure, site congruence, and small étale topology; none states this theorem.
- Ripgrep of upstream WeilConjectures for `zariskiEtale|ZariskiEtale|etaleTensor|etale.*[Mm]odule`, and the exact item id. The id is absent; the results include existing étale Hom and structure-sheaf constructions, which are reused, but no equivalence of quasi-coherent module categories.
- Ripgrep of `lean/Sheaf`, DAG declarations and upstream names for scheme/Zariski/étale quasi-coherent equivalence found only cohomology comparisons and existing tensor-section infrastructure. These are distinct from this categorical theorem. `tools/blueprint_refs.py search 'etale structure sheaf'` found no blueprint node with that phrase. The regular-function ring sheaf is a helper of this ringed-site comparison, using the existing presheaf rather than a new independent construction.

A final search for open-site inclusions found the already recorded `AlgebraicGeometry.gabberOpenEtale` and `gabberPreimageEtaleIso` in `Sheaf.AlgebraicGeometry.GabberH0ZariskiConstructions` (node `def-weil-pbc-gabber-h0-zariski-constructions`). Their full definitions were read and are reused directly; this module does not redefine either construction.

No statement correction and no disputed mathematical assertion. No new DAG nodes or dependency-record repairs are needed. The ring sheaf, section-preserving sheafification interfaces and canonical maps are helpers of the owning comparison node, all listed in `lean.declarations` with its blueprint/source docstrings.

Validation: the final module, including reuse of the published open-site constructions, passed `scompile.py Q131 lem-trf-scheme-zariski-etale-quasi-coherent-equivalence <module>` (exit 0) in both the sandbox check and actual module-path check, with no errors or unexpected warnings. The mandatory delivery dry run is performed with `deliver2.py ... --no-push` before the final push. No global build or direct edits to either read-only checkout were run.

## Second reading by Q131

Independent maintainer second reading on 2026-10-18 of immutable delivery
`d0fa352ba5cb06280b5a8f34d4ec9787ab465b7b`. This replaces the worker placeholder;
the worker report above is preserved.


Read `literature/stacks-project/descent.tex` in the Q131 source clone:
070S lemma-compare-sites (around 2294–2365), 03FH
remark-change-topologies-ringed-sites (2370–2396), 0GN7
lemma-fully-faithful-associated (2459–2495), 03DX
proposition-equivalence-quasi-coherent (2499–2607), 05VG
lemma-equivalence-quasi-coherent-properties (2613–2670), and 03LC
proposition-equivalence-quasi-coherent-functorial (2892–2955).
Also read sites-modules.tex definition-site-local (2941, clause 6),
definition-invertible-sheaf (5675), lemma-invertible-is-locally-free-rank-1
(7635), and spaces-properties.tex definition-structure-sheaf (3768) and
definition-quasi-coherent (5223). The scheme specialization is expressly
compatible with the existing scheme structure sheaf in that source.

1. **Objects and assumptions:** `T : Scheme.{u}` is an arbitrary scheme.
   `F : T.Modules` and `[F.IsQuasicoherent]` are ordinary Zariski modules;
   `SmallEtaleModules T` is SheafOfModules over the explicit regular-function
   ring sheaf on the actual small étale site. No field, characteristic,
   Noetherian, nonempty, finite-type, or separation assumption is added here.
2. **Associated sheaf:** the family `e` identifies the underlying additive
   extension sheaf with the recorded `etaleTensorSectionsSheaf F`.
   Its scalar equation supplies the module action; its module-map equation
   supplies naturality. This is an isomorphism of sheaves, so it already
   respects all site restriction maps, not only objectwise section groups.
3. **Forward functor:** `zariskiEtaleOpenRingMap` is the actual open-subscheme
   function map, from `restrictFunctorΓ.inv`. Module extension is the
   Mathlib pullback left adjoint for precisely that map. Read
   Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean: pullback
   is selected by its adjunction, and pullbackIso describes its presheaf
   pullback followed by sheafification. This is the requested ringed-site
   tensor pullback. Selection by this universal property is permitted;
   it does not choose an arbitrary functor from a bare Nonempty assertion.
4. **Equivalence and inverse:** the first two blocks assert preservation of
   quasi-coherence by extension and restriction and invertibility of their
   actual adjunction unit and counit. These give exactly the adjoint
   equivalence on the full quasi-coherent subcategories with the specified
   inverse. `ZariskiEtaleModuleContext` contains only continuity and
   right-adjoint-existence proofs; its existence is concluded, not assumed.
5. **Open-section normalization:** the unit equation composes with `e` and
   `tensorOpenSectionIso` to give identity on F(W). The counit equation
   reverses these coordinates and gives identity on G(W -> T). Its proof
   argument h is supplied by the preceding preservation assertion, so
   does not impose a new hypothesis.
6. **Lines:** the first local-unit condition is equivalent to the recorded
   IsLineModule formula on the scheme site (covering sieves and restrictions
   to all slice sites). The next block includes every line module G without
   assuming it quasi-coherent first, concluding quasi-coherence and
   invertibility of its restriction. Thus both directions of the line
   equivalence are present. The use of Nonempty here is the existence of a
   local trivialization, which is precisely the mathematical predicate.
7. **Arbitrary morphism pullback:** for every a : U -> T the theorem supplies
   hp and the direct-image restriction isomorphism r. The section equation
   fixes r to the actual gabberPreimageEtaleIso map. The definition
   zariskiEtalePullbackComparison takes the unique left-adjoint mate of
   that fixed r. It is a natural isomorphism for all modules and hence on
   quasi-coherent modules, and is available before any qc/separated premise.
   Read the current TensorPullbackAdjunction through scompile.py --source:
   exists_tensorPullbackAdjunction specifies the unit as sheafified 1 tensor m.
   Classical.choose here therefore retains the canonical unit normalization.
8. **Direct images:** only the final block assumes QuasiCompact a and
   IsSeparated a, as the item does. Stacks 03LC(3) holds for qc quasi-separated
   maps; the item's separated specialization is legitimate. Both direct
   images are asserted quasi-coherent. zariskiEtalePushforwardComparison is
   explicit: étale unit, inverse pullback comparison, ordinary counit. The
   last two clauses give naturality and compatibility with the extension
   units under r, which, using the earlier open-section identities, is the
   requested identity on sections over a^{-1}W.

## Dependency and construction audit

All snapshot statement dependencies were read and their used declarations opened:

- def-pc-scheme: Mathlib Scheme and Scheme.Hom, ordinary locally ringed schemes.
- def-sc-etale-qcoherent-module: EtaleTensorSectionsSheaf and its actual
  EtaleTensorSections restrictions; descent does not replace the section groups.
- pqf-def-coherent: the module uses Mathlib IsQuasicoherent, not the finite-type
  conjunction in the inherited CoherentFiniteType record. Its finite-type and
  coherence clauses are not assumptions of this item. No inherited record is
  redefined or repointed by this delivery.
- def-pur-sheaf-tensor-product: SiteTensorFunctoriality and its publicly retained
  TensorProductOfUniverses construction use genuine sectionwise tensors and
  sheafification. The comparison uses the canonical module pullback API.
- def-trf-space-quasi-coherent-module: Mathlib QuasicoherentData and
  IsQuasicoherent (Quasicoherent.lean 202–261) use local arbitrary free
  presentations, not finite presentation or finite type.
- def-sc-invertible-module: Scheme.Modules.IsInvertible (Invertible.lean 57ff)
  is Zariski locally the unit module; no tensor-invertibility predicate on
  an unrelated category is substituted.
- def-trf-algebraic-space: AlgebraicSpace.IsLineModule (AlgebraicSpace.lean 195ff)
  is exactly the covering-sieve local-unit condition used here on scheme sites.
- def-pc-module-pullback: read the recorded TensorPullbackSectionAdjunction
  and the existing explicit tensor pullback/normalized adjunction used by the
  module. They concern the same tensor functor; no private pullback is defined.
- lem-trf-space-qc-separated-etale-local: read the scheme-test diagonal and
  quasi-compact-atlas predicates and locality theorem. This item specializes
  the usual meanings to scheme QuasiCompact and IsSeparated.

The original structure presheaf and structural pullback of functions were read
in WeilConjectures/AlgebraicGeometry/Sites/Gm.lean (90–99, 170ff).
The open inclusion and preimage comparison were read in
GabberH0ZariskiConstructions.lean (30ff, 75ff). These are reused, not copied.
The helper definitions contain explicit presheaves, ring maps, pushforwards,
adjunctions, and mates. All four theorem proofs in the delivered file are
exactly `by sorry`; no local proof is smuggled into a definition.

The two slice sheafification helpers retain AddCommGrpCat.{u} on the
u+1-object/u-morphism site. Their affine-basis argument is a real size-preserving
construction route; Mathlib AffineEtale.lean 90–125 already supplies the
corresponding essentially-small affine basis and sheafification on the
unlocalized scheme site. The slice assertions are not extra hypotheses or
silent identifications of site universes. They belong to this module's site
interface and are listed in lean.declarations with source/blueprint and proof
docstrings. No missing independent notion is hidden by an arbitrary map, and
no genuine unstated prerequisite is required merely to type this statement.
Unproved proof dependencies remain stage-3 obligations, not hollow data.

The ten-step main docstring follows the recorded proof: tensor sections and
adjunction; étale restriction; affine free presentations; unit/full faithfulness;
local cokernels; overlap cocycles and fpqc descent; gluing and counit; adjoint
mates; rank-one descent; qc separated pushforward and flat base change. The
worker's warning that the flat-base-change numerical interface will require
its full degree-zero interface at proof time is not an extra assumption here.

## Searches, universes, edge cases and mechanical checks

Independent ripgrep searches of Mathlib, upstream WeilConjectures, and the Q131
side sources for Zariski/étale comparisons, smallEtale module rings and
sheafification found cohomology comparisons and the reused structure/inclusion
APIs, but no existing statement of this module's full equivalence. Loogle query
`"IsQuasicoherent", "Equivalence"` returned zero hits. LeanSearch query
`Equivalence of quasi coherent modules on Zariski and small etale sites of a scheme`
returned eight infrastructure hits (IsQuasicoherent, QuasicoherentData, small
étale topology), none this theorem. No duplicate notion or exact theorem was found.

Checked empty scheme and empty opens, zero modules, empty presentation indices,
non-finitely-generated quasi-coherent modules, identity maps, open immersions,
arbitrary non-étale scheme morphisms, and qc separated maps without finite type
or properness. Empty-site local-unit assertions are correctly vacuous; the zero
module is a line only on the empty scheme. The fixed universe u is arbitrary
and the site object universe remains u+1; there is no unbound implicit variable
(autoImplicit is false), universe equality, or independent smaller test universe.

The lean.statement field is byte-for-byte equal to the main signature from
`theorem` through the text immediately preceding `:= by`. All 21 listed
helper/main declarations are present. Lines are at most 100 characters; imports
use approved namespaces. Source-place/blueprint module and declaration docstrings
are present. There is no statement correction, so no §1(C) citer audit is due.
The current dropped-route list was read through read-only git show; its
intersection with all direct statement/proof dependencies is empty. No route-pivot
repair note exists for this item at origin/newtargets-dag. No infinity/dg/model
machinery or pro-étale substitute is introduced.

## Compiler evidence and final checks

Reproduced the worker's recorded per-file compile with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q131 \
  lem-trf-scheme-zariski-etale-quasi-coherent-equivalence \
  snapshot/lean/Sheaf/AlgebraicGeometry/SchemeZariskiEtaleQuasiCoherentEquivalence.lean
```

Exit code 0. The installed wrapper currently runs the isolated server overlay
rather than a local compiler. It reported sandbox Sheaf/Stage2/Sandbox0.lean
(38.5 s) and library
Sheaf/AlgebraicGeometry/SchemeZariskiEtaleQuasiCoherentEquivalence.lean (105.5 s),
with no Lean errors or warning diagnostics. These are wrapper timings; the wrapper
announced its unchanged 60 s per-Lean-invocation limit. No limit was raised.
The clean library-path confirmation reproduces the worker's claim. There is one
delivered Lean module; no additional module needs compilation. A report-only fix
requires no further compiler run.

Final findings: only the H11/H1 placeholder, completely repaired by the supplied
replacement report. No mathematical, canonical-map, universe, hollow-definition,
statement-verbatim, source, or edge-case defect found. No global build, live Lean
write, direct ssh invocation, merge, delivery, claim, or Git mutation was performed.
