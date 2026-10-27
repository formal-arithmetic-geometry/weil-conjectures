## Worker report

The module `Sheaf.AlgebraicGeometry.BigFppfZariskiRingedComparison` states
`AlgebraicGeometry.Scheme.bigFppfZariskiRingedComparison`, with its sole proof
`sorry`. No statement correction is made. The dependency module gives the same
ringed-topos data with independent site universes. There are no new DAG nodes.

Read the node, its ten proof steps, every statement dependency and its recorded
Lean signature/docstring, and Stacks `descent.tex`,
`remark-change-topologies-ringed` (070R) and `lemma-compare-sites` (070S), especially
part (1) and its proof. The source covers all modules and sheafifies the section
presheaf; it does not assert that this presheaf is already fppf sheaf-valued.

Clause-by-clause correspondence:

- The scheme is the arbitrary binder `S : Scheme.{u}`. No finiteness, separation,
  nonemptiness, flatness or quasi-coherence hypothesis is imposed on S or M.
- The small Zariski site is `Opens.grothendieckTopology S`; the big fppf site is
  `Scheme.fppfTopology.over S` on `Over S`. The actual open-inclusion functor is
  the existing `S.restrictFunctor`, with objects `Over.mk W.ι`.
- The universe convention uses explicit universe u: scheme and slice objects
  live in u+1, arrows in u, section rings and modules in u. These universes are
  retained rather than identifying the object and Hom universes. The two
  forgetting instances, additive sheafification, local-equivalence instance,
  and continuity are existential conclusions, not hypotheses.
- The structure sheaf is `O`, with the natural ring-presheaf isomorphism
  `o : O.obj ≅ (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat`.
  Thus every object is exactly its ring of regular functions, and every ring
  restriction is pullback of functions under the displayed identification.
  This is a fully specified realization of the stated ring sheaf, not a new
  ring notion or a choice from an uncharacterized existence theorem.
- `φ` is the ring map from `S.ringCatSheaf` to restriction of O. The first
  conjunct fixes its component by `o(φ_W(a)) = W.topIso.inv a`. Hence φ is the
  identity on regular functions after the usual open-subscheme identification.
- `p : RingedToposMorphismOnSites O S.ringCatSheaf` gives the geometric adjunction,
  finite-limit preservation and all ring identities, together with induced
  additive module direct image. `d` identifies its set direct image with actual
  restriction, and `p.modules = SheafOfModules.pushforward φ` identifies its
  module direct image with actual restriction, including scalar restriction.
- The equation using `p.adj.homEquiv ... p.ringMap`, followed by `d.hom`, is exactly
  that its structural map is adjoint to the identity ring comparison φ. It
  ties the geometric and module constructions to the specified structural map.
- `SheafOfModules.pullback φ` is the existing canonical inverse image for the
  continuous ringed-site morphism. Its right-adjoint witness is an existential
  conclusion. This is the ringed tensor pullback: the Mathlib continuous module
  pullback construction and the imported ringed-topoi module-adjunction theorem
  identify it with extension of scalars of geometric inverse image. No arbitrary
  map or an additional adjunction hypothesis replaces that pullback. Its actual
  chosen adjunction is `SheafOfModules.pullbackPushforwardAdjunction φ`.
- `P : S.Modules ⥤ PresheafOfModules O.obj` and the additive equivalences `s M U`
  identify its values with `Γ((Modules.tensorPullback U.hom).obj M, ⊤)` for EVERY
  Zariski module. The scalar conjunct transports the O-action through o to the
  usual action on these pullback sections. The `@id Γ(U.left, ⊤)` only supplies
  Lean's expected type; it changes no scalar.
- The restriction conjunct, quantified over every `h : U' ⟶ U`, gives pullback
  by the normalized scheme unit, restriction from the inverse image of top to
  top, the inverse of `tensorPullbackSectionComp`, and transport by `h.w`.
  This is precisely pullback of sections followed by h^*u^* ≅ (uh)^*.
  Functoriality and semilinearity are carried by the actual `PresheafOfModules`.
- For each `v : M ⟶ N`, the next conjunct identifies `(P.map v).app (op U)` with
  `((Modules.tensorPullback U.hom).map v).app ⊤`. Thus P is the specified functor
  on all module maps, not just an objectwise realization.
- `e : SheafOfModules.pullback φ ≅ P ⋙ PresheafOfModules.sheafification (𝟙 O.obj)`
  is a natural isomorphism of actual module-sheaf functors. Its components
  therefore commute with every big-site restriction and scalar action, and
  naturality identifies pullback of v with sheafification of P_v.
- The last equation evaluates the actual pullback-adjunction unit on W, then
  `e.hom`, and identifies it with `toSheafify` of the section in P at W. The
  section is obtained from x using the normalized unit for W.ι and restriction
  from W.ι^{-1}W to top. This is the canonical open-pullback identification
  M(W) ≅ Γ(W,j^*M), not an independently chosen additive equivalence. Through s
  this is exactly q_M(j) after P_M(j)=M(W). It is the full unit equation on all
  opens, and fixes the canonical comparison of left adjoints.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies `.over S`.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphismOnSites`, the §1(B) extension below, recorded alongside
  `CategoryTheory.RingedToposMorphism` in its original owning module.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the Mathlib `SheafOfModules` category used throughout.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  tensor interface, publicly retaining the ordinary tensor/change-of-rings
  constructions. The general ringed-site pullback is Mathlib's
  `SheafOfModules.pullback` from `Sheaf.PullbackContinuous` (not Mathlib's
  scheme-module pullback).
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, its adjunction, and `toSheafify`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionAdjunction`, and
  `tensorPullbackSectionComp`. These are the recorded tensor formula and its
  uniquely section-normalized adjunction, not a second pullback construction.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.restrictFunctor`, `Opens.topIso`.

Every stated proof-dependency module is imported without `public`; Mathlib
leaves (tilde/free modules, fppf/fpqc and Zariski/fppf coverage inclusion, open
pullback squares, composite adjunction, conjugate-unit equation, associativity
of left-adjoint composition) are supplied by their existing Mathlib imports.
The proof docstring carries all ten steps with the same argument as the node.
No import of the downstream quasi-coherent equivalence is made: that module
mentions this item as a proof dependency. Its existing `sfbFppfRings`,
`sfbSectionPullback` and `sfbOpenSection` are not redefined; their concrete
formulas occur directly in the theorem instead. This avoids an import cycle
when the maintainer adds the proof-dependency import there.

Edge cases checked before writing: S empty; the empty open W; the zero module;
identity and composite big-site arrows; the identity scheme map; non-affine
schemes and overlaps; and non-quasi-coherent modules. The statement has no
quasi-coherence binder, asserts only sheafification of P, and uses the full
category of all modules. Units and canonical composition include identity and
empty-open cases. No index set, degree or nonzero ring condition is introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: “The tensor inverse image from Zariski modules to
  the big fppf site is the sheafification of pullback sections”. Eight hits,
  including `SheafOfModules.sheafificationCompPullback`, `pullbackIso`, `pullback`,
  and the continuous pullback adjunction. These are general site constructions;
  none identifies the section presheaf on the scheme big fppf site.
- `msearch.py ... loogle '"SheafOfModules", "pullback"'`: twelve hits, principally
  presheaf pullback and its identity/composition API. No exact comparison.
- `msearch.py ... grep 'fppf.*[Zz]ariski|[Zz]ariski.*fppf|sheafificationCompPullback'`:
  four hits: Zariski/fppf precoverage inclusion and the general module comparison.
- `msearch.py ... leansearch`: “ringed topos geometric morphism module direct
  image independent universes”. Eight hits, including module sheaves, scheme
  modules, and pullback of free modules; no generic ringed-topos structure.
- `rg` in project Sheaf and WeilConjectures for the item id and
  `bigFppf|big_fppf|fppf.*[Zz]ariski|[Zz]ariski.*fppf`: no existing declaration
  states this arbitrary-module theorem. The downstream
  `SchemeBigFppfQuasicoherentEquivalence` covers only quasi-coherent modules.
- `rg` for ringed structure declarations found the original equal-universe
  record and the landed `RingedToposMorphismOfUniverses`; their full signatures
  were read. The latter requires `EssentiallySmall.{r}` of each site, so is
  unavailable for the native scheme site with section rings in u. Neither
  provides the repaired interface needed here.
- Searched `dag/lean_names_upstream.json` and the project source for duplicate
  theorem/structure names; the new full names have no previous declaration.

Compilation: both files separately, in dependency order, with the prescribed
`scompile.py` wrapper, including their library paths. The dependency compiled
in 5.5 s and the theorem in 2.4–2.5 s after the superset repair. No errors or non-sorry warnings remain.

## Dependency modules

`def-weil-pbc-ringed-topos-morphism`: the old record requires C and D to have
object and Hom universe u, the same as the ring sections. `Over S` instead has
objects in u+1 and morphisms in u. The already landed
`RingedToposMorphismOfUniverses` still requires `EssentiallySmall.{u} (Over S)`
when rings and modules are u-small, which is unavailable for all u-small
schemes. Requiring that instance would exclude the stated big site.

`Sheaf.CategoryTheory.RingedToposMorphism` retains its original definition
verbatim and appends `RingedToposMorphismOnSites`, which supplies the same definition
with independent object/Hom universes and explicitly supplied ambient
`HasSheafCompose` instances for the underlying-set functors. It retains every
field: set inverse/direct images, adjunction, finite-limit preservation, ring
map and four generalized-element ring identities, additive module direct
image, its underlying-set comparison, and the scalar/addition transpose
identity. No theorem is asserted and no definition data are postponed. Site
smallness is not needed merely to specify this geometric-adjunction data. The
item proves the needed forgetting instances existentially. The original
module, file, primary declaration, and recorded statement are retained. The `declarations` list owns BOTH `CategoryTheory.RingedToposMorphism`
and `CategoryTheory.RingedToposMorphismOnSites`. No original declaration is
edited; the extra structure is appended verbatim. The dependency node is
changed only in `lean`, with the required explanatory note.

## Second reading by N0

A separate rereading of the node and both complete modules checked the binders
and conclusions in the order above. In particular, the rereading checked that
P is a functor on ALL modules, that the arrow equation uses h.left followed by
the inverse composition comparison and the Over commuting equation, and that
P_v uses the recorded tensor pullback's map. It checked the first φ equation
and the geometric-adjoint structural equation together: both are required to
specify the ringed morphism. It checked that e is a natural isomorphism of
module sheaves rather than objectwise additive bijections, and that its unit
equation is on every open, including the empty open. The native site universe
mismatch was repaired in the dependency interface, with all original fields
retained. Compiler errors found in this pass were namespace shadowing of
`forget`/`PresheafOfModules` and missing expected scalar type; those were fixed
by full names and the explicit identity type cast. No change to the node's
mathematical statement or omission of a clause was needed. The independent
maintainer review will read the actual delivery.

## Returned delivery repair (1016faa1c72f, H13 with H4/H9 consequences)

Implemented the maintainer's preferred superset correction. The original
`lean/Sheaf/CategoryTheory/RingedToposMorphism.lean` is a byte-for-byte prefix
of the delivered module: both its structure and additive instance remain
unchanged. The independent-universe structure and its additive instance are
appended unchanged from the returned delivery, under their original names.
The separate `RingedToposMorphismOnSites.lean` file is removed from the packet;
the item publicly imports `Sheaf.CategoryTheory.RingedToposMorphism` instead.
The dependency record retains the live `module`, `file`, primary `declaration`
and `statement`, adds a two-entry `declarations` list, and explains the
§1(B) extension. This preserves ownership of the established declaration and
module as requested, including all existing consumers.

Compared the original module with current server source using the prescribed
`scompile.py --source Sheaf.CategoryTheory.RingedToposMorphism`; it matches
the read clone. The item's signature and all mathematical clauses match the
returned version; only its import changes. The repaired node files retain
the current main branch's non-Lean fields. Delivery wrappers rebase the packet
on current main. The second reading for this repair compared both complete
structures field by field, checked that the old module is an exact prefix,
and verified that the new structure suffix is identical to the returned one.
Both declarations are explicitly listed under the original owning node.

Validation of the repaired delivery: both modules compiled cleanly separately
in dependency order with `scompile.py` (5.5 s for the extended original module,
2.4–2.5 s for the item). No non-sorry warnings. The required dry run is run
before push.
