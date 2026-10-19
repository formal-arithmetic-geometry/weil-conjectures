## Worker report

The module `Sheaf.Paper.ProEtaleLocallyConstantSheaf` defines the constant module
presheaf and its sheafification, the corresponding construction on a localized
ringed site, global constancy, and local constancy. The main declaration is
`AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheaf`.

Source read: Bhatt--Scholze, The pro-etale topology for schemes, Definition
7.3.1(1), including the preceding paragraph. That paragraph fixes a locally
topologically noetherian scheme for that section; the definition itself makes
sense on arbitrary schemes. The module follows the item's explicit arbitrary
scheme convention and the blueprint's final sentence in
`sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/def-weil-scheme-morphism-properties.md`,
which was also read and defines constancy after a pro-etale covering family.
No conclusion from the later noetherian-dependent theory is asserted here.

Clause-by-clause correspondence:

* The scheme is `Y : Scheme.{t}`; the commutative ring is `A : Type t` with
  `[CommRing A]`. The site is exactly `Y.ProEt`, with topology
  `ProEt.topology Y`. The terminal object is `ProEt.mk (𝟙 Y)`.
* The coefficient sheaf is `(constantSheaf (ProEt.topology Y)
  CommRingCat.{t + 1}).obj (CommRingCat.of (ULift.{t + 1, t} A))`, followed
  by `sheafCompose` with `forget₂ CommRingCat RingCat`. This is precisely
  the coefficient ring in the dependency's `proEtaleDerivedCategory`.
  No alternative ring sheaf or module category is substituted.
* A module is bundled as `M : ModuleCat.{t + 1} (ULift.{t + 1, t} A)`.
  ULift changes only the carrier universe; A-module structures correspond
  to these structures by the canonical ring equivalence. This permits all
  modules in the site's larger value universe, including infinite modules.
* `proEtaleConstantModulePresheaf` has `obj _ := M` and `map _ := 𝟙 M`.
  Its coefficient presheaf is the constant commutative ring presheaf followed
  by forgetting commutativity. Thus its action is exactly A's original action.
* `proEtaleConstantModuleSheaf` applies Mathlib's
  `PresheafOfModules.sheafification` to this presheaf along the ring
  sheafification unit. That functor sheafifies the underlying abelian presheaf
  and equips it with the sheafified scalar action: a locally represented pair
  a,m acts by the section represented by a•m. The module's construction does
  not merely assert that some compatible action exists.
* `IsConstantProEtaleModuleSheaf` is
  `∃ M, Nonempty (F ≅ proEtaleConstantModuleSheaf Y A M)`; the isomorphism
  lives in `SheafOfModules`, so it preserves the coefficient action.
* The local predicate quantifies over `I : Type (t + 1)`, `U : I → Y.ProEt`,
  and arrows `f : ∀ i, U i ⟶ ProEt.mk (𝟙 Y)`. The condition
  `Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _` uses the
  actual small pro-etale precoverage, defined by comapping the scheme
  pro-etale precoverage. Thus it requires an fpqc/pro-etale covering family,
  rather than only a jointly surjective family or an arbitrary sieve.
* For every i, a separate existential `M` and a `Nonempty` module-sheaf
  isomorphism identify `F.over (U i)` with
  `proEtaleConstantModuleSheafOver Y A (U i) M`. The modules can vary with i.
* Restriction is precisely Mathlib's `SheafOfModules.over`. The localized
  constant construction uses `Over U`, the localized topology, and the ring
  `A_Y.over U`. Its sheafification unit is the original unit whiskered by
  `(Over.forget U).op`. Its module presheaf again has identity restrictions.
  This constructs the constant module on the localized ringed site itself;
  no identification with the small pro-etale site of the scheme U is assumed.
* There are no finiteness, noetherianity, nonempty-family, nonzero-ring,
  finite-generation, freeness, or finite-rank assumptions.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`: its full body fixes the
  larger value universe and constant commutative ring followed by forgetting.
  Imported as required; the present statement uses its same underlying site
  and coefficient sheaf, not the derived category.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`: sheafification of `Functor.const`.
* `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction`: the sheafification adjunction and its unit.
* `Mathlib.AlgebraicGeometry.Modules.Sheaf`,
  `AlgebraicGeometry.Scheme.Modules`: this dependency record also points to
  the general `SheafOfModules` carrier, which is the correct specialization
  here. Read `SheafOfModules` in `Mathlib.Algebra.Category.ModuleCat.Sheaf`.
  Its objects are module presheaves with sheaf underlying abelian presheaves;
  its morphisms are linear presheaf maps. No dependency repair is necessary.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor` and `SheafOfModules.over`, plus
  `CategoryTheory.Sheaf.over` and `GrothendieckTopology.over` from
  `Mathlib.CategoryTheory.Sites.Over`: the localized ring and module sheaves.
  This dependency is a Mathlib leaf with no lean record, as allowed.
* The construction uses `PresheafOfModules.sheafification` from
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`. Its full
  signature and docstring, and the underlying `sheafify` construction's
  description in `Presheaf.Sheafify`, were read.

Two named theorem obligations have `sorry` proofs:
`proEtaleConstantRingUnit_locallyBijective` and
`proEtaleConstantRingUnit_over_locallyBijective`. Each has a source and
natural-language proof in its docstring and is attached to this definition
node in `lean.declarations`. They supply proof-only instances required by
Mathlib's actual sheafification construction. Neither chooses data, a module
action, a sheaf, or an isomorphism from an unproved existence theorem.
Every definition's data is given in full. Nothing was proved at stage 2.

Edge cases checked by reading the constructors and quantifiers: the zero ring
and zero module are allowed; arbitrary infinite modules are allowed; an empty
index type is allowed exactly when its empty presieve really covers the base
(as on the empty scheme); no point or geometric stalk is needed. Empty schemes
and empty cover members do not require nonempty instances. The site lives in
Type (t+1) with morphisms in Type t, its cover index and value modules in the
larger universe. All universe variables and binders are explicit.

Searches made using `msearch.py` (stored in searches.jsonl):

* LeanFinder: “A sheaf of modules on the small pro etale site is locally
  constant if a covering family makes it isomorphic to constant module
  sheaves”: eight hits, principally `Sheaf.IsConstant` and related lemmas
  and condensed locally constant functors. None supplies this ringed-site
  cover-local module predicate.
* Loogle: `CategoryTheory.Sheaf.IsConstant`: twelve hits for ordinary
  category-valued sheaves, global constancy and its preservation. They do
  not construct a module over the sheafified varying coefficient ring.
* LeanSearch: “locally constant sheaf of modules on a Grothendieck site”:
  unavailable, service returned Internal Server Error. No verdict is inferred.
* Mathlib grep: `LocallyConstant.*Sheaf|Sheaf.*LocallyConstant|IsLocallyTrivial`:
  eleven hits in condensed discrete sheaf files, on different sites.
* Direct rg in the upstream project and this project's `lean/Sheaf` for
  constant-module and locally-constant notions found etale-site and condensed
  constructions, including fixed-ring ModuleCat sheaves, not this predicate.
  `rg` for the item's id in upstream found no declaration. Exact candidate
  names were checked in Mathlib, upstream, `dag/lean_names_upstream.json`,
  and this project's Lean, with no collision.
* Mathlib's module-presheaf sources were searched for constant module
  constructors. The existing `PresheafOfModules.sheafification` supplies
  precisely the simultaneous ring/module sheafification and is reused.

No node faults or statement corrections were needed. No new nodes and no
unusable dependency modules were needed: every helper is a construction or
proof obligation explicitly belonging to this node's multi-clause definition.
The source was compiled cleanly using only `scompile.py`, on the server with
nice 19, two threads, and the default 60-second per-file limit.

## Second reading by NB

I independently read the node, every statement dependency's current record,
the declarations below, and the source context before accepting the Lean.
The node has no statement_change; no new nodes or dependency modules are
part of this delivery.

Object, hypothesis and conclusion checklist (each verdict: matches):

1. An arbitrary scheme Y and commutative ring A: `Y : Scheme.{t}` and
   `A : Type t`, `[CommRing A]`. No other geometric or algebraic instance
   is assumed. The small site is `Y.ProEt`, with `ProEt.topology Y`.
   I read the full `proEtaleDerivedCategory` definition in the dependency
   module and Mathlib's `ProEt`, `precoverage`, and `topology`. Its objects
   are weakly etale maps, not just etale maps or inverse systems of etale maps.
2. The constant coefficient ring A_Y: the displayed `constantSheaf` into
   `CommRingCat.{t + 1}`, evaluated at `CommRingCat.of (ULift A)`, followed
   by `sheafCompose` with `forget₂ CommRingCat RingCat`. This is verbatim
   the coefficient-ring term in `proEtaleDerivedCategory`. `ULift` transports
   A by a ring equivalence; it imposes no condition on A.
3. An A_Y-module sheaf F and its module-linear isomorphisms:
   `F : SheafOfModules.{t + 1} (...)` and `Nonempty (F ≅ ...)`.
   The current dependency is `CategoryTheory.ringedSiteModules`, whose full
   body is precisely `SheafOfModules R`. I opened this abbreviation and
   Mathlib's `SheafOfModules`, `Hom`, and underlying module-presheaf maps:
   this is the dependency's exact category, with sectionwise linear maps.
4. An arbitrary A-module M: `M : ModuleCat.{t + 1} (ULift A)`.
   `proEtaleConstantModulePresheaf` has `obj _ := M`, `map _ := 𝟙 M`.
   The scalar ring is the constant presheaf with value `ULift A`; the action
   is M's original action, rather than an independently chosen action.
5. Its constant module sheaf: `proEtaleConstantModuleSheaf` applies
   `PresheafOfModules.sheafification` along the ring sheafification unit.
   I read that functor's full definition and `Presheaf.Sheafify`'s construction:
   its underlying abelian sheaf is the sheafification, and its scalar action
   is determined locally by the original scalar products. This realizes
   the node's locally represented a,m mapping to am, including relations
   in M. It is not a free-module replacement.
6. Global constancy: `IsConstantProEtaleModuleSheaf` is exactly
   `∃ M, Nonempty (F ≅ proEtaleConstantModuleSheaf Y A M)`.
   The existential does not require a finite or free M.
7. A covering family over Y: `∃ (I : Type (t + 1)) (U : I → Y.ProEt)`
   and `f : ∀ i, U i ⟶ ProEt.mk (𝟙 Y)`, with
   `Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _`.
   I checked the precoverage's comap from scheme pro-etale covers. This
   expresses actual pro-etale/fpqc coverings of the terminal object,
   rather than just joint surjectivity or arbitrary morphisms.
8. Each member has its own module and trivialization: the following
   `∀ i, ∃ M, Nonempty (...)` retains the quantifier order, permits varying
   modules, and compares `F.over (U i)` with
   `proEtaleConstantModuleSheafOver Y A (U i) M` by a module-sheaf isomorphism.
9. Localized ringed-site restriction and localized constant sheaf:
   Mathlib's `SheafOfModules.over` uses `Over U`, the topology `J.over U`,
   and coefficient sheaf `R.over U`. I read `overFunctor`, `over`,
   `Sheaf.over`, and `GrothendieckTopology.over`. Whiskering the ring unit
   with `(Over.forget U).op` and sheafifying the constant module presheaf
   on `Over U` gives exactly the second construction specified by the node.
   No equivalence with the small site of the underlying scheme is assumed.
10. No finiteness clause: none of A, M, I, or Y is required finite,
    noetherian, connected, or nonempty. There is no hidden freeness or
    finite-presentation hypothesis.

Source comparison: I read Bhatt--Scholze Definition 7.3.1(1) with the
opening of Section 7.3, and the blueprint's
`def-weil-scheme-morphism-properties`. The former section works with locally
topologically noetherian X and set sheaves. The node explicitly gives the
blueprint's module version for arbitrary schemes; cover-local constancy
itself needs neither that noetherian assumption nor the later consequences
of Section 7.3. I also read Stacks `sites.tex`, Example
`example-constant-sheaf` and Definition `definition-localize`, and
`sites-modules.tex`, Definitions `definition-sheaf-modules` and
`definition-localize-ringed-site`. They confirm the exact sheafification,
module and restriction constructions used here.

Edge cases: I may be empty, with the genuine covering condition retained;
there is no `Nonempty I`. In particular the empty scheme and empty cover
members are allowed. A may be the zero ring, M the zero module or any
infinite module; no nontriviality instance or finite-rank assumption appears.
There is no integer n or characteristic restriction. The value and index
universe is t+1, the site-object universe, while schemes and A lie in t,
exactly as the site dependency requires. Larger carriers can be accommodated
by increasing t; all universe variables are explicitly declared. The generic
presheaf constructor explicitly binds its category and hom universes too.

Independent searches, with different phrasing from the worker:

* LeanFinder via msearch: "A module sheaf is trivial on slice sites over a
  covering family with arbitrary discrete module fibers". Eight hits,
  including `SheafOfModules.unit`, `free`, `Sheaf.IsConstant`, and the
  module sheafification scalar-action implementation; none gives this
  localized pro-etale module predicate. The existing sheafification
  construction is already reused.
* Loogle via msearch: `SheafOfModules.over`. Twelve hits, including
  `over`, `Hom.over`, and local generators. These provide restriction
  and generating sections, not constancy. Restriction is reused here.
* Mathlib grep via msearch: `locallyTrivial|LocallyConstantSheaf|constantModule`.
  Five hits, all condensed discrete-module constructions on another site.
* Direct rg over Mathlib, the older upstream project's WeilConjectures,
  the group's exact `lean/WeilConjectures` overlay and `lean/Sheaf`, using
  `locallyconstant.*sheaf|locally_constant.*sheaf|islocallytrivial|constantmodulesheaf`.
  I opened upstream `ConstructibleSheaf/Defs.lean`'s
  `LocallyConstantDatum` and `IsLocallyConstantSheaf`: they require the
  small etale site, not this pro-etale site. I read the exact new framework
  `ConstructibleSheaf/ProEtaleModule/Def.lean`: its
  `IsLocallyFinitelyPresented` is local finite presentation of internal
  module objects, and its constructibility predicate uses finite strata.
  Neither is arbitrary-module coverwise constancy on a localized ringed site.
  The framework `ModuleObject/Basic.lean` uses locally constant functions
  on profinite sets, also not the present notion. I read
  `coord/pefw-upstream-framework.md`; its audit likewise does not attach
  local triviality. Thus no complete existing match replaces this module.

Mismatch repaired: the worker imported the scheme-specific
`Mathlib.AlgebraicGeometry.Modules.Sheaf` for the general module-category
node. That dependency has since received the exact general-site module
`Sheaf.CategoryTheory.RingedSiteModules`. I replaced the obsolete import
with that recorded module. Its abbreviation is definitionally the same
`SheafOfModules` already used, so no signature or mathematical construction
needed rewriting. The worker report's older dependency description is
superseded by this check. All other constructions were retained.

H5/H6/H8/H9: every data definition has an explicit construction. The only
sorries are the two named locally-bijective ring-unit theorems listed in
`lean.declarations`; these supply proof instances, not chosen objects or
module actions. Their docstrings explain sheafification-unit local lifts
and equality witnesses, then their preservation on the localized site.
No theorem is proved. All declaration docstrings carry the source and
blueprint id. No private definitions, file-local instances/notation,
unbound variables or lines over 100 characters occur. The main signature
in `lean.statement` agrees verbatim with the source signature.

Validation: the delivered module compiled cleanly with scompile.py on the
server, nice 19, two threads, default 60 seconds per file. The helper compiled
its side-only RingedSiteModules dependency in the private overlay too.
