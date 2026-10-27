## Worker report

The delivery states `AlgebraicGeometry.Scheme.normalDivisorialOpenRestriction` in
`Sheaf.AlgebraicGeometry.NormalDivisorialOpenRestriction`. Its sole theorem has proof
`sorry`. All eight local helper definitions have real data. The rank-one predicate is
imported from `Sheaf.AlgebraicGeometry.NormalDivisorialModule`, as requested in
the maintainer return. The mathematical statement,
proof, and proof dependencies of the node are unchanged. The statement dependencies
gain the already landed `def-per-effective-q-cartier-weil-divisor`, whose existing
`Scheme.WeilPrime` and `Scheme.WeilDivisor` are reused, and the new
`def-sfb-coherent-reflexive-rank-one`, which owns the imported predicate.

Source read: `literature/stacks-project/divisors.tex`, labels
`lemma-normal-class-group` (0EBM), `lemma-reflexive-normal` (0EBL),
`definition-divisor-invertible-sheaf` (0BE6), and `lemma-normal-c1-injective` (0BE8).
The node's agent-extracted formulation and its ten proof steps supply the finite
Noetherian version, the explicit section prescription, and the boundary assertion.
The module docstring and theorem docstring describe the concrete construction and
all ten proof steps. No statement correction or disputed statement is needed.

Hypotheses and objects, matched individually:

- The scheme is `Y : Scheme.{u}`. All its section and stalk modules have the same
  arbitrary universe `u`; no field, separatedness, projectivity, excellence, or
  smoothness assumption is imposed.
- Integrality is `[IsIntegral Y]`, the recorded Mathlib definition, including
  nonemptiness and the domain condition on sections of nonempty opens.
- Noetherianity is `[IsNoetherian Y]`. Mathlib's class is local Noetherianity plus
  compactness, equivalent to the node's finite affine cover by Noetherian rings;
  see `isNoetherian_iff_of_finite_iSup_eq_top` in `Noetherian.lean:284`.
- Normality is the explicit binder `hnormal : ∀ y : Y,
  IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)`.
  This uses precisely the recorded inline normal-domain interface.
- The open subscheme is `U : Y.Opens` and nonemptiness is `[Nonempty U]`.
  `U.toScheme` and `U.ι` are the canonical open subscheme and its open immersion.
  Integrality of `U.toScheme` is inferred from these assumptions, not added.
- Prime divisors are `Y.WeilPrime`, points with local-ring dimension one. Taking
  their reduced closures is the bijection with the node's integral closed
  subschemes. `Y.WeilDivisor` is their finitely supported integer combination.
- `Y.functionField` is the recorded generic-stalk field. `WeilDivisor.Allows`
  writes a nonzero rational function as `a/b` in the codimension-one local ring
  and requires `ord(a)-ord(b)+D p ≥ 0`. Here `Ring.ord R a` is the length of
  `R/(a)`; on a DVR, for nonzero `a`, it is exactly the normalized order.
  The natural numbers are coerced to integers before subtraction. The disjunct
  `f = 0` includes zero independently of its order.
- `AllowsSection` imposes that condition at every prime divisor meeting the
  open. In an irreducible scheme an open meets a prime divisor exactly when it
  contains its generic point. The ambient generic-point skyscraper is the
  constant rational sheaf on nonempty opens and the zero group on the empty open.
- `divisorialSubpresheaf` is the infimum of subpresheaves containing all allowed
  sections, using Mathlib's actual subpresheaf lattice; `divisorialModule` is its
  module sheafification. `divisorialInclusion` is the sheafification of the
  inclusion followed by the adjunction counit. These constructions use no
  theorem asserting a mere existence. The first conclusion asserts injectivity
  and exactly the prescribed image on every open, so the generated/sheafified
  presentation is identified with the node's actual valuation subsheaf.
- `Modules.dual` is the upstream internal Hom into the unit module.
  `Modules.IsCoherentReflexiveRankOne` is the conjunction of the recorded
  `RingedSpace.IsCoherent`, `IsIso (SheafOfModules.bidual F)`, and
  `Modules.rank F = 1`. The last is the dimension of the generic stalk over
  the function field, using upstream `Modules.GenericRank`, not a new rank.

Conclusions, in the order of the Lean conjunction:

1. For every divisor, its divisorial module is coherent, reflexive, and rank one.
   Its inclusion is sectionwise injective with range exactly `AllowsSection`.
2. For zero, an isomorphism to `𝟙_ Y.Modules` identifies the rational inclusion
   with the generic germ of each regular section. This is equality as embedded
   subsheaves, expressed using an isomorphism of bundled modules with that formula.
3. Every coherent reflexive rank-one `F` is isomorphic to `D.divisorialModule`
   for a finite Weil divisor `D`.
4. Every `D` has `E` on `U` with `D.IsOpenRestriction U E`, meaning its coefficient
   at every height-one point of `U` is the coefficient at the same point of `Y`.
   The restriction isomorphism identifies each rational section via
   `openFunctionFieldMap`. This map is the inverse open-immersion generic-stalk
   isomorphism, followed by specialization along the equality of generic points.
   No arbitrary field isomorphism or arbitrary sheaf comparison is substituted.
5. Every invertible module `L` on `U` is the restriction of some coherent
   reflexive rank-one `F` on `Y`.
6. If such an `F` restricts to the unit, there are `s`, an injective enumeration
   `Z : Fin s → Y.WeilPrime`, and integers `m`, with range exactly the primes
   whose closures lie in the boundary, and `F ≅ O(∑ m_i[Z_i])`.
   These are precisely the codimension-one irreducible components: any larger
   irreducible closed subset containing a height-one prime divisor would have
   generic prime strictly below a height-one prime, hence would be all of `Y`;
   it cannot lie in the proper closed boundary. Conversely every codimension-one
   boundary component has one such generic point. Thus this range equality
   encodes “precisely,” including zero coefficients and empty boundary.
7. For every `D,E`, the double dual of `O(D) ⊗ O(E)` is isomorphic to `O(D+E)`.
8. For every coherent reflexive rank-one `F` and divisor `E`, its twisted double
   dual again has all three properties. If `F|U` is invertible and the coefficients
   of `E|U` vanish (`E.IsOpenRestriction U 0`), its restriction is isomorphic to
   `F|U`.
9. For every module `F`, the dual and double-dual restriction isomorphisms preserve
   evaluation on all sections. The double-dual comparison also commutes with the
   actual bidual evaluation morphism. The section formulas determine these maps
   canonically; an unconstrained isomorphism would not give these equations.
10. Tensor restriction preserves pure tensor sections under the canonical
    `restrictAppIso` identifications, exactly the recorded tensor comparison.
    Pure tensor sections locally generate the sheaf tensor product, so this fixes
    its comparison as well.

Dependency declarations read and used (module followed by declarations):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the integral-scheme clause
  reexports Mathlib `Scheme.functionField`, not the component product intended
  for a possibly reducible curve. Its docstring explicitly specifies this use.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  the normalized integer order is represented by `Ring.ord` on numerators and
  denominators, from `Mathlib.RingTheory.OrderOfVanishing.Basic`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: its public upstream import
  exposes `RingedSpace.IsCoherent`, with finite-type kernels; the weaker
  `IsQuasiCoherentFiniteType` conjunction is not used for coherence.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`; `WeilConjectures.AlgebraicGeometry.Modules.Dual`:
  `Modules.dual`; its public bidual import exposes `SheafOfModules.bidual`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: normalized tensor
  pullback interface, public statement dependency. Open restriction itself is
  the canonical `Modules.restrict` from Mathlib, canonically isomorphic to
  `Modules.pullback U.ι` by `restrictFunctorIsoPullback`; no second pullback.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the existing sheaf tensor structure;
  upstream `Modules.Dual` uses its same localization tensor construction.
- `Sheaf.AlgebraicGeometry.EffectiveQCartierWeilDivisor`: `Scheme.WeilPrime`,
  `Scheme.WeilDivisor`. Only these already defined notions are used; no
  effectiveness or Q-Cartier hypothesis is added.
- Additional existing tools: `Modules.skyscraper`, `Modules.SkyscraperSections`
  from `Modules.FlatPullbackStalk`, `Modules.rank` from `Modules.GenericRank`,
  `PresheafOfModules.Submodule` and `sheafification`, and the canonical counit.

The available recorded proof dependencies are imported without `public`:
coherence local on an open cover, restriction/tensor comparison, coherent affine
sections, reflexive height-one intersection, coherent finite type on locally
Noetherian schemes, quasi-coherent tensor affine sections, coherent sheaf Hom,
coherent local presentation, and stalk internal Hom. Mathlib proof inputs are
likewise imported. No module is imported for the not-yet-recorded proof nodes
`lem-trf-normal-domain-principal-divisor-kernel`,
`lem-per-divisorial-fractional-module-lattices`,
`lem-sfb-affine-reflexive-module-comparison`, and
`lem-sfb-coherent-reflexive-hull`; none is needed to type the statement or construct
its data. Their pending proofs remain the DAG's existing tasks, not new sorries here.

Edge cases checked before and during writing:

- `Y = Spec K`: there are no height-one primes. Every allowed nonempty section
  is in `K`, the empty intersection is all `K`, all divisors are zero, and rank-one
  coherent modules are one-dimensional vector spaces.
- A DVR, `D=n[closed]`: the inequality is `ord(f) ≥ -n`, giving `π^(-n)R`.
  Tensor adds the two exponents; negative coefficients instead give ideals.
- `U=Y`: the boundary enumeration has `s=0`; the kernel assertion says a trivial
  module is `O(0)`. No nonempty boundary or positive `s` is required.
- Boundary of codimension at least two: again `s=0`; a reflexive module trivial
  off that boundary is trivial, as height-one reconstruction requires.
- `W=∅` in every section formula: the skyscraper section type is a function on
  the empty proposition, hence has one element; `AllowsSection` is vacuous and
  the range characterization gives exactly this zero group. No spurious copy
  of `K` appears over the empty open.
- A singular normal scheme (e.g. a normal quadric cone): the result does not claim
  every rank-one reflexive module is invertible; invertibility on `U` is required
  only in the last restriction clause.
- Zero `F` fails generic rank one, as it should; `E=0` and `D=0` remain allowed.
- No characteristic restriction, dimension bound, or independently too-small test
  universe is present. All local orders concern nonzero elements of DVRs, so
  `ENat.toNat` never truncates an infinite length in the valuation calculation.

Searches run, with actual outcomes:

- `msearch.py ... leanfinder "On an integral Noetherian normal scheme Weil
  divisors classify coherent rank one reflexive sheaves and restrict to open
  subschemes"`: eight hits, including normalizationDiagram, finite fraction
  normalization, and powers clearing denominators. None states the dictionary.
- `msearch.py ... leansearch "Weil divisor sheaf on a normal scheme reflexive
  coherent rank one"`: eight hits including `Scheme.Modules`, structureSheafInType,
  and ideal sheaf constructions, none giving the divisorial dictionary.
- `msearch.py ... loogle "AlgebraicGeometry.WeilDivisor, IsReflexive, divisorial"`:
  zero hits, unknown identifier `AlgebraicGeometry.WeilDivisor`.
- `msearch.py ... grep "WeilDivisor|Divisorial|divisorial|IsReflexive"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the divisorial terms:
  found the reusable `EffectiveQCartierWeilDivisor` definitions, affine-only
  divisor lattices, and the strict-local Cartier theorem, which differs from this
  sheaf dictionary; upstream curve rational sections and generic-rank/skyscraper
  constructions were reused. Many remaining hits concern unrelated log structures.
- `grep -rn "lem-sfb-normal-divisorial-open-restriction" lean/WeilConjectures`:
  no declaration for this item. An `rg` for all chosen new declaration names in
  both project roots found no preexisting names. The DAG node of the reused
  divisor definition was opened and its statement and Lean record read.

Validation: all compiler invocations used the prescribed `scompile.py Q91
lem-sfb-normal-divisorial-open-restriction <file>` wrapper, in module mode.
The complete module compiled both as sandbox and under its own module name.
Earlier elaboration diagnostics were repaired: the generic stalk equality needed
its inverse direction; the finite sum needed an explicit `WeilDivisor.divisorialModule`
application; and the sheafification counit needed its full target and the standard
transparency option for the identity scalar restriction. No additional theorem
or proof obligation was introduced for any of these repairs.

## Second reading by Q91

I reread the actual node and the final signature clause by clause after compilation.
This is a separate self-check; the dispatcher's explicit no-other-agents instruction
precludes an independent worker here, and the maintainer supplies independent review.

The first pass had plain isomorphisms for `O(0)` and only the dual restriction
comparison. I replaced the zero isomorphism with the generic-germ formula and
added the double-dual section evaluation formula, the commutative bidual square,
and the tensor pure-section comparison. These repairs ensure that “canonical” in
the last sentence is mathematical data in the signature. I checked that the
range equality for the boundary enumerates all and only its codimension-one
components, and retains `Fin 0` and zero coefficients. I rechecked the cast before
subtraction in `Allows`, the `O(D)` sign at a DVR, and the trivial section over
an empty open. No mismatch remains between the node's hypotheses and conclusions
and the final statement. The eight local helpers implement notions introduced by this item, and the
imported rank-one conjunction now has its own definition node; the existing prime/divisor, Hom, dual, rank, coherence, tensor,
and restriction definitions are reused. No definition's data contains `sorry`.


## Returned-delivery repair

The return for immutable head `c3a61fb5bd6c` required reuse of
`AlgebraicGeometry.Scheme.Modules.IsCoherentReflexiveRankOne` from
`Sheaf.AlgebraicGeometry.NormalDivisorialModule`. The theorem module now imports
that module and no longer defines or claims ownership of the predicate. Its
theorem signature is unchanged.

The named dependency is not actually present in current published sources. The
local tree has no source or recorded owner; repeated prescribed `scompile.py
--source` calls report `Module source unavailable`. A read-only check of the
server's exact source path reports `Source exists: False`; the server's current
`local/stage2/parallel/source-index.pickle` reports `Cached owners: []` and no
source stamp for the module. Compiling with only the import, and the previous
`--no-push` dry run, failed with its missing `.olean`, including current-source
confirmation.

This retry repairs that missing prerequisite under the brief's §1(A), supplying
the sole definition at the owner module and declaration name required by the
return, with its own definition node. No alternate name or second copy is used.

## New nodes

`def-sfb-coherent-reflexive-rank-one` owns
`Sheaf.AlgebraicGeometry.NormalDivisorialModule` and the single definition
`AlgebraicGeometry.Scheme.Modules.IsCoherentReflexiveRankOne`. The item cites this
new definition in `stmt_deps`. All underlying notions are reused: coherence from
`RingedSpace.IsCoherent`, canonical reflexivity from
`IsIso (SheafOfModules.bidual (R := Y.sheaf) F)`, and generic dimension one from
`Modules.rank F = 1`. The definition has real conjunction data and no `sorry`.
The integral scheme and module binders impose precisely the new node's objects;
no normality or Noetherianity hypothesis is needed for defining the conjunction.

Searches for the new node: LeanSearch's query `coherent reflexive rank one sheaf
on integral scheme` returned eight general scheme/sheaf hits; Loogle's query
`IsCoherentReflexiveRankOne, SheafOfModules.bidual,
AlgebraicGeometry.Scheme.Modules.rank` returned zero hits (unknown predicate);
Mathlib grep `IsCoherentReflexiveRankOne|def.*[Rr]eflexive` in AlgebraicGeometry
returned zero hits. Project grep found only an unrelated derived reflexivity
notion in `RelativeBidualTriangles`. The definition-node grep found no matching
conjunction, and `blueprint_refs.py search reflexive rank` found zero blueprint
nodes. The unabridged msearch outputs are recorded in the new node.
`blueprint_refs.py ancestor` confirms the ancestor is null, matching the item's
historical prerequisite chain. Source read: Stacks `divisors.tex`, the actual
statements of `lemma-reflexive-normal` and `lemma-normal-class-group`.

The zero module fails generic rank one, and the structure module over a field
has rank one and invertible evaluation. Over a normal singular scheme, the
predicate permits noninvertible rank-one reflexive modules, as required. The
existing theorem's edge-case analysis remains unchanged.

Validation of this retry: `scompile.py Q91
lem-sfb-normal-divisorial-open-restriction` compiled both delivered files together
in dependency order, checking each separately, with no errors or warnings. It
checked the helper in the private overlay and the theorem as both sandbox and
library module. No new postponed theorem was added.

## Immutable-head 1983547c474e return: repaired reviewer fix packet

The returned `--apply-fixes` error names a new-node JSON under a nested
`dag/nodes/sec-six-functors-basics/` path. The stage-2 reviewer interface accepts
this file directly under its fix directory as
`DIR/def-sfb-coherent-reflexive-rank-one.json` (see `tools/merge_delivery.py`,
the `r[:-5] in D["new"]` test). The worker delivery interface separately requires
the node under `dag/nodes/<chapter>/`; the delivered DAG file retains that
required location.

This repair supplies a flat reviewer fix packet in the sandbox at
`review-fixes/def-sfb-coherent-reflexive-rank-one.json`, parsed and checked equal
to the delivered definition node. Its complete contents are embedded below so
that the repaired artifact is carried to the server in this report. For the
reviewer's `--apply-fixes DIR`, save this JSON as
`DIR/def-sfb-coherent-reflexive-rank-one.json` directly in DIR. The module
basenames accepted by the same interface are `NormalDivisorialModule.lean` and
`NormalDivisorialOpenRestriction.lean`; the report basename is
`lem-sfb-normal-divisorial-open-restriction.report.md`.

The return specifies no mathematical, Lean, or node-content correction. This
packet repairs the stated path failure through the existing flat-file interface.
Any further reviewer edits belong in the flat JSON before applying it. The
canonical DAG file, the unique predicate owner, and the theorem signature are
unchanged. No launcher, shared tool, or live source was edited.

<!-- BEGIN FLAT REVIEW FIX: def-sfb-coherent-reflexive-rank-one.json -->
```json
{
 "id": "def-sfb-coherent-reflexive-rank-one",
 "kind": "definition",
 "title": "Coherent reflexive module of rank one on an integral scheme",
 "status": "split",
 "import_flags": [],
 "statement": "Let $Y$ be an integral scheme [def-pc-scheme, def-pc-integral-scheme], with function field $k(Y)$ [def-sc-function-field], and let $F$ be an $\\mathcal O_Y$-module. Say that $F$ is coherent reflexive of rank one if it is coherent [pqf-def-coherent], its canonical evaluation morphism $F\\to\\mathcal Hom_{\\mathcal O_Y}(\\mathcal Hom_{\\mathcal O_Y}(F,\\mathcal O_Y),\\mathcal O_Y)$ is an isomorphism [def-pur-sheaf-hom], and the stalk of $F$ at the generic point has dimension one over $k(Y)$.",
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-integral-scheme",
  "def-sc-function-field",
  "pqf-def-coherent",
  "def-pur-sheaf-hom"
 ],
 "source": {
  "document": "literature/stacks-project/divisors.tex",
  "place": "Tags 0EBL (lemma-reflexive-normal) and 0EBM (lemma-normal-class-group), the rank-one coherent reflexive modules used in their statements."
 },
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "mathlib_match": null,
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "coherent reflexive rank one sheaf on integral scheme",
   "results": "[leansearch] OK 8 hit(s)\n  {\"name\": \"AlgebraicGeometry.Scheme.Modules\", \"module\": \"Mathlib.AlgebraicGeometry.Modules.Sheaf\", \"type\": \"AlgebraicGeometry.Scheme → Type (u + 1)\", \"doc\": \"Given a scheme $X$, this defines the type of sheaves of modules over the ring sheaf associated to $X$, obtained by composing the structure sheaf (taking values in commutative rings) with the canonical\"}\n  {\"name\": \"AlgebraicGeometry.LocallyRingedSpace.𝒪\", \"module\": \"Mathlib.Geometry.RingedSpace.LocallyRingedSpace\", \"type\": \": Sheaf CommRingCat X.toTopCat\", \"doc\": \"The sheaf $\\\\mathcal{O}_X$ of commutative rings on the underlying topological space of a locally ringed space $X$, where every stalk is a local ring. This is the canonical sheaf associated to the local\"}\n  {\"name\": \"SheafOfModules.isQuasicoherent\", \"module\": \"Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent\", \"type\": \": ObjectProperty (SheafOfModules.{u} R)\", \"doc\": \"A property asserting that a sheaf of modules over a ring sheaf satisfies local bijectivity conditions between hom-sets and module morphisms, ensuring compatibility with the ring structure and sheaf ax\"}\n  {\"name\": \"AlgebraicGeometry.instIsGermInjectiveOfIsIntegral\", \"module\": \"Mathlib.AlgebraicGeometry.SpreadingOut\", \"type\": \"[IsIntegral X] : X.IsGermInjective\", \"doc\": \"Every integral scheme is germ-injective. That is, for every point $ x $ in an integral scheme $ X $, the natural map from the local ring $ \\\\mathcal{O}_{X,x} $ to the stalk of the structure sheaf at $ \"}\n  {\"name\": \"SheafOfModules.QuasicoherentData.IsFinitePresentation\", \"module\": \"Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent\", \"type\": \"{C : Type u'} →\\n  [inst : CategoryTheory.Category.{v', u'} C] →\\n    {J : CategoryTheory.GrothendieckTopology C} →\\n      {R : CategoryTheory.Sheaf J RingCat} →\\n        [inst_1 : ∀ (X : C), (J.over X).HasSheafCompose (CategoryTheory.forget₂ RingCat AddCommGrpCat)] →\\n          [inst_2 : ∀ (X : C), Cate\", \"doc\": \"A proposition asserting that a quasicoherent sheaf $\\\\mathcal{M}$ over a ring sheaf $\\\\mathcal{O}$ on a site $(\\\\mathcal{C}, J)$ satisfies the finite presentation condition: for every object $X \\\\in \\\\math\"}\n  {\"name\": \"AlgebraicGeometry.Spec.locallyRingedSpaceObj_sheaf'\", \"module\": \"Mathlib.AlgebraicGeometry.Spec\", \"type\": \"(R : Type u) [CommRing R] : (Spec.locallyRingedSpaceObj <| CommRingCat.of R).sheaf = structureSheaf R\", \"doc\": \"For a commutative ring $ R $, the sheaf of the locally ringed space $\\\\operatorname{Spec}(R)$ is equal to the structure sheaf $\\\\mathcal{O}_{\\\\operatorname{Spec}(R)}$ constructed from the ring $ R $.\"}\n  {\"name\": \"SheafOfModules.instIsQuasicoherentOfIsFinitePresentation\", \"module\": \"Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent\", \"type\": \"(M : SheafOfModules.{u} R) [M.IsFinitePresentation] : M.IsQuasicoherent\", \"doc\": \"Every sheaf of modules with finite presentation over a ring sheaf is quasicoherent.\"}\n  {\"name\": \"AlgebraicGeometry.Scheme.Modules.instAbelian\", \"module\": \"Mathlib.AlgebraicGeometry.Modules.Sheaf\", \"type\": \": Abelian X.Modules\", \"doc\": \"For any scheme $ X $, the category of sheaves of modules over the structure sheaf of $ X $ is an abelian category. This follows from the preadditive structure, existence of finite products, kernels, a\"}\n",
   "date": "2026-10-24",
   "verdict": "No definition of the conjunction of scheme coherence, canonical bidual reflexivity and generic rank one."
  },
  {
   "tool": "loogle",
   "query": "IsCoherentReflexiveRankOne, SheafOfModules.bidual, AlgebraicGeometry.Scheme.Modules.rank",
   "results": "[loogle] OK 0 hit(s) | loogle: unknown identifier 'IsCoherentReflexiveRankOne'\n",
   "date": "2026-10-24",
   "verdict": "No definition of the conjunction of scheme coherence, canonical bidual reflexivity and generic rank one."
  },
  {
   "tool": "grep",
   "query": "IsCoherentReflexiveRankOne|def.*[Rr]eflexive (Mathlib/AlgebraicGeometry)",
   "results": "[grep] OK 0 hit(s)\n",
   "date": "2026-10-24",
   "verdict": "No definition of the conjunction of scheme coherence, canonical bidual reflexivity and generic rank one."
  },
  {
   "tool": "rg",
   "query": "IsCoherentReflexiveRankOne|def.*[Rr]eflexive in lean/WeilConjectures and lean/Sheaf",
   "results": "lean/Sheaf/CategoryTheory/RelativeBidualTriangles.lean:138:def reflexive (K : D.{c, v, r, w} J O) (M : RingedSiteDualityModel.{c, v, r, w} J O) :",
   "date": "2026-10-24",
   "verdict": "Only a different derived reflexivity notion. No sheaf coherent reflexive rank-one conjunction."
  },
  {
   "tool": "rg",
   "query": "coherent.{0,15}reflexive.{0,15}rank|rank.{0,8}one.{0,15}reflexive in dag/nodes/def-*.json",
   "results": "No matches. Statement nodes use the notion, notably the owning item, but no definition node introduces this conjunction.",
   "date": "2026-10-24",
   "verdict": "A new definition node is needed for the missing imported owner."
  },
  {
   "tool": "blueprint_refs.py search",
   "query": "reflexive rank",
   "results": "0 blueprint nodes match 'reflexive rank'",
   "date": "2026-10-24",
   "verdict": "No duplicate blueprint definition."
  },
  {
   "tool": "scompile.py --source",
   "query": "Sheaf.AlgebraicGeometry.NormalDivisorialModule",
   "results": "Module source unavailable: Sheaf.AlgebraicGeometry.NormalDivisorialModule",
   "date": "2026-10-24",
   "verdict": "The source module named in the return is absent; supply its missing definition with the same name and module, then import it."
  }
 ],
 "created": {
  "by": "worker",
  "item": "lem-sfb-normal-divisorial-open-restriction",
  "date": "2026-10-24",
  "group": "Q91"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "Historical alteration/Picard prerequisite, the coherent reflexive rank-one objects in the divisorial-sheaf dictionary. The latest stability blueprint no longer spells out this historical prerequisite.",
   "via": [
    "lem-sfb-normal-divisorial-open-restriction",
    "lem-sfb-constant-variety-picard-detection",
    "lem-sfb-birigidified-affine-triviality-locus",
    "lem-sfb-field-square-after-finite-extension",
    "lem-sfb-field-product-square-power",
    "lem-sfb-normal-group-square-power",
    "lem-sfb-group-affine-section-ampleness",
    "lem-sfb-normal-smooth-group-local-ample-line",
    "lem-sfb-symmetric-line-power-prolongation",
    "lem-sfb-normal-symmetric-cubical-extension",
    "lem-sfb-symmetric-ample-power-extension",
    "lem-sfb-regular-group-generic-ampleness",
    "lem-sfb-stable-picard-theta-ampleness",
    "lem-sfb-stable-relative-picard-kummer",
    "lem-sfb-stable-level-versal-branch-freeness",
    "lem-sfb-stable-abelian-level-normalization",
    "lem-sfb-projective-stable-pointed-level-parameter",
    "lem-sfb-stable-pointed-generic-extension",
    "lem-sfb-equivariant-single-curve-nodal-reduction",
    "lem-sfb-equivariant-plurinodal-field-alteration",
    "lem-sfb-equivariant-smooth-galois-model",
    "lem-sfb-gabber-global-snc-alteration",
    "lem-sfb-nested-open-regular-alteration",
    "lem-sfb-tame-pair-proper-generators",
    "lem-sfb-continuous-algcl-open-scalar-comparison",
    "lem-sfb-continuous-algcl-open-finiteness",
    "lem-sfb-admissible-direct-image"
   ]
  },
  "same_as": []
 },
 "lean_audit": {
  "master": {
   "state": "none"
  },
  "slopmaster2": {
   "state": "none"
  }
 },
 "chapter": "sec-six-functors-basics",
 "unit": "sk-thm-sf-ctf-stability",
 "lean": {
  "module": "Sheaf.AlgebraicGeometry.NormalDivisorialModule",
  "declaration": "AlgebraicGeometry.Scheme.Modules.IsCoherentReflexiveRankOne",
  "file": "lean/Sheaf/AlgebraicGeometry/NormalDivisorialModule.lean",
  "statement": "def Modules.IsCoherentReflexiveRankOne {Y : Scheme.{u}} [IsIntegral Y]\n    (F : Y.Modules) : Prop",
  "branch": "newtargets-dag",
  "by": "Q91",
  "date": "2026-10-24",
  "existing": false,
  "note": "Supply the missing module named in the return. There is no renamed duplicate: the theorem module imports this sole conjunction and does not define it."
 }
}
```
<!-- END FLAT REVIEW FIX: def-sfb-coherent-reflexive-rank-one.json -->

The following extraction, run by the reviewer from the report's directory,
materializes the embedded artifact in a fresh flat fix directory. It invokes
no project checker or merger and does not modify the project sources.

```python
from pathlib import Path
import json
report = Path("lem-sfb-normal-divisorial-open-restriction.md").read_text()
start = report.index("<!-- BEGIN FLAT REVIEW FIX:")
start = report.index("```json\n", start) + len("```json\n")
end = report.index("\n```", start)
node = json.loads(report[start:end])
fixdir = Path("normal-divisorial-flat-fixes")
fixdir.mkdir(exist_ok=True)
(fixdir / (node["id"] + ".json")).write_text(
    json.dumps(node, ensure_ascii=False, indent=1) + "\n")
```
