## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle` states
`AlgebraicGeometry.schemeDerived_mayerVietoris_triangle`. Its only theorem proof is
`sorry`. The accompanying definition module contains complete terms, without sorry.

Hypothesis and conclusion matching:

- W is a scheme: `(X : Scheme.{u₁})` (X denotes the node's W).
- W is quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
- U and V are open subschemes: `(U V : X.Opens)`; their schemes are `U.toScheme`
  and `V.toScheme`, with canonical immersions `U.ι` and `V.ι`.
- The opens are quasi-compact: `hU : IsCompact (U : Set X)` and the corresponding `hV`.
- They cover W: `hcover : U ⊔ V = ⊤`. The overlap is `(U ⊓ V).toScheme`, with
  immersion `(U ⊓ V).ι`; quasi-separatedness ensures its quasi-compactness.
- For every E in D_QCoh: `(E : schemeDerivedCategory X)` and
  `(hE : schemeDerivedQCohProperty X E)`. This is the underlying object and membership
  predicate of the recorded full subcategory, without changing the category.
- Each restriction is `(schemeOpenRestriction X U).mapDerivedCategory.obj E`,
  and likewise for V and U ⊓ V. The abbreviation expands to precisely the prescribed
  overFunctor / overEquiv composite, not derived pullback or a different sheaf carrier.
- Derived direct images are the dependency's `schemeDerivedDirectImage` at the
  canonical open immersions, applied to these restricted objects.
- The first arrow is `biprod.lift (adjU.unit.app E) (adjV.unit.app E)`.
- The second arrow is `biprod.desc rhoU (-rhoV)`, with the two rho maps constructed
  by `schemeDerivedOpenDirectImageRestriction`. This is the adjoint of restriction
  of the counit, transported by the canonical restriction composition isomorphism.
  Thus these are actual restriction arrows, not arbitrary arrows with the right type.
- The final arrow is the existential `δ : RjUV_* (E|UV) ⟶ E⟦(1 : ℤ)⟧`.
- `Triangle.mk ... δ ∈ distTriang (schemeDerivedCategory X)` states distinguishedness.
  The three subsequent `schemeDerivedQCohProperty` conjuncts put each direct-image
  term in D_QCoh. With hE, these also put their finite biproduct and the triangle in
  that full subcategory (the induced triangulated structure is not separately assumed).
- The three adjunctions are existential conclusions, not added hypotheses: they
  express the restriction adjunctions used to specify the arrows. No arbitrary right
  adjoint replaces the recorded direct-image functor. Changing adjunction coordinates
  transports the triangle by the induced isomorphisms of its direct-image terms.
- Explicit `HasDerivedCategory.{w₁}` binders supply the four localization choices,
  with arbitrary object and localization universes. These are the existing library
  encoding of the unbounded derived categories, not boundedness assumptions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`; the full subcategory definition was read as well.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`,
  expanding to `RingedSpace.derivedModuleDirectImage` (whose definition and
  K-injective comparison were read in RingedSpaceDerivedDirectImage).
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`:
  `schemeDerivedDirectImage_preserves_QCoh`, the justification for the final membership
  assertions, as explicitly explained in the theorem proof docstring.
- The new dependency `def-pc-derived-open-restriction-maps` supplies the definitions
  of the canonical restriction composites and arrows. Its module uses Mathlib's
  `SheafOfModules.overFunctor`, `overMap`, `overFunctorMap`, `Scheme.Modules.overEquiv`,
  `Functor.mapDerivedCategoryCompIso`, `Functor.mapDerivedCategoryNatIso`,
  `Adjunction.homEquiv`, and the existing exactness instances from
  `Sheaf.Paper.DerivedHomMayerVietoris` (moduleOverFunctor_* and moduleOverMap_*).

Edge cases checked before writing: either open may be empty; both may be empty when
X is empty; either may be all X; U=V=X is allowed. For the last case the maps are
pair of identities and difference, giving the standard split triangle. Disjoint
opens give zero overlap. E may be zero; there is no nonzero hypothesis, boundedness
hypothesis, characteristic restriction or affine hypothesis. The intersection is
not assumed compact separately: that follows from quasi-separatedness and hU/hV.
The minus sign is on the V summand, including characteristic two.

Searches performed:

- msearch LeanFinder: `derived Mayer Vietoris triangle for a scheme covered by two
  opens` returned eight hits about scheme gluing and site MayerVietorisSquare,
  none the derived module-sheaf triangle.
- msearch Loogle: `Triangle.mk, biprod.lift, Adjunction.unit` returned zero hits,
  unknown Triangle.mk. Source inspection located it in
  `CategoryTheory.Pretriangulated`, which is now opened explicitly.
- msearch grep: `mayer|Mayer|over.*[Aa]djunction` in Algebra/Category/ModuleCat
  returned zero hits.
- rg in WeilConjectures for Mayer/mayer and the item id found only pro-etale/adic
  Mayer--Vietoris and other unrelated references; no statement for O_X-modules.
- rg in lean/Sheaf found the extension-by-zero triangle (08BU), derived Hom sequence
  (08BW), and derived gluing statement (08DG); these have different statements.
- New-node searches are recorded verbatim/summarized in its mathlib_searches and
  discussed below. LeanSearch was attempted and returned Internal Server Error;
  other services and direct source searches supplied the needed information.

The local literature checkout is absent. The source Tag 08BV was opened at
https://stacks.math.columbia.edu/tag/08BV; its K-injective/short-exact-sequence proof
agrees with the node. No statement correction or statement dispute is needed.
No files outside this item's sandbox were authored and no local compilation ran.

## New nodes

`def-pc-derived-open-restriction-maps` defines the canonical restriction composites,
their underived and derived composition isomorphisms, and the adjoint restriction
map between direct images for nested opens, all by complete terms. Its source is
Stacks Tag 08BV's two restriction arrows. This packages existing exact functors
rather than redefining restriction on sheaves or choosing a second derived category.
The composition formula is the same canonical formula written inline in the landed
DerivedOpenGluing module. No existing named declaration or DAG definition node
packages the direct-image restriction arrow. The existing derived Hom restriction
is a map on Hom sets of two restricted objects and has a different domain/codomain.
LeanSearch failed with Internal Server Error; LeanFinder returned eight scheme
restriction formulas, none derived; Loogle found the underived `overFunctorMap`,
which is reused; grep over Mathlib, WeilConjectures, lean/Sheaf and DAG nodes found
no matching declaration/node; blueprint_refs search returned zero matches.
The structural exactness and additivity instances use existing Mathlib theorems;
there are no new proof obligations hidden inside any definition. A scoped instance
search budget is needed only for additivity of the three-fold restriction composite.

## Second reading by U1

I independently read the item node, both delivered modules, the four recorded
statement dependencies and their declaration signatures, and the new node's
additional dependency `lem-sc-derived-hom-mayer-vietoris`. I read the Stacks
cohomology.tex source at `lemma-exact-sequence-j-star` (Tag 08BV), including the
preceding section introduction: its only ambient assumptions are a ringed space
and a two-open cover, and it uses the unbounded derived category. The qcqs scheme
and quasi-coherent specialization is the item's explicit restriction of that
statement; Tag 08D5(1) supplies the direct-image membership assertions.
Sources: https://stacks.math.columbia.edu/tag/08BV and
https://stacks.math.columbia.edu/tag/08D5.

Object, hypothesis and conclusion checklist, written before assessing the Lean:

- Ambient W is a scheme: `X : Scheme.{u₁}`. Verdict: exact renaming. I read
  Mathlib's `Scheme` and `Scheme.Hom` signatures; these are the recorded
  `def-pc-scheme` declarations, not an affine or Noetherian substitute.
- W is quasi-compact and quasi-separated: `[CompactSpace X]` and
  `[QuasiSeparatedSpace X]`. Verdict: exact topological conditions on the scheme.
- U,V are quasi-compact open subschemes: `U V : X.Opens`, `hU` and `hV` are
  `IsCompact` of their underlying subsets. Verdict: exact; the schemes are
  `U.toScheme`, `V.toScheme`, and the overlap `(U ⊓ V).toScheme`.
- W is their union: `hcover : U ⊔ V = ⊤`. Verdict: exact cover condition.
- The three named open immersions: `U.ι`, `V.ι`, `(U ⊓ V).ι`. Verdict: precisely
  the canonical inclusions; no additional immersion data or assumptions.
- For every E in D_QCoh: `E : schemeDerivedCategory X` with
  `hE : schemeDerivedQCohProperty X E`. Verdict: exact underlying-object encoding
  of the recorded full subcategory. I read the definitions: the category is the
  unbounded localization of module-sheaf complexes, and the property requires
  quasi-coherent cohomology in every integer degree.
- Restricted objects: `(schemeOpenRestriction X U).mapDerivedCategory.obj E`
  and the V/overlap analogues. Verdict: exact restriction. The abbreviation uses
  the prescribed `overFunctor` followed by `Scheme.Modules.overEquiv`, on the
  shared `SheafOfModules (moduleRings ...)` carrier. I read Mathlib's `overEquiv`,
  `overFunctorEquiv`, and `overMapCompOverEquiv`: they identify these composites
  with ordinary open restriction. `Scheme.Modules.restrictFunctor` itself uses
  the distinct `X.Modules` category instance, so it is not a replacement for the
  shared derived-category carrier.
- Direct images: `schemeDerivedDirectImage` at each inclusion, applied to the
  corresponding restriction. Verdict: exact recorded dependency. I followed it
  through `RingedSpace.derivedModuleDirectImage` to the unbounded right derived
  functor and its K-injective comparison; it is neither extension by zero nor
  an arbitrary right adjoint.
- First arrow: `biprod.lift (adjU.unit.app E) (adjV.unit.app E)`.
  Verdict: the pair of restriction adjunction maps, with exactly the right source
  and two summands. The adjunctions are existentially supplied, not extra
  hypotheses. They relate the actual recorded functors. Different adjunction
  coordinates give naturally isomorphic right-adjoint terms and transport the
  triangle, so this choice of coordinates does not change the assertion.
- Second arrow: `biprod.desc rhoU (-rhoV)`, where rhoU/rhoV are
  `schemeDerivedOpenDirectImageRestriction` for `homOfLE inf_le_left/right`.
  Verdict: exactly the difference of restriction maps. I checked the full term:
  inverse composition iso, restricted counit, composition iso, then the overlap
  adjunction's `homEquiv`. There is no unconstrained arrow existential here.
- Final arrow and distinguishedness: the existential `δ` has source the overlap
  derived direct image and target `E⟦(1 : ℤ)⟧`; `Triangle.mk ... δ ∈ distTriang`
  asserts distinguishedness. Verdict: exact order of terms and shift.
- Triangle in D_QCoh: the last three conjuncts assert
  `schemeDerivedQCohProperty X` of all three individual direct-image terms.
  Together with hE, their finite biproduct belongs to the same full subcategory;
  distinguishedness is the induced distinguishedness from D(O_X). Verdict:
  exact, without asking for an unrelated triangulated structure or omitting
  quasi-coherence. The recorded preservation theorem has only qcqs morphism
  assumptions, as needed for these inclusions.
- Localization binders: the four `HasDerivedCategory.{w₁}` instances use the
  shared sheaf-module carrier, with arbitrary `u₁,w₁`. Verdict: localization
  choices in the established encoding, with no boundedness, small-scheme,
  coefficient-field or characteristic restriction.

Edge cases: an empty open is permitted, both may be empty when X is empty,
U=V=X is permitted (the split diagonal/difference triangle), and disjoint opens
have zero overlap. The zero derived object is permitted. The intersection's
compactness follows from quasi-separatedness rather than a new hypothesis.
There is no degree cutoff; degree zero and negative degrees are included.
The sign on the V summand also works in characteristic two. No index set,
nonempty condition, finiteness of cohomology, or additional universe parameter
has been introduced.

Independent searches (queries differ from the first worker's):

- LeanFinder: `distinguished triangle of derived pushforwards for two open
  subsets`, eight hits. `Scheme.Modules.restrictFunctorComp`, `restrictFunctor`,
  and `restrictAdjunction` are underived ingredients; the other hits concern
  ordinary sheaf pushforward. None states this derived triangle.
- LeanFinder: `adjoint of restriction counit between derived direct images of
  nested opens`, eight hits, all underived scheme/sheaf restriction formulas.
  I opened `restrictAdjunction`, its counit formulas and the `overEquiv` bridges.
  None defines the needed derived morphism.
- Loogle: `SheafOfModules.overMap`, eight hits including `overFunctorMap` and
  `overMapCompOverEquiv`. These are reused ingredients, not this derived map.
- LeanSearch: `derived pushforward restriction morphism for nested open
  subsets`; service returned Internal Server Error. Recorded as unavailable.
- Direct rg searches over Mathlib homological/algebraic-geometry sources,
  WeilConjectures, and lean/Sheaf for Mayer/mayer, directImageRestriction,
  restriction composition, and the new names: no matching statement or named
  derived map. Existing sheaf modules give the shriek triangle (different
  orientation and functors), Hom Mayer--Vietoris (Hom sets), and open gluing
  (objects with compatibility); these do not duplicate this item.
- DAG searches for nested opens and derived/direct-image restriction found no
  existing node defining this adjoint restriction arrow. Other results describe
  base change, inverse-image adjunctions, or cohomology restrictions.

New-node reading: `def-pc-derived-open-restriction-maps` introduces a scheme and
nested opens, the exact restrictions, canonical composition identification,
and the adjoint of the restricted counit. The formula agrees term by term with
its module and the restriction arrows used in 08BV's sheaf exact sequence.
The node cites the scheme, derived category, derived direct image and existing
open-exactness module; the latter's recorded signatures were read and reused.
All data definitions are complete terms. Exactness/additivity instances only
compose the existing structures; no new theorem is proved or hidden inside a
definition. The definition node has the required id, chapter/unit, definition
kind, split status, source, search records, empty proofs, null mathlib_match,
creation record, and none-state audits. There are no dependency replacement
modules. The local item copy had a shorter ancestry path than the current server base.
I initially shortened the new node's `via` to match the local copy; the dry-run
preflight supplied the current server path and I restored the worker's original
new-node path, which was correct. This metadata discrepancy does not affect
the mathematical statement. No delivery definition, statement, or Lean code
needed a change, and no statement correction or disputed statement is present.

Docstrings checked: both modules and every declaration cite their own blueprint
node and source; the theorem carries all four proof steps, including the
non-split SES triangle and final QCoh argument. The only delivered theorem
proof remains `sorry`; there are no hollow definitions, private declarations,
file-local instances/notation, or unbound variables/universes. Both node
`lean.statement` strings agree verbatim with their module signatures.

Validation: scompile compiled both modules together in dependency order on the
server in 12.3 seconds, exit code 0, with no warnings or errors. No local Lean
build or direct git command was run.
