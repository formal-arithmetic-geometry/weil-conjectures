## Worker report

The module `Sheaf.Algebra.Homology.ChangeOfRingsKFlat` states
`SheafOfModules.changeOfRings_isKFlat_of_flat_terms`. Its only proof is `sorry`.
The original statement is unchanged; its statement dependencies gain the new construction node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`.
  The sheafification and locally-bijective instances supply the module sheaf categories.
  `J.HasSheafCompose` supplies forgetting commutative ring sheaves to ring sheaves.
  These are ambient implementations of sheaf categories, not flatness assumptions on φ.
- The sheaves of commutative rings are `{R S : Sheaf J CommRingCat.{max u v}}`,
  and the given coefficient morphism is `(φ : R ⟶ S)`.
- `K` is a `CochainComplex (SheafOfModules ... R) ℤ`, including all unbounded complexes.
- K-flatness is exactly `(hK : CochainComplex.IsKFlat K)`, using the recorded predicate.
- Flatness of every term is `(hflat : ∀ p : ℤ, exactFunctor _ _
  (@MonoidalCategory.tensorRight _ _ (monoidalCategory R) (K.X p)))`.
  This states exactly the node's parenthetical definition: tensoring on the right with
  `K.X p` preserves finite limits and finite colimits. No new flatness predicate is defined.
  The existing `SheafOfModules.IsFlat` has equal site object and morphism universes;
  here its underlying exactness expression is written directly to retain both universes.
- The changed complex is `changeOfRingsComplex φ K`. Its terms are definitionally the
  recorded `changeOfRings φ (K.X i)` and its differentials are the recorded
  `changeOfRingsHom φ (K.X i) (K.d i j)`.
- The first conclusion is `CochainComplex.IsKFlat (changeOfRingsComplex φ K)`.
- The second conjunct quantifies over every integer p and states exactness of tensoring
  over S with `(changeOfRingsComplex φ K).X p`, precisely flatness of every changed term.

Dependency declarations read and used:

- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`, whose body tests acyclicity
  of `mapBifunctor F K (curriedTensor _)` against every acyclic F.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: `SheafOfModules.changeOfRings`
  and `changeOfRingsHom`, with their full signatures; the construction uses these verbatim.
  The sheaf tensor is the source `SheafOfModules.monoidalCategory`.
- The new `Sheaf.Algebra.Homology.ChangeOfRingsComplex` supplies the missing termwise object.
- Proof imports cover every recorded proof dependency: Mathlib's
  `SheafOfModules.restrictScalars` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`;
  `CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules`;
  `PresheafOfModules.sheafification` in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
  `PresheafOfModules.existsUnique_bilinear_sheafification_extension` in
  `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`;
  and `CochainComplex.mapBifunctor` in `Mathlib.Algebra.Homology.BifunctorShift`.
  The proof docstring retains all five DAG proof steps.

Edge cases checked: zero complex, zero target ring, identity coefficient map, empty site,
negative degrees and complexes unbounded in both directions. Nothing asserts a nonzero ring,
a nonempty site, boundedness, or flatness of S as an R-module. Separate site universes are
retained, with module/ring universe `max u v`, just as in the K-flat dependency.
The auxiliary construction has real terms and differential data; only the named proofs
of shape and square-zero are postponed. They do not select an unknown object.

Sources read: the local Stacks `sites-cohomology.tex`, lemma-pullback-K-flat (Tag 0G7E),
and `sites-modules.tex`, lemma-flat-change-of-rings (Tag 05V4). The source agrees with the
node. No statement correction or disputed statement.

Searches performed (full search-service results are also recorded in searches.jsonl):

- `leanfinder`: `Change of rings preserves K-flat complexes of sheaves of modules with flat terms`: 8 hits; Module.Flat.of_flat_tensorProduct, Module.Flat.iff_flat_tensorProduct, Module.Flat.trans, ModuleCat.preservesFiniteLimits_extendScalars_of_flat, Module.flat_iff_of_isLocalization, Module.Flat.iff_lTensor_preserves_shortComplex_exact, Module.Flat.iff_rTensor_preserves_shortComplex_exact, Module.Flat.isBaseChange.
- `loogle`: `SheafOfModules.changeOfRings, CochainComplex.IsKFlat`: 0 hits; .
- `grep`: `IsKFlat|changeOfRings`: 15 hits; Mathlib/Algebra/Category/ModuleCat/Pseudofunctor.lean, Mathlib/Algebra/Category/ModuleCat/Differentials/Basic.lean, Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean, Mathlib/Algebra/Category/ModuleCat/Presheaf.lean, Mathlib/Algebra/Category/ModuleCat/ChangeOfRingsExact.lean, Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafify.lean, Mathlib/Algebra/Category/ModuleCat/EnoughInjectives.lean, Mathlib/Algebra/Category/ModuleCat/Presheaf/ChangeOfRings.lean.
- `leansearch`: `Termwise extension of scalars cochain complex sheaves modules`: unavailable: service unavailable: Internal Server Error.
- `leanfinder`: `Termwise change of rings cochain complex of sheaves of modules`: 8 hits; CochainComplex.HomComplex.instModuleCochain, SheafOfModules.restrictScalars, CochainComplex.HomComplex.Cochain.shiftLinearMap, SheafOfModules.over, CochainComplex.HomComplex.Cocycle.instModule, CochainComplex.HomComplex_X, CochainComplex.HomComplex, CochainComplex.HomComplex.Cochain.shiftLinearMap_apply.
- `grep`: `changeOfRingsComplex|extendScalars.*Complex`: 0 hits; .

The module-only results concern flat ring modules, restriction of scalars, or Hom complexes,
not this theorem or the missing construction. Direct `rg` searches of Mathlib, upstream
`WeilConjectures`, project `lean/Sheaf`, `dag/lean_names_upstream.json`, and the DAG found no
matching theorem or general-site complex constructor. The exact item-id upstream search
had no hits. `blueprint_refs.py search "change of rings"` found five unrelated blueprint
nodes. Existing derived-change modules take a supplied functor E with object/map formulas;
the topological tensor-pullback complex additionally performs inverse image and cannot
serve as a general-site coefficient-change constructor.

## New nodes

`def-pur-change-of-rings-complex` defines termwise coefficient change for general-site
cochain complexes. Its source is the coefficient-change specialization of Tag 0G7E.
It reuses `changeOfRings` and `changeOfRingsHom` and the Mathlib cochain complex type.
The two named auxiliary theorems assert shape and square-zero, with full natural-language
proofs and `sorry`; the definition supplies every data field explicitly. No chosen functor,
extra compatibility hypotheses, or unknown existence witness enters the main statement.
The LeanSearch attempt was unavailable; LeanFinder and Mathlib grep found no matching
construction. The DAG, upstream and project searches above exclude an existing general-site
node or declaration. The new node records the actual search-service output summaries.

Validation: both delivered files compiled cleanly using scompile.py on the server,
with nice 19, two threads and 60 seconds per file. No local compiler was used.

## Second reading by NK

I independently read the node, its Stacks source places, the dependency declarations, and both
Lean files. The node's objects and hypotheses match as follows:

- The site `(C, J)` and its category/sheafification instances are rendered by the implicit
  `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}` and the three instances on
  `J`; the ring-sheaf forgetful composition is the required `CommRingCat` to `RingCat`
  composition at universe `max u v`.
- The two sheaves and coefficient map are exactly `{R S : Sheaf J CommRingCat.{max u v}}`
  and `(φ : R ⟶ S)`. No flatness, nonzero, characteristic, or nonempty-site hypothesis is
  added.
- `K` is an unrestricted integer-indexed `CochainComplex` of `R`-module sheaves. Its
  K-flatness is `hK : CochainComplex.IsKFlat K`, whose dependency definition tests every
  acyclic complex and the total tensor complex. Its termwise flatness is exactly
  `hflat : ∀ p : ℤ, exactFunctor _ _ (tensorRight (K.X p))`, preserving finite limits and
  finite colimits, as in the node's parenthetical functor formulation.
- The auxiliary definition `SheafOfModules.changeOfRingsComplex φ K` has terms
  `changeOfRings φ (K.X i)` and maps `changeOfRingsHom φ (K.X i) (K.d i j)`; its named
  `changeOfRingsComplex_shape` and `changeOfRingsComplex_comp` theorems supply the cochain
  shape and square-zero fields. Thus it is the node's termwise `K ⊗_R S`, rather than a
  private complex or a supplied arbitrary functor.
- The conjunction's first clause is
  `CochainComplex.IsKFlat (changeOfRingsComplex φ K)`. Its second clause quantifies every
  `p : ℤ` and is exactness of `tensorRight` with the changed term over `S`, exactly the
  assertion that all changed terms are flat `S`-modules.

The conclusion order and quantifier order are unchanged. The source Lemma 21.18.1 (Tag 0G7E)
assumes precisely K-flatness and flat terms and concludes K-flatness and flat terms after
pullback; the identity-topos coefficient-change specialization uses the displayed `- ⊗_R S`.
Tag 05V4 supplies the termwise flatness step and does not assume that `R → S` is flat.

Edge cases checked: `p` ranges over all integers (including negative degrees), so boundedness
and `n = 0` are not imposed; a zero complex and zero target ring are admitted; an empty site is
not excluded; the identity map is admitted; no characteristic or nonzero condition appears.
The single universes `u, v` and `max u v` retain the separate site object/morphism universes and
do not exclude the source's cases.

Searches were repeated independently. `loogle` for `SheafOfModules.changeOfRings` returned no
identifier. `leanfinder` for a termwise coefficient-changed K-flat sheaf complex returned only
presheaf tensor and unrelated sheaf/cohomology declarations. Grep over Mathlib, upstream
`WeilConjectures`, and project `lean/Sheaf` found no general-site `changeOfRingsComplex` or
matching preservation theorem; the hits were restriction/extension scalar ingredients,
finite-module flatness, or specialized pullback/derived modules. The recorded `leansearch`
attempt was unavailable, and the blueprint search for “change of rings” found only unrelated
nodes. The existing `SheafOfModules.IsFlat` was read: it has equal site and module universes,
so the theorem correctly writes the exactness predicate directly to retain `u` and `v`.
The existing `CochainComplex.IsKFlat`, `changeOfRings`, `changeOfRingsHom`, and
`monoidalCategory` declarations were used verbatim.

No mismatch was found and no file or node statement was changed. The new
`def-pur-change-of-rings-complex` is necessary and its data is explicit; only its named shape
and composition proofs are postponed. Both sibling modules compiled with `scompile.py` on the
server, with only the permitted `sorry` declarations and no other warnings.
