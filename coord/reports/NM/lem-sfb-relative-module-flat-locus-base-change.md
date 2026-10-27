## Worker report

The single new module `Sheaf.AlgebraicGeometry.RelativeModuleFlatLocusBaseChange` states
`AlgebraicGeometry.isOpen_moduleFlatLocus_and_baseChange`, with its entire proof `sorry`.
It is the complete module version of Stacks Project, More on Morphisms, Tag 05VJ,
`lemma-base-change-criterion-flatness-fibre` (local source `more-morphisms.tex`,
lines 4701–4764). No definition, helper theorem, dependency repair, or statement
correction is introduced. The node copy changes only `lean`.

Hypotheses and conclusions, matched with the unchanged node:

| Node clause | Lean rendering |
| --- | --- |
| Schemes S, X, Z | `{S X Z : Scheme.{u}}` with explicit `universe u` |
| Morphisms p:X→S, a:Z→S, f:X→Z | `(p : X ⟶ S) (a : Z ⟶ S) (f : X ⟶ Z)` |
| a composed with f equals p | `(hf : f ≫ a = p)`; categorical composition is written in diagrammatic order |
| p locally of finite presentation | `[LocallyOfFinitePresentation p]` |
| a locally of finite type | `[LocallyOfFiniteType a]`; no quasi-compactness is imposed |
| O_X-module M | `(M : X.Modules)` |
| M quasi-coherent | `[SheafOfModules.IsQuasicoherent.{u} M]` |
| M of finite presentation | `[SheafOfModules.IsFinitePresentation.{u} M]`, the existing local finite free presentation predicate |
| M flat over S through p | `(hflat : M.IsFlatOver p)`, the recorded affine-local predicate |
| M_x with scalar action through f | `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M`, then `(ModuleCat.restrictScalars (f.stalkMap x).hom).obj` |
| U is exactly the relative flat locus | The set comprehension `{x : X | Module.Flat (Z.presheaf.stalk (f x)) (...)}` occurring verbatim in the openness clause and right-hand inverse image |
| U open | `IsOpen` of that comprehension, the first conjunct |
| Every scheme S' and arbitrary v:S'→S | `∀ (S' : Scheme.{u}) (v : S' ⟶ S), ...`, with no extra condition on v |
| X'=X×_S S', Z'=Z×_S S' | `pullback p v`, `pullback a v` |
| Projection b:X'→X | `pullback.fst p v` |
| Canonical induced f':X'→Z' | `pullback.map p v a v f (𝟙 S') (𝟙 S) ...`; its first compatibility proof is exactly hf in the orientation required by pullback.map, and its second is the identity square |
| M'=b* M, the actual tensor pullback | `((Scheme.Modules.tensorPullback (pullback.fst p v)).obj M)` |
| Flatness of M' at x' over O_{Z',f'(x')} | The left comprehension uses `(pullback a v).presheaf.stalk (f' x')`, restriction of scalars along `(f'.stalkMap x').hom`, and the stalk functor on `pullback p v` applied to M' |
| Equality U'=b⁻¹(U) | Equality of that left comprehension with `(pullback.fst p v) ⁻¹'` the original comprehension |
| No flatness condition on p, a, f, v; no Noetherian hypothesis | There are no such binders or instances. `hflat` concerns the module M, not the morphism p. |

All variables and universes are explicitly bound; both `autoImplicit` and
`relaxedAutoImplicit` are false. The shared universe u is the ordinary category
`Scheme.{u}` convention and includes all base changes in that category; unlike
an independent smaller universe, it allows the identity base change. No `let`
or `show` binder, local notation, arbitrary comparison map, or chosen object is
inserted in the signature. The two short proofs supplied to `pullback.map`
only verify commutativity of its specified diagram and introduce no hypothesis.

Recorded statement dependencies used (full signatures and docstrings read):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms `Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (only the locally finite type clause is needed).
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  the exact `SheafOfModules.IsQuasicoherent` predicate. Its combined
  `IsQuasiCoherentFiniteType` and its coherence predicate are not imposed: the
  node calls for quasi-coherence and finite presentation, not Stacks coherence.
- `def-weil-pbc-module-finite-type-presentation`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`,
  `SheafOfModules.IsFinitePresentation` (the latter is publicly available through
  `CoherentFiniteType`).
- `def-pc-scheme-module-flat-over`:
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `def-weil-pbc-module-stalk`:
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`,
  `PresheafOfModules.moduleStalkFunctor`. For scheme sheaves the recorded node's
  note explicitly prescribes `RingedSpace.moduleStalkFunctor`, imported from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`. Its stalk carrier and
  scalar action are precisely the specialization of that presheaf construction;
  no second stalk definition is made.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.map`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies their existence for schemes.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly imports
  the upstream explicit `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
  This is the actual inverse-image/sheafified extension-of-scalars construction.

The statement-dependency modules are public imports; modules for stated proof
dependencies are plain imports unless already public statement imports. These
include the upstream closed `locallyOfFinitePresentation_of_comp` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` and the
recorded affine sections, open flat locus, pointwise module flatness, stalk
pullback, preservation of quasi-coherence/finite presentation/relative flatness
modules. Mathlib proof leaves are imported from AffineScheme, Modules.Tilde,
Flat.Localization, Fiber, and Morphisms.QuasiSeparated (finite presentation/type
permanence modules are already public). The currently unstated proof-only
nodes `lem-sfb-fibrewise-module-flatness-criterion`,
`lem-sfb-flat-residue-fibre-square` remain proof-plan citations in the docstring; no unstated interface is needed to
type this theorem. The first step's `lem-a1-map-over-base-finite-presentation`
is closed upstream and its module is imported, despite its lack of a lean record.
Every node proof step is carried into the theorem docstring, including the zero
stalk case and quasi-coherence of the fibre module used for pointwise descent.

Edge cases checked against Tag 05VJ and the exact Lean type:

- Empty X or an empty base-changed source: both set comprehensions are empty;
  the openness and equality clauses remain meaningful, with no nonemptiness binder.
- Zero module, or a zero stalk at an individual point: the zero module is flat
  over every ring, so such points belong to the locus. No nonzero-stalk condition
  occurs. The proof docstring handles this case separately in the fibrewise test.
- Zero module with a nonflat p is permitted. Thus module flatness over S has not
  been replaced by flatness of p.
- Identity v: the canonical chosen pullback and its projection give the expected
  equality after the canonical identity comparison, without requiring the chosen
  pullback scheme to be definitionally X.
- Nonflat v, including a closed immersion into the parameter scheme, is allowed.
  The statement uses no flat-base-change instance for v.
- Identity f need not make U all of X: for S=Spec(k), X=Z=Spec(k[t]) and
  M=O_X/(t), M is finitely presented and flat over k, while its flat locus over
  X is D(t), with zero stalks away from t. This distinguishes the module
  statement from structure-sheaf flatness and tests the scalar restriction.
- No Noetherian or characteristic restriction, and no finite rank restriction,
  enters the type. The local finite presentation/type hypotheses are exactly
  those in the source and the node.

Searches for an existing statement:

1. `msearch.py ... leanfinder` with query
   "The flat locus of a finitely presented quasi coherent sheaf flat over S is open
   and commutes with arbitrary base change of S": 8 hits, headed by
   `AlgebraicGeometry.Flat.isStableUnderBaseChange` and
   `AlgebraicGeometry.UniversallyOpen.of_flat`. These concern morphisms already
   flat or ascent, not this module locus equality.
2. `msearch.py ... loogle` with query `Module.Flat, Module.FinitePresentation`:
   6 hits, including `Module.Flat.projective_of_finitePresentation`,
   `Module.FinitePresentation.isBaseChange_map`, and
   `Module.isLocallyConstant_rankAtStalk`. None states this relative scheme result.
3. `msearch.py ... grep` with query
   `flatLocus|flat_locus|isOpen.*flat|flat.*isOpen`: 9 Mathlib hits in
   UniversallyOpen, Flat, FlatMono and FlatDescent, concerning flat morphisms.
4. `rg -n 'flatLocus|flat_locus|relative_module_flat|relativeModuleFlat'` in both
   `lean/WeilConjectures` and `lean/Sheaf`: only
   `Sheaf.AlgebraicGeometry.RelativeFlatLocusBaseChange`,
   `AlgebraicGeometry.isOpen_flatLocus_and_baseChange`, was a candidate. Its full
   source was read: it assumes `[Flat p]` and concerns `(f.stalkMap x).hom.Flat`,
   the structure sheaf specialization Tag 05VK, not arbitrary M of Tag 05VJ.
5. `rg -n 'lem-sfb-relative-module-flat-locus-base-change' lean/WeilConjectures`:
   no existing declaration attached to this item. DAG search for
   `isOpen_flatLocus_and_baseChange|RelativeFlatLocusBaseChange` confirms the
   candidate belongs to `lem-sfb-relative-flat-locus-base-change`.

Validation: the module compiles cleanly through the required `scompile.py`,
both as a sandbox file (4.6 seconds) and under its library module name
(3.9 seconds), against the live published build. An initial inference failure
on `IsFinitePresentation` was fixed by making its already intended module
universe explicit as `.{u}`. No mathematical assumption or dependency changed.
No statement dispute, node fault, or source correction was found.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
