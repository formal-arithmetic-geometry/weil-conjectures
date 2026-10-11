## Worker report

The module `Sheaf.Paper.FiniteSurjectiveCoherentGenericSupport` states
`AlgebraicGeometry.Scheme.exists_coherent_pushforward_support_eq_range`, with only `sorry`
as proof. It introduces no definitions. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- Schemes and morphisms: `{X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X)`.
- Finite and surjective f: `[IsFinite f] [Surjective f]`.
- Locally Noetherian X: `[IsLocallyNoetherian X]`.
- Integral closed subscheme: `[IsClosedImmersion i] [IsIntegral Z]`.
- Generic point of the image: `(ξ : X)` and
  `hξ : closure ({ξ} : Set X) = Set.range i.base`. A closed immersion identifies Z with
  this range. In particular ξ belongs to the range, so no separate membership hypothesis
  is needed. On an integral scheme this is precisely its generic point.
- Existence of an O_Y-module: `∃ F : Y.Modules`.
- Coherence: `RingedSpace.IsCoherent Y.toRingedSpace F`.
- The direct image is `(Modules.pushforward f).obj F`. Mathlib's
  `Modules.pushforward_obj_obj` states sectionwise equality with F on the inverse-image
  open; it is definitional equality, so no extra hypothesis or existential choice is needed.
- Exact support equality: the set
  `{x : X | ¬ Subsingleton (((Modules.pushforward f).obj F).presheaf.stalk x : Type u)}`
  equals `Set.range i.base`. For abelian groups, a zero stalk is exactly a subsingleton
  carrier. This is the project's inline support convention, not a new support predicate.
- Annihilation of the generic stalk: every scalar a in
  `IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk ξ)` satisfies `a • s = 0`
  for every s in the canonical module stalk of the same pushforward. This is equivalent
  to m_ξ times the stalk being zero. No finite-dimensionality or residue-field isomorphism
  is added to the conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `def-pc-module-pullback` records `Sheaf.AlgebraicGeometry.TensorPullback` and
  `Scheme.Modules.tensorPullback`. This theorem only uses its direct-image side, already
  provided by `Mathlib.AlgebraicGeometry.Modules.Sheaf`, `Scheme.Modules.pushforward`;
  the dependency module's docstring expressly refers to that same sectionwise pushforward.
  Importing the tensor-pullback implementation itself would be an unused import.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: support is explicitly its inline
  nonzero-stalk locus. Its proper-support predicates are not used here and are not imported.
- `Sheaf.Topology.PresheafModuleStalkFunctor`: `PresheafOfModules.moduleStalkFunctor` was
  read. As its recorded note and the stage brief require for scheme modules, the statement
  uses `Sheaf.Algebra.Homology.ModuleStalkFunctor`,
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, whose object is the same stalk
  carrier equipped with the canonical module action. No stalk notion is redefined.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` was read; the statement
  needs the maximal ideal of the existing structure-sheaf stalk, not the quotient field,
  so uses `IsLocalRing.maximalIdeal` directly.

Edge cases checked: integral Z is nonempty; hence the hypotheses exclude empty X and,
by surjectivity, empty Y. The zero module is allowed in the existential domain, but cannot
satisfy the support equality, since the range of i is nonempty. No quasi-compactness,
Noetherian (as opposed to locally Noetherian), separatedness, characteristic, or field
hypothesis is imposed. One explicit universe u covers the schemes, module carriers and
stalk carriers. The scalar-action clause concerns the O_X-stalk action, not an action of
O_Y or an independently supplied field. ξ is not required to be a closed point.

Source checked at [Stacks 01YO](https://stacks.math.columbia.edu/tag/01YO), Lemma 30.13.1
and its proof. The local literature/stacks-project/coherent.tex file is absent on this
machine, so the original tag was opened online. It agrees with the node and the Lean;
there is no statement correction or disputed statement.

Searches:

- `msearch.py ... leansearch` with query "A finite surjective morphism admits a coherent
  module with pushforward supported on an integral closed subscheme and generic stalk
  annihilated by the maximal ideal": service unavailable, Internal Server Error.
  No verdict is inferred from that unavailable service.
- `msearch.py ... leanfinder` with query "finite surjective morphism coherent sheaf
  pushforward support integral closed subscheme generic stalk annihilated maximal ideal":
  eight hits, chiefly Scheme.IdealSheafData.support_map, Hom.support_ker and closed
  subscheme range/support identities; none asserts existence of the coherent module.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite, Scheme.Modules.pushforward"`:
  zero hits, unknown identifier for the unqualified Scheme.Modules.pushforward query.
  The full declaration and docstring were read directly in Modules/Sheaf.lean.
- `msearch.py ... grep "coherent|support" AlgebraicGeometry/Modules`: five hits,
  all concerning quasi-coherence of tilde; no theorem matching this node.
- `rg` in WeilConjectures and lean/Sheaf for
  `finite.*surjective.*coherent|exists_coherent_pushforward_support_eq_range|` followed
  by the full node id: only a citation in FiniteSurjectiveAffineTargetNoetherian.lean.
  The declaration-name search in dag/lean_names_upstream.json also gave no match.
- Read the existing coherence, module stalk, support, tensor pullback and scheme-module
  pushforward modules to avoid duplicate definitions.

The final module compiles on the server without errors or warnings. The docstring carries
all six natural-language proof steps and their DAG inputs for stage 3.

## Second reading by C1

Independent second reading: opened the node and delivered Lean together, all eleven
statement-dependency nodes, and the defining declarations. Read Stacks 01YO and Section
01YN online, and the original `coherent.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex
(label `lemma-finite-morphism-Noetherian`). The local Stacks source is absent.
There is no ambient base, field, separation, or global Noetherian assumption in this
source section. The node and Lean agree with the source.

Object, hypothesis, and conclusion checklist (every verdict: exact):

1. Schemes X, Y and Z: `{X Y Z : Scheme.{u}}`, Mathlib's schemes extending
   locally ringed spaces with local affine charts. Morphisms f and i:
   `(f : Y ⟶ X) (i : Z ⟶ X)`, in the scheme category.
2. Finite f: `[IsFinite f]`; the recorded class extends `IsAffineHom f` and
   requires finite induced ring maps on every affine open. No merely integral or
   locally finite type substitute is used.
3. Surjective f: `[Surjective f]`; its field is `Function.Surjective f` on points.
4. Locally Noetherian X: `[IsLocallyNoetherian X]`, Noetherian section rings on
   affine opens, equivalent to the node's affine-cover definition. Global
   Noetherianity and quasi-compactness are not required.
5. Integral closed subscheme: `[IsClosedImmersion i] [IsIntegral Z]`.
   The immersion class requires a closed embedding and surjective stalk maps;
   integrality includes nonemptiness and domains on nonempty opens, equivalent
   to the node's affine-open condition. Neither X nor Y is assumed integral.
6. Generic point of this subscheme: `(ξ : X)` and
   `hξ : closure ({ξ} : Set X) = Set.range i.base`. Since ξ belongs to its
   closure, this implies membership in i(Z); the closed embedding identifies
   that closure with all of Z. Thus no point outside Z or nongeneric point is
   admitted. This is exactly the node's stated closure condition.
7. Existential sheaf: `∃ F : Y.Modules`, where Mathlib defines `Modules` as
   `SheafOfModules.{u} Y.ringCatSheaf`, the category of O_Y-modules.
8. Coherence: `RingedSpace.IsCoherent Y.toRingedSpace F`, whose definition is
   finite type together with finite-type kernels of all maps from finite free
   modules on every open. It is the dependency's coherence definition.
9. Direct image of that same F: `(Modules.pushforward f).obj F`. Read its
   definition and `pushforward_obj_obj`: sections on U are definitionally
   sections of F on f inverse-image U; restriction and scalar maps are the
   canonical ones. The module-pullback dependency's tensor pullback is not
   needed to state its existing right-adjoint direct image.
10. Exact support equality: `{x : X | ¬ Subsingleton
    (((Modules.pushforward f).obj F).presheaf.stalk x : Type u)} = Set.range i.base`.
    Read `Modules.HasSupportProperOver`: it uses precisely this nonzero-stalk
    locus. Subsingleton for an additive group is equivalent to the zero object.
    No properness predicate or reduced-subsheme choice is added here.
11. Maximal-ideal annihilation: for every `a` in
    `IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk ξ)` and every `s`
    in `(RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
    ((Modules.pushforward f).obj F)`, `a • s = 0`. Read both the general
    presheaf stalk dependency and the ringed-space stalk functor. Their carriers
    are the same Mathlib abelian-group stalk; its canonical action is the
    Mathlib module structure induced by multiplication of germs. The residue
    field dependency is the quotient of this same structure-sheaf stalk by
    its maximal ideal. The formula is exactly m_ξ times this stalk equals zero,
    without extra dimension or residue-field-isomorphism assertions.

The quantifiers put the choice of F after all scheme, map and generic-point data;
all conclusions concern that same F. No extra instances or hypotheses occur.

Edge cases: an integral Z is nonempty, so empty Z is excluded by the source itself;
its map to X excludes empty X, and surjectivity then excludes empty Y. The zero
module remains in the existential domain but cannot satisfy nonempty support.
No index family or integer n appears; the coherence dependency includes n = 0
via its universal natural-number binder. No restriction on characteristic occurs.
Universe u is explicit and arbitrary and shared by schemes, their sheaves and stalks,
as required by Mathlib's scheme category. There are no independent test-object
universes, unbound variables, or hidden field or domain assumptions on X.

Independent searches with different words from the worker:

- `msearch.py ... leanfinder "coherent module on finite covering prescribed
  irreducible support killed by generic maximal ideal"`: eight hits, including
  `Module.support`, `Module.notMem_support_iff`, `ModuleCat.Tilde.exists_const`,
  and section-extension lemmas. These concern module support or sections, not
  the coherent sheaf existence statement of this node.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Modules.pushforward"`:
  twelve hits for the existing pushforward, its adjunction, additivity and
  composition. The exact direct-image notion exists and is used; none of
  these hits states the target existence theorem.
- `msearch.py ... grep "maximalIdeal|annihilator" AlgebraicGeometry/Modules`:
  zero hits. Direct rg of source WeilConjectures and project Sheaf for
  `exists_coherent_pushforward|finite.*surjective.*coherent|prescribed.*support|
  generic.*annihilat` found only the citing affine-target module and unrelated
  PerfectSupportedMapLift material. Broader coherent/support searches found
  tilde quasi-coherence, ideal-sheaf support and section zero loci, not this
  statement. The worker's LeanSearch outage remains explicitly recorded;
  no successful-search verdict is inferred from it.

No new definition nodes or dependency modules are present or needed. No statement
correction is present or needed. All six proof steps and their DAG inputs are in
order in the theorem docstring, including the nonzero generic stalk needed for
support equality. There is one theorem with only `sorry`, no definitions or local
notation, standard namespace and imports, and all lines are at most 100 characters.
The node's `lean.statement` is byte-for-byte the signature before `:=`.

Mismatches found: none. Changed only this report by appending the independent
second reading; retained the Lean module and node record unchanged.
Single-file server compilation with the mandated scompile command passed in
1.8 seconds, with no errors or warnings. The initial invocation used a relative
path from the repository instead of the sandbox; rerunning with the absolute
sandbox file path resolved that invocation error.
