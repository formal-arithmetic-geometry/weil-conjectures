## Worker report

Module: `Sheaf.AlgebraicGeometry.EquivariantCoherentSubmoduleExtension`.
Declaration: `AlgebraicGeometry.EquivariantCoherent.exists_equivariant_coherent_submodule_extension`.
This is one theorem with `sorry`; no definition or additional theorem is introduced.
The natural-language statement and all proof steps remain unchanged. Three already
landed definition nodes are added to `stmt_deps`: `def-a1-scheme-groupoid-laws`,
`def-sfb-scheme-groupoid-module`, and `def-sfb-equivariant-coherent-gzero`.
The first two were already proof dependencies. The third supplies the action
presentation and the coherent subcategory, avoiding duplicate definitions.

Clause-by-clause rendering:

- Field F: `{F : Type u} [Field F]`. No characteristic, perfection or algebraic
  closure assumption is present.
- Group scheme G over F: `G : Over (Spec (.of F))` and `[GrpObj G]`.
  Affineness is `[IsAffine G.left]`; finite type is the pair
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Separated finite-type F-scheme Y: `Y : Over (Spec (.of F))`,
  `[IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`.
- The action is `[ModObj G Y]`. This includes the multiplication and identity
  action laws, rather than an arbitrary scheme map.
- `DY : ActionGroupoidModel G Y` presents precisely the action groupoid.
  Its source, target, identity, inverse and composition are pinned by the existing
  definitions and `group_coordinate`; this is presentation data, not an extra
  geometric assumption. The same applies to `DU` for the restricted action.
- The invariant open is `j : U ⟶ Y`, `[IsOpenImmersion j.left]`, with the
  restricted action `[ModObj G U]` and `[IsModHom G j]`. For an open immersion
  the action on U making j equivariant is unique. Equivariance says that
  G times U maps into U; the inverse action gives the reverse inclusion in
  `a⁻¹(U) = G times U`. Thus this describes exactly invariant opens, and does
  not impose smoothness, reducedness, or pointwise-only invariance.
- The quasi-coherent linearized ambient module is
  `M : Scheme.GroupoidModule (source G Y) (target G Y)
    (identityArrow G Y) (inverseArrow G Y) DY.comp DY.laws`.
  Its fields are `moduleObj`, `quasiCoherent`, `beta`, `unit`, and `cocycle`.
  In particular `beta` has direction `a^*M ≅ pr₂^*M`; its equations are the
  existing normalized pullback equations. M is not wrapped in `Coherent`.
- The prescribed coherent linearized module N is `N : Coherent DU`; coherence
  is exactly `RingedSpace.IsCoherent`, including the finite-type kernel clause,
  not just finite presentation or quasi-coherence plus finite type.
- Its prescribed inclusion into the restriction of M is
  `n : underlying N ⟶ (Scheme.Modules.tensorPullback j.left).obj M.moduleObj`,
  with `[Mono n]`. This is an actual sheaf subobject, not a sectionwise-submodule
  surrogate or only an isomorphism class without its ambient inclusion.
- `hn` says that n intertwines the given linearizations. Written with
  `a_U : G times U → U`, `r : G times U → G times Y`, it says
  `a_U^*n ; C_a ; r^*beta_M ; C_p⁻¹ = beta_N ; p_U^*n`, where C_a and C_p
  are `mixedCompComparison`, normalized by `tensorPullbackSectionComp`.
  `pullbackIso` transports the existing opaque groupoid pullback interface to
  the same actual tensor-pullback functor, without a new choice.
  The quantified `ha` and `hp` are respectively the equivariance equality
  for j and naturality of the product projection. Both are derivable from
  `[IsModHom G j]` and the Cartesian monoidal product; they are not extra
  hypotheses or an empty test family. A separate sandbox compile checks this.
- The extension is `L : Coherent DY` and an equivariant map `l : L.obj ⟶ M`;
  `Mono l.val` makes its underlying module a submodule of M. A morphism of
  `Scheme.GroupoidModule` is exactly a module map commuting with beta.
- Restriction equals the given linearized submodule through an isomorphism
  `e : j^*(underlying L) ≅ underlying N`, with `IsPullbackMap j L N e.hom`.
  This isomorphism intertwines the specified, canonically restricted
  linearizations. The equality `j^*l = e.hom ≫ n` makes the two monomorphisms
  into the fixed ambient sheaf represent the same subobject. No arbitrary
  unrelated isomorphism suffices.
- There is no coherence assumption on M, nor smoothness, reductivity,
  connectedness or reducedness assumption on G. `u` is explicit and arbitrary;
  no independent smaller universe is used for any test object.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`; on `Over (Spec F)` this is
  exactly the group-scheme notion recorded by `def-sc-group-scheme`. The
  interpretation is also documented in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and its morphisms (`def-pc-scheme`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact` (`def-weil-finite-type-morphism`).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `.Separated`: `IsSeparated`
  (`def-weil-proper-morphism`); no `IsProper` hypothesis is imposed.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes
  `RingedSpace.IsCoherent` from `WeilConjectures.AlgebraicGeometry.Coherent`, and
  `SheafOfModules.IsQuasicoherent` (`pqf-def-coherent`). These exact declarations
  are used through the coherent subcategory and groupoid-module fields.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp`,
  `tensorPullbackSectionId` (`def-pc-module-pullback`), used through the
  groupoid-module and mixed-comparison interfaces. The actual tensor
  construction was read in `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`
  (`def-weil-open-immersion`).
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `Scheme.IsGroupoid`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidModule`: `Scheme.GroupoidModule`,
  `groupoidModulePullback`, `groupoidModuleUnitLaw`, `groupoidModuleCocycleLaw`,
  `GroupoidModule.Hom` and its category instance.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`: `source`, `target`,
  `identityArrow`, `inverseArrow`, `ActionGroupoidModel`, `Coherent`, `underlying`,
  `pullbackIso`, `linearization`, `mixedCompComparison`, `IsPullbackMap`.
  No new G-zero definition is used or introduced.

All recorded proof dependencies with a Lean module are plain imports:
`GroupoidModuleLimitsColimits`, `CoherentKernelCokernelLocallyNoetherian`,
`ModuleFiniteTypeAffineGenerators`, `QuasiCoherentModuleColimitEvaluation`.
The upstream closed `Flat.of_field` theorem is imported from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`.
Mathlib proof leaves are imported through that module, `Morphisms.Affine`,
`Noetherian`, `Morphisms.FinitePresentation`, `ModuleCat.FilteredColimits`,
and `Limits.ConcreteCategory.Basic`, with other morphism-permanence declarations
already public through the statement imports. The two genuine proof-only nodes
`lem-sfb-cartesian-groupoid-pushforward-adjunction` and
`lem-sfb-flat-noetherian-groupoid-coherent-approximation` have no recorded module
in the read clone; no import is invented for an unstated theorem. Neither is
needed to type this theorem, and their full roles are preserved in its proof docstring.

The current blueprint was read through `literature/blueprint/latest/`,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`:
`sk-thm-sf-ctf-stability-direct-images.md` and its `.proof.md`, clause (3).
It states the direct-image target reached through this supporting extension node;
this item is not the blueprint unit statement.

Source reading: `literature/stacks-project/groupoids.tex`, definition-groupoid-module,
lemma-pushforward (09VH), lemma-colimits (077R), lemma-abelian (077S), and
lemma-colimit-coherent (07TU); `coherent.tex`,
lemma-coherent-Noetherian-quasi-coherent-sub-quotient (01Y1). The result remains
explicitly an agent assembly, not attributed as an exact Stacks theorem.

Edge cases checked mathematically before and after writing: U empty (zero extension),
U=Y (the given coherent submodule), Y empty, M=0, N=0, trivial group scheme,
nonreduced finite group schemes such as alpha_p, and arbitrary characteristic.
For G_m acting on A¹ and M=F[x,x⁻¹], coherent restricted lattices such as x⁻ⁿF[x]
are allowed: there is no finite-type requirement on the ambient M. The docstring
retains the nonempty-filtered-index handling for empty covers and generator lists.
No statement fault or STATEMENT-DISPUTED issue was found.
The separate module-mode probe `scratchpad/EquivarianceComparisons.lean`
compiled cleanly in both contexts (1.4 seconds each). It derives the target
comparison by applying `congrArg` to `IsModHom.smul_hom (A := G) (f := j)`,
and derives the source comparison from naturality of `snd`. Thus the universally
quantified comparisons in `hn` and `IsPullbackMap` have inhabitants in every case.
An initial probe used positional arguments for `smul_hom`; its actual implicit
argument interface was read and the probe corrected before the successful compile.

Searches:

- `msearch.py leanfinder`: "An equivariant coherent submodule on an invariant
  open extends inside a quasi-coherent module". Eight hits concerning
  `SheafOfModules.QuasicoherentData`, `IsQuasicoherent` and `ModuleCat.Tilde`;
  none is the equivariant extension theorem.
- `msearch.py loogle`: `"Coherent", "submodule"`. Zero hits.
- `msearch.py grep`:
  `(equivariant|lineariz).*(coherent|submodule)|(coherent|submodule).*(equivariant|lineariz)`.
  Zero Mathlib hits.
- `msearch.py leansearch`: "A coherent equivariant submodule of a restricted
  quasi-coherent sheaf on an invariant open extends to a coherent equivariant
  submodule on the whole scheme". Eight hits, ordinary open restriction and
  morphism facts; no equivariant extension theorem.
- `rg` in the exact live read clone's `lean/WeilConjectures` and `lean/Sheaf`:
  `lineariz|Lineariz|GroupoidModule|SchemeGroupoid`, and
  `equivariant.*extension|coherent.*extension|coherent_submodule`.
  These located the reused groupoid and equivariant-coherent infrastructure,
  ordinary finite-type extension, and unrelated linearizations; no exact theorem.
- `rg -n lem-sfb-equivariant-coherent-submodule-extension lean/WeilConjectures`:
  no declaration carrying this blueprint id.
- `rg -n submodule_extension|SubmoduleExtension` in both source roots and
  `dag/lean_names_upstream.json`: ordinary module/submodule extension only.
- `tools/blueprint_refs.py search equivariant coherent submodule`: zero blueprint
  nodes. A DAG search for `ActionGroupoidModel` located the existing
  `def-sfb-equivariant-coherent-gzero`; its declaration and full source were read.

Validation: the complete delivered module compiled cleanly through `scompile.py`
in both the sandbox and library-name contexts (1.6 seconds each). It has exactly
one `sorry` theorem, all variables and universes explicitly bound, no local notation,
no local instances, no new data definitions, and no lines longer than 100 characters.

## Second reading by Q49

This is a separate in-thread rereading of the node and completed signature, not
an independent-agent review: the dispatch brief explicitly prohibits starting
other agents, and assigns independent review to the maintainer.
The important mismatch to avoid was using `Coherent DY` for the ambient M;
the file correctly uses the unrestricted quasi-coherent `Scheme.GroupoidModule`.
I checked the directions of all four comparison arrows in `hn`: its left side
runs from a_U^*N through a_U^*j^*M to r^*a_Y^*M, then r^*p_Y^*M and p_U^*j^*M;
the right side runs first through beta_N. Thus n is equivariant for its given
linearization, rather than merely a mono of underlying modules. I checked that
`IsPullbackMap j L N e.hom` is correctly oriented from j^*L to N, and the final
commutative-inclusion equality preserves the given submodule. The group,
finite-type, separatedness and invariant-open hypotheses match one for one;
no properness, smoothness or reductivity has entered. Coherence is the complete
01BV predicate, and the unit/cocycle are the existing groupoid laws. The action
models are pinned to multiplication on every test scheme and impose no choice
of a different groupoid. No mismatch required changing the node statement.
