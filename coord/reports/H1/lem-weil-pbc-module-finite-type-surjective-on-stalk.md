## Worker report

The module `Sheaf.Topology.FiniteTypeSurjectiveNearStalk` states
`SheafOfModules.exists_surjective_neighbourhood_of_surjective_stalk`, with its proof
left as `sorry`. It introduces no new definition or node and changes only the item's `lean`.

Hypothesis and clause correspondence:

- Ringed space `(X, O_X)`: `X : TopCat.{u}` and
  `R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}`. This is a topological
  space with a sheaf of rings; no commutativity or local-ring assumption is imposed.
- Sheaves of modules and their morphism: `G F : SheafOfModules.{u} R`, `φ : G ⟶ F`.
  Mathlib's morphism has linear component maps and naturality for the semilinear
  restriction maps; these are exactly the dependency's structures.
- Point: `x : X`.
- Target of finite type: `[SheafOfModules.IsFiniteType.{u, u, u} F]`, the Mathlib predicate giving finite
  generating sections locally (not finite presentation and no finiteness on `G`).
- Surjective induced map on stalks: `hφ : Function.Surjective` of the image of
  `φ.val` under `PresheafOfModules.toPresheaf R.obj` and then
  `TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x`. Its domain and codomain are
  precisely `G.val.presheaf.stalk x` and `F.val.presheaf.stalk x`. Forgetting the
  module structure in this surjectivity predicate changes neither elements nor
  the induced map; the module structure is the one provided by the stalk dependency.
- Open neighbourhood: `∃ U : Opens X, x ∈ U ∧ ...`.
- Every open subset `W ⊆ U` and every section: `∀ W, W ≤ U → ∀ t : F.val.obj (op W)`.
- Open covering of `W`: `I : Type u`, `V : I → Opens X`, `hV : ∀ i, V i ≤ W`, and
  `(⨆ i, V i) = W`. A covering can always be indexed in the space's universe,
  e.g. by its points (choosing a lifting neighbourhood at each point), so this
  imposes no bound on the size of a cover needed for existence.
- Local lifts: `g : ∀ i, G.val.obj (op (V i))` and, for every `i`,
  `φ.val.app (op (V i)) (g i) = F.val.map (homOfLE (hV i)).op t`.
  The right side is exactly the restriction of `t` along the open inclusion.

Dependency declarations read and used:

- `def-weil-sheaf-of-modules-category`: Mathlib.Algebra.Category.ModuleCat.Sheaf,
  `SheafOfModules`, `SheafOfModules.Hom` and its category instance; underlying
  `PresheafOfModules.Hom` and `PresheafOfModules.toPresheaf` in
  Mathlib.Algebra.Category.ModuleCat.Presheaf.
- `def-weil-pbc-module-finite-type-presentation` clause (1):
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators,
  `SheafOfModules.IsFiniteType`, `LocalGeneratorsData` and `GeneratingSections`.
- `def-weil-pbc-module-stalk`: Mathlib.Topology.Sheaves.Stalks,
  `TopCat.Presheaf.stalkFunctor` and `stalk`, with `exists_germ_eq` and `germ_eq`
  read for the proof docstring; Mathlib.Algebra.Category.ModuleCat.Stalk,
  `PresheafOfModules.germ_ringCat_smul` and the ring-stalk module instance.
  All dependencies are Mathlib records and need no `lean` repair.

Edge cases checked before drafting: the empty space has no point `x`, so has no
instance of the premises; a zero target and zero generating family are included
by `IsFiniteType` and the proof's `n = 0` case; an empty `W` admits the empty cover,
with union bottom and no lifting equations; a zero source can satisfy the premise
only when the target stalk vanishes, and finite type then gives a neighbourhood
where the target vanishes. No field, characteristic, Noetherian or separation
hypothesis appears. Universe `u` is arbitrary and shared by the space, rings and
modules, with no small test-object quantification. In any common sufficiently
large universe it accommodates all three carriers.

Source checked: https://stacks.math.columbia.edu/tag/01B8, Lemma 17.9.4 and its proof.
The local `literature/stacks-project/modules.tex` file is absent on this machine;
the published source was read instead. The node agrees with the source and needs
no correction. The module docstring expands its three proof steps and explicitly
includes the zero-generator case. No statement dispute.

Searches:

- msearch.py LeanFinder, query "finite type sheaf of modules morphism surjective
  at one stalk is surjective on a neighbourhood": 8 hits, including
  `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` (requires all
  stalks), `app_surjective_of_stalkFunctor_map_bijective` (bijective stalks), and
  `PresheafOfModules.IsLocallySurjective`; no matching theorem.
- msearch.py Loogle, query "SheafOfModules.IsFiniteType,
  TopCat.Presheaf.stalkFunctor": 0 hits.
- msearch.py grep, query "surject.*stalk|stalk.*surject|IsFiniteType", restricted
  to Algebra/Category/ModuleCat/Sheaf: 10 hits concerning finite type generators
  and finite presentations, no single-stalk neighbourhood theorem.
- msearch.py LeanSearch, query "finite type module sheaf surjective stalk implies
  surjective neighbourhood": unavailable, Internal Server Error.
- rg in source `WeilConjectures` and project's `lean/Sheaf`, query
  `IsFiniteType|stalk.*[Ss]urject|surject.*stalk`: only different contexts,
  notably scheme-module `epi_of_surjective_stalk` (all stalks), étale and
  constructible stalk lemmas, and generator definitions. None matches.
- grep of the item id in `WeilConjectures`: no hits.
- rg for `IsFiniteType.*stalk|surjective_near|surjective.*finiteType|finiteType.*surjective`
  in upstream declaration names, Mathlib module categories and `lean/Sheaf`: no hits.

Validation: server compilation succeeded with the explicit universe parameters on
`SheafOfModules.IsFiniteType`; the final delivery dry run is recorded below.


## Second reading by H1

I independently read the item node, its module, all three statement-dependency
nodes and the Mathlib declarations they record. I also read the statement of
lem-weil-pbc-ringed-space-module-exactness-local-lifting, clause (1), used in
the proof docstring. The local Stacks checkout is absent; I read the published
01B8 page and the actual upstream modules.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/modules.tex,
including the introduction, pathology section, Definition definition-finite-type
(01B5), and Lemma lemma-finite-type-surjective-on-stalk (01B8) with its proof.
I followed its ringed-space and module definitions in upstream sheaves.tex,
labels definition-ringed-space, definition-presheaf-modules and
definition-sheaf-modules. These sources impose no local-ring, separation,
Noetherian, nonzero-ring, or characteristic assumption. In particular the
pathology section explicitly permits the zero structure sheaf.

The node's objects, hypotheses and conclusion, matched separately:

1. Topological space X and sheaf of rings O_X: `{X : TopCat.{u}}` and
   `{R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}`. PASS.
   Sites/Spaces.lean defines the topology by opens covering each point, so this
   is exactly a sheaf on the opens of X. The ring convention is the one of the
   recorded sheaf-of-modules dependency; no field or local-ring instance occurs.
2. Module sheaves G and F over that same O_X: `{G F : SheafOfModules.{u} R}`.
   PASS. Sheaf.lean:33 uses a PresheafOfModules over R.obj with its underlying
   abelian presheaf a sheaf. Presheaf.lean:43 has modules over R(U), semilinear
   restriction maps and functoriality, exactly the dependency's objects.
3. O_X-linear morphism G to F: `(φ : G ⟶ F)`. PASS. SheafOfModules.Hom.val
   is a PresheafOfModules.Hom, whose app components (Presheaf.lean:96) are
   R(U)-linear maps satisfying naturality. There is no extra hypothesis on G.
4. Point x in X: `(x : X)`. PASS, before the stalk-surjectivity hypothesis.
5. F of finite type: `[SheafOfModules.IsFiniteType.{u, u, u} F]`. PASS.
   I read Generators.lean:44, 95, 113, 137 and 142: finite index sets of generating
   sections, with Epi of the free map, on a CoversTop family. On Opens X these
   give precisely finitely many generators near each point, clause (1) of the
   recorded finite-type/presentation definition. No finite presentation or
   pointwise surjectivity on sections is substituted. The sheafification
   instances needed by that class are supplied for this topological site,
   as confirmed by compilation without any added binders.
6. Surjective map G_x to F_x: `hφ : Function.Surjective` of
   `(TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
   ((PresheafOfModules.toPresheaf R.obj).map φ.val)`. PASS. I read
   Presheaf.lean:143-174 and Stalks.lean:76-83, 147-155: the functor takes the
   colimit over open neighbourhoods and maps the germ of g to the germ of φ(g).
   Stalk.lean:167-176 equips this very carrier with the ring-stalk module
   action, characterized by germ_ringCat_smul. Forgetting the action for
   Function.Surjective does not change the carrier or induced function.
7. One open neighbourhood U of x: `∃ U : Opens X, x ∈ U ∧ ...`. PASS.
   U is chosen before W and t, so it works for every section on every subopen.
8. Arbitrary open W contained in U and t in F(W):
   `∀ (W : Opens X), W ≤ U → ∀ t : F.val.obj (op W)`. PASS.
9. An open covering of that W: existential `I : Type u`, `V : I → Opens X`,
   `hV : ∀ i, V i ≤ W`, and `(⨆ i, V i) = W`. PASS. Supremum is the union
   of the opens. Covers indexed in Type u suffice: from any covering with
   local lifts choose one covering member and its lift for each point of W,
   and reindex by the subtype W, which lies in Type u. Thus the index universe
   does not strengthen this existential conclusion.
10. A lift g_i on every covering member, with the correct restriction equation:
    `g : ∀ i, G.val.obj (op (V i))` and
    `∀ i, φ.val.app (op (V i)) (g i) = F.val.map (homOfLE (hV i)).op t`.
    PASS. Opposite turns V_i -> W into the restriction F(W) -> F(V_i).
    The covering and lifts may depend on W and t, exactly as in the node.

Edge cases: X empty admits no x, so the quantified assertion has no instance;
this is not an exclusion of empty ringed spaces. Empty W permits I = PEmpty,
union bottom and vacuous lift equations. Zero rings and zero module sheaves
are allowed without Nontrivial assumptions. A zero target permits zero lifts;
a zero source has surjective stalk precisely when F_x vanishes, and finite
generation yields local vanishing. Finite generator sets may be empty (n = 0),
explicitly covered by the proof docstring. No characteristic constraint occurs.
The arbitrary common universe u handles all carriers after placing them in a
common universe; it contains no quantification over test objects in a smaller
universe and hence no vacuous hypothesis of that kind. All variables and the
sole universe parameter are explicitly bound.

Independent searches, using terms different from the first worker's:

- msearch LeanFinder: "finite generators cokernel vanishes at a point vanishes
  locally module sheaf": 8 hits, including IsFiniteType.exists_localGeneratorsData,
  LocalGeneratorsData.IsFiniteType and generatorsOfIsCokernelFree. These are
  generator/presentation constructions, not the one-stalk neighbourhood lemma.
- msearch Loogle: `SheafOfModules.IsFiniteType, "surjective"`: zero hits.
- msearch grep: `cokernel.*stalk|stalk.*cokernel|surjective.*neighbourhood|surjective.*neighborhood`:
  zero hits.
- msearch LeanSearch: "finitely generated sheaf cokernel zero stalk open
  neighborhood": unavailable (Internal Server Error), recorded as unavailable,
  with no mathematical verdict inferred from that failed service.
- Direct rg in Mathlib's module-category sources, source WeilConjectures,
  project lean/Sheaf and dag/lean_names_upstream.json for finite type, cokernel
  vanishing, surjectivity near/neighbourhood, stalk surjectivity and the proposed
  full declaration name: no exact statement. Source Scheme.Modules.epi_of_surjective_stalk
  requires all stalks and schemes; WeilSheaf.surjective_stalkMap concerns Weil
  sheaves and assumes an epimorphism. Neither is this lemma. Existing generator
  and finite-presentation declarations were inspected above and reused.

No new definition nodes or dependency modules are present or needed. No node
correction or statement_change is present or needed; the original statement
agrees with 01B8, including its expanded local-lifting meaning. No mismatch was
found, and I left the correct Lean and node record unchanged. The report is the
only second-reading change. The module and declaration docstrings name the source
and blueprint id. The three proof steps reproduce finite local generators,
simultaneous germ lifts and shrinking, then local coefficient lifts and linear
combinations, including zero generators. There are no definitions and no proved
auxiliary statements: the only proof is the required sorry.

Validation: independent scompile succeeded, exit 0, compiled in 1.8 seconds,
without warnings. The stored lean.statement was checked verbatim against the
signature in the module; all Lean lines have at most 100 characters. The prescribed
delivery dry run and push follow this review.

## Reviewer fix (R-mfs1153)

The delivered statement worked over an arbitrary `R : Sheaf (Opens.grothendieckTopology X) RingCat`
(not a ringed space: noncommutative rings allowed) and took the stalk map through the bare
`TopCat.Presheaf.stalkFunctor AddCommGrpCat` instead of the landed stalk notion. Restated in the
project form: `(X : RingedSpace.{u})`, `G F : SheafOfModules.{u} (moduleRings X)`, `[F.IsFiniteType]`,
`hφ : Function.Surjective ((moduleStalkFunctor X x).map φ)` (def-pc-module-stalk-functor), in namespace
`AlgebraicGeometry.RingedSpace`. The conclusion keeps the node's explicit local-lifting spelling of
"φ|_U surjective as a map of sheaves". Compiled clean under L.
