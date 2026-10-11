## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianSheavesGModules` states
`AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules`, with a single `sorry`.
No definition or instance is introduced. The source is Stacks
[04JQ](https://stacks.math.columbia.edu/tag/04JQ), read together with
[03QT](https://stacks.math.columbia.edu/tag/03QT) and the action formula of 03QW.
The local source `/home/ubuntu/c1-stacks-review/etale-cohomology.tex` was also read at
`section-galois-action-stalks` (8516ff) and `lemma-equivalence-abelian-sheaves-point`
(9078ff). The assigned repository's literature checkout is absent.

Hypothesis and clause mapping:

- A field K: `(K : Type u) [Field K]`. A separable closure: `(Ks : Type u)`,
  `[Field Ks] [Algebra K Ks] [IsSepClosure K Ks]`. These are Mathlib's field-extension
  and separable-closure structures, not private definitions.
- The corrected geometric point uses `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`,
  `[Algebra Ks Ω] [Algebra K Ω] [IsScalarTower K Ks Ω]`. The tower says the inclusions
  agree, and the field maps are injective. No algebraicity or perfection assumption is
  imposed on Ω. `s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))` is the specified
  geometric point over `S := Spec (.of K)`.
- The group is definitionally `G := Gal(Ks/K)`. Import `Mathlib.FieldTheory.KrullTopology`
  supplies its Krull topology and topological group structure (instances at 133 and 139).
- The small etale site is `J := S.smallEtaleTopology`; abelian sheaves are
  `Sheaf J AddCommGrpCat.{max (u + 1) v}`, as explicitly recorded in
  `def-weil-pbc-etale-sheaves`. The category is not replaced by a category of finite,
  locally constant, constructible, or torsion sheaves.
- Discrete G-modules are the existing
  `Rep.DiscreteContinuousRep.{0, u, max (u + 1) v} ℤ G`. Integer modules are precisely
  abelian groups, and linear G-actions are actions by abelian-group automorphisms.
  This existing full subcategory imposes open stabilizers on every element. Its maps
  are all equivariant integer-linear maps. `U` is only its existing inclusion functor.
- The equivalence is `E`. The natural isomorphism `i` identifies its underlying abelian
  group functor with `p.sheafFiber`, where `p := pointSmallEtale s`. This is the exact
  geometric-stalk construction of `def-weil-pbc-geometric-stalks`, with colimits over
  opposite pointed etale neighbourhoods. Components of `i` are abelian group
  isomorphisms, so preserve addition, zero, and inverse; naturality fixes the maps too.
- `Eset` is an equivalence from all set-valued etale sheaves to Mathlib's
  `DiscreteContAction (Type (max (u + 1) v)) G`. The discrete topology on Type is the
  existing instance `AlgebraicGeometry.hasForget₂TypeTopCat` from
  `Sheaf.AlgebraicGeometry.EtaleFieldGsets`. `V` is the composite of the two existing
  full-subcategory inclusions, not a newly defined action category. `j` identifies
  its underlying functor with the same point's set-valued `sheafFiber`.
- The `Nonempty` natural isomorphism in `Action (Type ...) G` makes the square commute:
  forgetting the abelian structure after E agrees equivariantly and naturally with
  forgetting it in sheaves and applying Eset. `sheafCompose J (forget AddCommGrpCat)`
  is the existing sheaf forgetful functor; `Rep.RepToAction` and `Functor.mapAction`
  are Mathlib's existing functors.
- Each of the final two clauses fixes the action, rather than quantifying over an
  unspecified equivalence. An element of the stalk is the germ
  `p.toPresheafFiber X x F.obj z`. For `g : Gal(Ks/K)` and any extending automorphism
  `τ : Ω ≃ₐ[K] Ω`, `hτ` expresses agreement on Ks. `hx` expresses precomposition
  of the pointed lift with `Spec τ`. The displayed equation transports the action
  through `i` or `j` and requires precisely the germ at that changed lift. This is
  the left action in Stacks 03QW, independent of which extension τ is used.

Dependencies and full signatures/docstrings inspected:

- `def-pc-field-extension`: Mathlib `Algebra` (Algebra/Algebra/Defs.lean:95), used via
  the three Algebra binders. Its recorded field-map injectivity is standard.
- `def-weil-pbc-geometric-stalks`: Mathlib
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber` (Sites/Point/Basic.lean:277),
  with `presheafFiber` (96), `toPresheafFiber` (103), and
  `AlgebraicGeometry.Scheme.pointSmallEtale` (Sites/EtalePoint.lean:64).
- `def-weil-pbc-etale-sheaves`: `Sheaf.AlgebraicGeometry.EtaleSheaves` records that
  Ab(T_et) is Mathlib `Sheaf T.smallEtaleTopology AddCommGrpCat` and Sh(T_et) is
  `Sheaf T.smallEtaleTopology (Type ...)`. Its locally-constant and constructible
  predicates are not used, so its large module is not imported unnecessarily.
- Added landed dependency `def-exc-discrete-modules-category`:
  `Sheaf.RepresentationTheory.DiscreteContinuousRep`, `Rep.DiscreteContinuousRep`.
  Its complete definition and docstring were read and reused.
- Added landed dependency `lem-exc-etale-field-gsets`:
  `Sheaf.AlgebraicGeometry.EtaleFieldGsets`, `AlgebraicGeometry.etaleFieldGsets`.
  Its statement and module were read; its discrete-action category and the Type-to-TopCat
  instance are reused. Its theorem itself is not a hypothesis or proof used here.
- The correction additionally cites `def-pd-separable-closure`: the recorded source
  module `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` explicitly identifies the
  notion with Mathlib `IsSepClosure` in the docstring of
  `IsSepClosure.exists_intermediateField_mem`; that declaration was read in full.
  `IsSepClosure` itself was read at IsSepClosed.lean:227. `def-weil-geometric-point`
  is the Mathlib record `Scheme.SpecToEquivOfField, IsAlgClosed`; its full signature
  and docstring were read at ResidueField.lean:346. No repair module is needed.

Edge cases: separably closed K has trivial G and evaluation gives the familiar abelian
sheaf/group equivalence. Imperfect K is allowed, and Ω need not be algebraic over K.
For finite K the target includes arbitrary discrete G-modules, not only finite ones.
The zero sheaf and zero module are allowed; Eset includes the empty sheaf/G-set.
No finiteness, torsion, connected-neighbourhood, or characteristic hypothesis is added.
`u` and `v` are explicitly bound. All fields can be put into a common universe, as
required by `Scheme.{u}`; arbitrary carrier sizes are covered by `max (u + 1) v`.
In the action formula, the empty etale object has no pointed lift, so contributes no
spurious requirement. All introduced variables are explicitly bound.

Searches actually run (all via msearch.py and logged in searches.jsonl):

- LeanFinder: `Abelian sheaves on the small etale site of a field equivalent to discrete
  continuous Galois representations`: 8 hits, mostly condensed discrete-module functors
  and the finite Galois-category fibre equivalence. None is this equivalence of all
  abelian etale sheaves with arbitrary discrete modules.
- Loogle: `CategoryTheory.Sheaf, CategoryTheory.Action, CategoryTheory.ContAction`:
  0 hits, with an unknown-identifier diagnostic for CategoryTheory.Action. This is an
  invalid namespaced query, not evidence of absence; the subsequent source inspection
  established the actual root namespaces Action and ContAction.
- Grep: `Galois.*sheaf|sheaf.*Galois|pointSmallEtale` in Mathlib/AlgebraicGeometry:
  6 hits, pointSmallEtale infrastructure and an unrelated ideal-sheaf Galois connection.
- LeanSearch: `geometric stalk of abelian etale sheaves on a field is equivalent to
  discrete Galois modules`: unavailable, HTTP Internal Server Error, not a no-match.
- Direct rg of WeilConjectures and lean/Sheaf for the item id and Galois/sheaf wording:
  no exact theorem. Hits are the etale-field G-set equivalence and section-descent
  infrastructure. `tools/lean_names_upstream.py show` supplied no attached declaration
  for this item. The item-id grep of WeilConjectures likewise has no declaration.
- Direct source inspection confirms Mathlib Action, ContAction, DiscreteContAction,
  RepToAction, sheafCompose, and the geometric stalk are existing notions. None was
  redefined. New declaration name was checked by rg against Mathlib and the source.

The theorem docstring includes both DAG proof steps and their cited nodes. Every proof
is `sorry`; no theorem is proved in stage 2. Server compilation is used exclusively.
No new definition node or dependency repair module is necessary.

## Statement corrected

Old statement (verbatim):

Let K be a field [def-pc-field-extension], K^sep a separable closure, and G=Gal(K^sep/K). Taking the geometric stalk [def-weil-pbc-geometric-stalks] at Spec K^sep induces an equivalence between abelian sheaves [def-weil-pbc-etale-sheaves] on the small etale site of Spec K and discrete G-modules. The equivalence is compatible with the underlying sheaf-of-sets/G-set equivalence and with the abelian group operations.

The geometric-point terminology conflicts with the project's definition for imperfect
fields: for K = F_p(t), its separable closure cannot contain a p-th root of t, since this
is purely inseparable over K, so it is not algebraically closed. Stacks 04JQ uses a genuine
geometric point; 03QW specifies the embedding of the separable closure into its
algebraically closed residue field and the action through extending automorphisms.
The corrected node therefore introduces Ω algebraically closed containing Ks over K,
uses Spec Ω for the geometric stalk, and leaves G = Gal(Ks/K). Ω may be any such extension,
not just an algebraic closure. This is the source's statement, not a perfect-field
specialization. The earlier set-sheaf node `lem-exc-etale-sheaves-gsets-point` already
contains the same geometric-point correction. The proof's first sentence is adjusted
to Spec Ω; all mathematical steps and proof dependencies remain the same.

Citer `lem-exc-field-discrete-modules`: holds true. Its abelian enhancement, transport
of a finite ring action, underlying G-set comparison, and exact-equivalence argument
still hold. The informal reference in its first proof step to Spec K^sep as a geometric
point should be read with Spec Ω; pointed etale fibres still use separable embeddings
in Ks. The citer is not edited. The exhaustive JSON scan found exactly this one citer
in stmt_deps/proof_deps, matching the rg search.

## Second reading by J1

I read the corrected node, its Stacks source (04JQ, with 03QT and 03QW), and
`Sheaf/AlgebraicGeometry/AbelianSheavesGModules.lean` independently.

- The field object is rendered by `(K : Type u) [Field K]`; no finiteness,
  characteristic, or perfection assumption is added. The separable closure is
  `(Ks : Type u) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]`, matching
  `[def-pd-separable-closure]`.
- The algebraically closed extension and geometric point are rendered by
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra Ks Ω] [Algebra K Ω]
  [IsScalarTower K Ks Ω]` and `s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))`.
  This fixes the original mismatch in which `Spec K^sep` was called geometric.
- `G := Gal(Ks/K)` is used with its Krull topology. `J := S.smallEtaleTopology`
  and `Sheaf J AddCommGrpCat` render all abelian sheaves on the small etale site;
  no constructibility, torsion, or local-constancy restriction appears.
- `E` lands in the existing `Rep.DiscreteContinuousRep ℤ G`, whose open
  stabilizer condition is the node's discrete G-module notion. `Eset` lands in
  `DiscreteContAction ... G`; `U` and `V` are the existing inclusions. Thus the
  two equivalences and their carrier functors are the stated objects.
- `i` and `j` identify the underlying abelian-group and set-valued functors with
  the same geometric stalk `p.sheafFiber`. The `Nonempty` natural isomorphism
  states compatibility with forgetting abelian structure, and hence with the
  underlying sheaf/G-set equivalence and group operations.
- The final two universal clauses quantify `g`, an extension `τ : Ω ≃ₐ[K] Ω`,
  its agreement `hτ` on `Ks`, pointed lifts `x,x'`, and a germ `z`; `hx` forces
  `x'` to be the lift changed by `Spec τ`. Their equations specify exactly the
  action on abelian and set-valued stalks described in 03QW.

Edge cases checked again: trivial G for separably closed K, imperfect K with an
independent algebraically closed Ω, finite K with arbitrary discrete modules,
zero and empty sheaves/modules, and empty etale objects (the universal clauses
then have no pointed lift). Universes `u,v` are explicitly bound and the target
carrier uses `max (u + 1) v`.

Searches and dependency checks found no existing declaration for this theorem.
The recorded dependencies `def-pc-field-extension`, `def-pd-separable-closure`,
`def-weil-geometric-point`, `def-weil-pbc-geometric-stalks`,
`def-weil-pbc-etale-sheaves`, `def-exc-discrete-modules-category`, and
`lem-exc-etale-field-gsets` were opened and their declarations match their uses.
The only mismatch was the node's original `Spec K^sep` geometric point; I changed
the node to the Ω formulation, added its required dependencies, and recorded the
correction and citer verdict above. The corrected module compiles with one
`sorry` theorem and no other diagnostics.
