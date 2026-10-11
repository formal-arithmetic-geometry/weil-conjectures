## Worker report

Module: `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDerivedHom`.
Declaration: `AlgebraicGeometry.finiteLocallyFree_derivedInternalHom_single`.
This states the node without changing its mathematical statement. All proofs are `sorry`.

Hypothesis and clause correspondence:

- Scheme Y: `(Y : Scheme.{u})`. No Noetherian, properness, characteristic,
  quasi-compactness, or connectedness assumption is imposed.
- P is an O_Y-module: `P : SheafOfModules.{u} (moduleRings Y.toRingedSpace)`.
  This is the shared module category used by `schemeDerivedCategory Y`, without
  the separate category instance on `Y.Modules`.
- P is finite locally free with finite ranks allowed to vary across the cover:
  `[SheafOfModules.IsFiniteLocallyFree.{u, u, u} P]`. This existing source class
  provides local generators whose maps from free sheaves are isomorphisms and whose
  generator index types are finite. On the open site its covering family is a
  Zariski open cover. Each finite index type can be identified with Fin d, giving
  exactly the stated local O_Y^d models. The fixed-rank dependency
  `def-amb-finite-locally-free-module` describes those local models, but its recorded
  `IsFiniteLocallyFreeOfRank` would impose a single global rank if used as the
  hypothesis. Therefore `stmt_deps` gains the already landed
  `def-sc-finite-locally-free-sheaf`, which records the existing variable-rank class.
  No new definition, dependency replacement, or statement correction is needed.
- L is any O_Y-module: the same binder for L, with no coherence or freeness restriction.
- P and L sit in degree zero: `(DerivedCategory.singleFunctor
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P` and its L counterpart.
- Derived category: the binder `[HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]` specifies the localization
  infrastructure of `schemeDerivedCategory`, not an extra geometric assumption.
- Derived internal Hom: `(derivedInternalHom (Opens.grothendieckTopology Y)
  Y.toRingedSpace.sheaf).obj (op P[0], L[0])`, with the two single-functor terms
  written in full in the actual signature. It is the shared bifunctor on the open
  ringed site, specialized to the scheme structure sheaf.
- Represented by ordinary sheaf Hom in degree zero: the first conjunct is
  `Nonempty (RHom(P[0], L[0]) ≅ Hom(P,L)[0])`. Here Hom(P,L) is precisely the
  existing `SheafOfModules.homObj (R := Y.toRingedSpace.sheaf) P L`, not global Hom.
  Representation means existence of an isomorphism, with no additional naturality
  or choice of comparison imposed.
- Equivalently, positive sheaf Exts vanish: the second conjunct is
  `∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor ... i).obj RHom(...))`.
  Positive integers match all positive Ext degrees. This concerns cohomology
  sheaves, not global Ext groups. The isomorphism conjunct already entails it,
  but it explicitly renders the node's equivalent formulation.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`
  (read its full definition and used its definitionally identical shared carrier),
  importing the shared `AlgebraicGeometry.moduleRings` from
  `Sheaf.Paper.DerivedHomMayerVietoris`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` (constant-rank dependency),
  `SheafOfModules.IsFiniteLocallyFree` (the added existing variable-rank node),
  and the cover characterizations `isFiniteLocallyFreeOfRank_iff_exists_over_iso_free`
  and `isFiniteLocallyFree_of_exists_over_iso_free` read to check the interpretation.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`.
  Its full signature, localization definition, and comparison statements were read.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`; its full signature and definition were read.
- Mathlib: `DerivedCategory.singleFunctor`, `DerivedCategory.homologyFunctor`,
  and `CategoryTheory.Limits.IsZero` provide the embedding and cohomology-vanishing syntax.

Source checked: the local Stacks checkout is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/08DQ . Its strictly perfect representative
computation specializes to P[0], L[0]. No source correction is necessary.
The theorem docstring carries the node's complete two-step proof route:
exactness via `lem-sc-ext-tensor-exact` and `lem-sc-ext-evaluation`, followed by
computation on a K-injective resolution and truncation in the derived category.

Edge cases checked before writing: P=0 (rank zero) gives zero sheaf Hom and zero
RHom; L=0 does likewise; P=O_Y gives L in degree zero, with vanishing positive
cohomology. Disconnected schemes with different finite ranks on their components
are admitted by IsFiniteLocallyFree. Empty schemes, empty covering families, and
unbounded finite ranks over infinitely many components are not excluded. L need
not be quasi-coherent. No assertion about vanishing global Ext is made: for
P=O_Y on a proper curve those global groups can be nonzero. Universes u and w
are explicitly declared; every theorem variable is explicitly bound.

Searches (all msearch calls recorded in searches.jsonl):

- `msearch.py ... leansearch`, query "derived internal Hom from a finite locally
  free sheaf is ordinary sheaf Hom in degree zero": unavailable, Internal Server Error.
- `msearch.py ... leanfinder`, same query: eight hits, including
  SheafOfModules.unitHomEquiv, freeHomEquiv, and LightCondensed.ihomPoints;
  none state the derived sheaf-level result.
- `msearch.py ... loogle`, query "SheafOfModules.homObj, DerivedCategory.singleFunctor":
  no hits; unknown identifier SheafOfModules.homObj (it is in the source project).
- `msearch.py ... grep`, query `derived.*[Hh]om|[Hh]om.*[Ff]inite[Ll]ocally[Ff]ree`:
  results about general derived functors and Ext, no exact sheaf-level theorem.
- `rg -n 'derivedInternalHom|lem-sc-finite-locally-free-derived-hom'` in the source
  project and lean/Sheaf: only the shared DerivedInternalHom module on sheaf-dag;
  no existing theorem for this item.
- Broader source/project grep for derived Hom and finite local freeness found
  related HomTensor and derived-complex APIs, not this statement.
- Grep of dag/nodes for IsFiniteLocallyFree found the already landed
  `def-sc-finite-locally-free-sheaf`; read its complete node and record.
- Exact proposed declaration-name grep in Mathlib, source, project, and
  dag/lean_names_upstream.json found no collision.

Validation: scompile.py Q1 lem-sc-finite-locally-free-derived-hom on the module
returned exit code 0, compiling in 2.9 seconds with no errors or warnings.
No disputed statement or mathematical node fault was found.


## Second reading by Q1

I read the sandbox node and theorem together, all four original statement-dependency
nodes and their declaration sources, and the already landed
`def-sc-finite-locally-free-sheaf` node. The local Stacks checkout is absent; I read
`cohomology.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex,
label `lemma-dual-perfect-complex`, and its Tag 08DQ rendering at
https://stacks.math.columbia.edu/tag/08DQ. The source assumes a ringed space and a
perfect first object, with arbitrary second derived object. Specializing to a
scheme and P[0], L[0] imposes no Noetherian, separatedness, field, or characteristic
condition. The local strictly-perfect computation gives this node's assertion.

Object/hypothesis/conclusion checklist (each verdict is PASS):

1. Y is an arbitrary scheme: `(Y : Scheme.{u})`; no geometric instances are added.
2. P is an O_Y-module: `P : SheafOfModules.{u} (moduleRings Y.toRingedSpace)`.
   I opened `moduleRings` in DerivedHomMayerVietoris: it is the scheme's commutative
   structure sheaf composed with forget-to-rings, exactly the coefficient sheaf.
3. P is locally O_Y to a finite rank, which may vary with the open:
   `[SheafOfModules.IsFiniteLocallyFree.{u, u, u} P]`.
   I read the classes and their cover characterizations in the recorded dependency
   module `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
   variable-rank freeness means local generator maps are isomorphisms and the
   generator sets on each cover member are finite. The finite sets identify with
   Fin d locally. `IsFiniteLocallyFreeOfRank` instead fixes one r globally;
   imposing it here would add a hypothesis absent from the node. The original
   dependency supplies the constant-rank local models; its same module already
   supplies the variable-rank class. No definition is duplicated or replaced.
4. L is an arbitrary O_Y-module: the shared `(P L : SheafOfModules ... )` binder;
   no local-freeness or quasi-coherence requirement on L.
5. Both P and L are degree-zero objects: the two
   `(DerivedCategory.singleFunctor (SheafOfModules ...) 0).obj` terms.
6. The ambient category is D(O_Y): `DerivedCategory (SheafOfModules ...)` is
   definitionally the recorded `schemeDerivedCategory Y` from DerivedCategory.lean.
   `[HasDerivedCategory.{w} ...]` supplies the shared localization infrastructure,
   rather than selecting a different category or asserting a geometric property.
7. RHom is internal derived Hom: `(derivedInternalHom
   (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj (op P[0], L[0])`.
   I read its full definition and comparison signatures: it localizes the shared
   sheaf Hom complex with functorial K-injective replacement in the second variable.
8. Ordinary Hom is sheaf Hom: `SheafOfModules.homObj
   (R := Y.toRingedSpace.sheaf) P L`. I read InternalHom.lean's definition and
   sectionwise description U -> Hom(P|U,L|U); this is not the global Hom group.
9. Representation in degree zero: the first conjunct is `Nonempty (RHom ... ≅
   (DerivedCategory.singleFunctor ... 0).obj (SheafOfModules.homObj ... P L))`.
   Existence of this isomorphism is exactly representation; the node does not
   specify a chosen comparison or assert naturality as additional data.
10. Every higher sheaf Ext vanishes: the second conjunct binds `∀ i : ℤ,
    0 < i → IsZero ((DerivedCategory.homologyFunctor ... i).obj RHom)`.
    With cochain indexing these are cohomology SHEAVES. Positive integers cover
    precisely all positive Ext degrees. This is the node's equivalent clause,
    logically redundant with the degree-zero isomorphism but not stronger.

Edge cases: P=0 and local rank d=0 are admitted by empty finite generator types;
L=0 is admitted; P=O_Y gives L[0]. The empty scheme admits the empty open cover;
there is no Nonempty cover/index binder. Disconnected schemes may have different
ranks, including unbounded finite ranks on infinitely many components. Neither
characteristic nor base field is constrained. The binders `universe u w` and the
explicit module carrier follow the recorded derived-category and internal-Hom
APIs; u can be enlarged for arbitrarily large scheme/module data, and w is the
localization morphism universe. No variable or universe is unbound. Degree zero
is included in the representation clause, and is deliberately excluded only from
higher-Ext vanishing. Negative cohomology also vanishes by the representation,
without an extra clause beyond what it entails. Global Ext need not vanish:
the structure sheaf on a curve already distinguishes that false interpretation.

Independent searches, using wording different from the worker's:

- msearch leanfinder: "Higher internal Ext sheaves vanish when the first argument
  is locally projective of finite rank". Eight hits: projective-object Ext and
  Tor vanishing and projective-dimension APIs; these are global Ext statements,
  not the internal derived sheaf-Hom assertion.
- msearch leansearch: "Cohomology of the internal Hom complex from a locally free
  sheaf of finite rank to a module concentrated in degree zero". Service returned
  Internal Server Error; recorded as unavailable, not as a negative search result.
- Direct rg in Mathlib's ModuleCat and derived-category sources, upstream
  WeilConjectures/Algebra and module-sheaf sources, and repository lean/Sheaf:
  `rhom|internalhom|homcomplex|hom.*locallyfree|locallyfree.*hom`, plus
  `locally.?free.*(ext|derived|hom)|(?:ext|derived|hom).*locally.?free`.
  Found general Hom complexes and `locallyFreeHomAbelianFunctor_exact` and
  `locallyFreeExtAddEquivH` in LocallyFreeExtCohomology.lean. I opened that module:
  exactness and global Ext/cohomology comparison do not state the derived
  internal Hom isomorphism of this node. No existing exact theorem was found.
- Exact-name rg in upstream/project sources and dag/lean_names_upstream.json found
  no collision for the delivered theorem. The only shared `derivedInternalHom`
  definition is the dependency module already imported by the delivery.

Mismatch repaired: the worker added the already landed definition node
`def-sc-finite-locally-free-sheaf` to stmt_deps. Under the uncorrected-item field
rule, stmt_deps may gain only NEW definition nodes of the delivery. The addition
is redundant: the original recorded local-freeness module already supplies the
class, and the node explicitly describes variable finite ranks via local models.
I removed that addition, restoring stmt_deps verbatim to the base, and updated
lean.note. The worker-report description of that addition above records the
first worker's work; this section supersedes it. No mathematical statement,
Lean signature, proof route, or module was changed. There are no new nodes or
dependency modules and no statement correction or disputed statement.

I checked H5/H6/H8/H9: one theorem, proof `sorry`, no definitions or private copies;
both source docstrings and blueprint id present; the theorem docstring carries
both exactness/evaluation and K-injective/truncation proof steps; three used
imports, no local notation/instances, and lines at most 100 characters. The node's
lean.statement is byte-for-byte the theorem signature before `:=`.

Validation: scompile.py Q1 lem-sc-finite-locally-free-derived-hom on the delivered
module returned exit code 0, compiled in 3.0 s, with no errors or warnings.
