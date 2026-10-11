## Worker report

The module `Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion` states
`AlgebraicGeometry.Scheme.Modules.module_cohomology_isZero_of_cech_vanishing`.
Its only theorem has proof `by sorry`; it introduces no definitions or instances.
The node copy changes only `lean`.

Hypothesis and clause mapping:

- The scheme X is `(X : Scheme.{u})`; the sheaf of O_X-modules is `(F : X.Modules)`.
- An arbitrary open U is `(U : X.Opens)` in both the hypothesis and conclusion.
- A family of opens is `(I : Type (max u w)) (V : I → X.Opens)`.
  The arrows `(hom : ∀ i, V i ⟶ U)` say each member is contained in U;
  `(⨆ i, V i) = U` says the members cover U. These are the Zariski coverings in
  `TopologicalSpace.Opens.grothendieckTopology`, whose objects and arrows are opens
  and inclusions. There are no finiteness, nonemptiness or separation assumptions.
- The chosen iterated fibre products are `(S : SiteCechComplex V hom)`.
  In a poset, its universal property forces `S.W p t` to be exactly the intersection
  of `V (t k)` for k in Fin (p+1). Its `indexMap` is consequently the unique inclusion
  of intersections, and its degree-zero product is the original member. There is no
  extra assumption on the family: all such products exist in opens. Quantification
  over all choices is equivalent to the node's fixed intersection construction;
  there is only one object and only one morphism with the required properties.
- The underlying abelian presheaf W ↦ F(W) is `((toPresheaf X).obj F)`.
  The recorded `S.cohomologyFunctor p` is homology of its actual Čech complex,
  with degree-p product indexed by `Fin (p+1) → I` and alternating restrictions
  using `Fin.succAbove`. `IsZero` of its value expresses Čech H^p = 0.
- Positive degree is `(p : ℕ), 0 < p →`, in the hypothesis and conclusion;
  there is no requirement at degree zero.
- The restricted O_U-module is `((restrictFunctor U.ι).obj F)`.
  Its cohomology is `(RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj`
  applied to that object. `IsZero` expresses its vanishing. This is derived global
  sections in the module category on U, exactly the node's H^p(U,F|_U), rather than
  Ext in abelian sheaves on X.

Universes u and w are explicitly declared. The index universe `max u w` can be
arbitrarily large and is at least the point/section universe, so the hypothesis
includes coverings indexed by the points of any open and cannot become vacuous
through an independently too-small universe. Smaller index types can be lifted
without changing the covering or its Čech complex up to canonical isomorphism.
As usual the theorem is universe-polymorphic, rather than internally quantifying
across universes. All binders are explicit; local compilation uses autoImplicit=false.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its `Hom`,
  and `Scheme.Opens` (def-pc-scheme); full signatures and docstrings read.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules` for module sheaves
  (def-weil-sheaf-of-modules-category), `Scheme.Modules.toPresheaf`, and
  `Scheme.Modules.restrictFunctor` (lem-weil-pbc-module-restriction-open-immersion-colimits).
  The signatures, definitions and docstrings of these, `restrictAdjunction`, and
  `SheafOfModules` were read. Restriction is exactly the recorded functor, not a
  private notion or a replacement tensor pullback.
- `Sheaf.Paper.PQFCohomology`: the dependency's declaration
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` identifies the degree
  functors as the already-defined `RingedSpace.moduleCohomology`. Its complete
  signature and docstring and the latter's definition were read; the module is
  imported and the exact cohomology definition it specifies is used.
- `Mathlib.CategoryTheory.Sites.Spaces`: `TopologicalSpace.Opens.grothendieckTopology`
  (def-sc-zariski-site), and `Mathlib.Topology.Sheaves.Sheaf`: `TopCat.Sheaf`.
  Definitions/docstrings read. These imports are already provided transitively;
  cover union and inclusion arrows express precisely this topology.
- `Sheaf.CategoryTheory.SiteCechComplex`: `CategoryTheory.SiteCechComplex` and
  `CategoryTheory.SiteCechComplex.cohomologyFunctor`
  (def-weil-pbc-site-cech-complex). The full module was read, including universal
  products, index maps, cochains, actual differential, complex and homology functor.

Source checked directly: [Stacks 01EV](https://stacks.math.columbia.edu/tag/01EV)
for module sheaves on all coverings of all opens, and
[Stacks 01E1 (2)](https://stacks.math.columbia.edu/tag/01E1) for identifying open
cohomology with cohomology of the restricted module. The local Stacks TeX file is
not present, so these authoritative tag pages were read. The theorem docstring
carries all nine proof steps with the DAG lemmas they use.

Edge cases checked before writing:

- Empty index type: its supremum is bottom, so the empty covering covers exactly
  the empty open. Every nonnegative Čech term is an empty product, hence zero.
  No Nonempty or Fintype binder excludes this case.
- Empty scheme and empty open: the sheaf axiom gives zero sections on the empty
  open, and derived module cohomology vanishes; the statement includes them.
- Zero module: both the Čech groups and the restricted cohomology are zero.
- Degree zero is intentionally excluded; a sheaf can have nonzero sections.
- Infinite covers are included. The scheme is unrestricted: no quasi-compactness,
  Noetherianity, characteristic, or coefficient condition is introduced.

Searches for an existing statement:

1. `msearch.py ... leanfinder "Vanishing higher Cech cohomology for every open covering
   implies vanishing higher sheaf cohomology on every open"`: eight hits, about
   Mayer–Vietoris sheaf conditions, opens-cover sheaf conditions, and
   `CategoryTheory.Sheaf.cohomologyPresheaf`; none is this module criterion.
2. `msearch.py ... loogle "Sheaf.H, Presheaf.cechComplex"`: zero hits (Loogle
   reports unknown identifier Sheaf.H).
3. `msearch.py ... grep "cech.*vanish|vanish.*cech|cech.*acyclic"`: zero Mathlib hits.
4. `rg` with that pattern and the node id in upstream WeilConjectures and project
   Sheaf: upstream `Topology/Sheaves/CechCriterion.lean` and
   `CategoryTheory/Sites/CechCriterion.lean`, and landed étale criteria and related
   modules. The upstream topological theorem's full signature was read: it is
   for abelian-sheaf Ext, a finite-cover refinement hypothesis, and cohomology on
   the whole space. It does not state derived module cohomology on restricted
   open subschemes. The site and étale variants likewise do not replace this node.
5. `grep -rn` for this exact node id in upstream WeilConjectures: no matches.
6. `rg` for the proposed full declaration suffix in Mathlib, upstream, project
   Sheaf and `dag/lean_names_upstream.json`: no name collision.

No statement correction, missing notion, or unusable dependency was found.
Local `lcompile.py` completed successfully, with no warnings or errors.
The independent second reading remains for the designated second worker.


## Second reading by G1

I independently opened the sandbox module and node, all six statement dependency
nodes, the recorded Mathlib definitions, SiteCechComplex, PQFCohomology, and
RingedSpaceModuleCohomology. The repository and upstream checkout were read only.
Only the report and search log were changed. No mismatch requiring a Lean or node
change was found; the existing signature is retained verbatim.

Source: the local Stacks checkout is absent. I read the actual Stacks TeX from
https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex,
labels `lemma-cech-vanish` and `lemma-cohomology-of-open`, including both proofs,
and checked the authoritative pages https://stacks.math.columbia.edu/tag/01EV
and https://stacks.math.columbia.edu/tag/01E1. The ambient hypothesis is an
arbitrary ringed space and an arbitrary module sheaf. Specializing to schemes
is exactly the node; neither source requires finiteness or separation.

My statement checklist, with Lean rendering and verdict:

1. Object X: `(X : Scheme.{u})`, the recorded Mathlib Scheme, not an affine or
   Noetherian specialization. PASS.
2. Object F: `(F : X.Modules)`. I read `Modules := SheafOfModules.{u}
   X.ringCatSheaf` and its abelian instance; this is a genuine O_X-module sheaf
   with compatible sectionwise scalar actions, not just an abelian sheaf. PASS.
3. Arbitrary open U: `(U : X.Opens)` in the hypothesis and conclusion. Its open
   scheme is `U.toScheme`; `U.ι` is the inclusion. PASS.
4. Arbitrary family: `(I : Type (max u w)) (V : I → X.Opens)` and
   `(hom : ∀ i, V i ⟶ U)`. In the opens category these arrows express precisely
   containment. The equation `(⨆ i, V i) = U` expresses the union covering,
   equivalent to the recorded Opens.grothendieckTopology pointwise cover
   condition. No finite or nonempty restriction. PASS.
5. Intersections and projections: `(S : SiteCechComplex V hom)`. I read its
   `W`, `pr`, `comm`, `universal`, `W_zero`, `pr_zero`, `indexMap`, and
   `indexMap_pr` fields. In this poset the finite intersection has the
   universal property, and the property conversely forces W to equal it;
   arrows are unique. Such data exist for every family, including the empty
   family. Thus quantifying over S adds no hypothesis and is not vacuous.
   `Fin.succAbove` selects exactly the omitted-factor inclusion. PASS.
6. Underlying abelian presheaf: `((toPresheaf X).obj F)`. The recorded Mathlib
   functor forgets the module structure and keeps the sections and restrictions.
   It does not replace the sheaf by a different carrier. PASS.
7. Cech cohomology: `(S.cohomologyFunctor p).obj ...`. I read `cochains`
   (product over `Fin (p+1) → I`), `differentialValue` (signed restrictions),
   `differential`, `complex`, and `cohomologyFunctor` (homology of that complex).
   For positive degrees the nonnegative complex has the same kernel/image as
   the node's integer complex with negative terms zero. PASS.
8. Hypothesis: `hcech` universally quantifies U, I, V, hom, cover equality, S,
   and `(p : ℕ), 0 < p → IsZero ...`. This is precisely vanishing for all
   positive degrees of all covers of all opens. Reordering these universal
   quantifiers does not change the statement. PASS.
9. Restricted module: `((restrictFunctor U.ι).obj F)`. I read the actual
   restriction definition, `restrictAppIso`, `restrict_obj`, and `restrict_map`:
   sections are those over the image open and scalars transport via the
   structure sheaf isomorphism. This is the dependency's restriction. PASS.
10. Conclusion: for all U and p with `0 < p`, `IsZero
    ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace p).obj
    ((restrictFunctor U.ι).obj F))`. The recorded moduleCohomology is
    `globalSectionsFunctor.rightDerived p`, in modules on U. PQFCohomology
    identifies its degree functors with this same definition. IsZero is on a
    ModuleCat object (and in the hypothesis on AddCommGrpCat), so it correctly
    expresses vanishing. Tag 01E1(2) justifies the source's open-cohomology
    notation. All clauses match, with no extra instances. PASS.

Edge cases: empty I forces U to be the empty open; each tuple type is empty
because Fin(p+1) is nonempty, and the cochains are empty products, hence zero.
The empty open and empty scheme are allowed. The zero module is allowed.
Degree zero is deliberately excluded on both sides. Arbitrary characteristic,
infinite covers, and schemes without quasi-compactness are included. Universes
u and w and all variables are explicitly bound. The index universe max u w
includes point-indexed covers, so it cannot make the hypothesis vacuous by
being too small; smaller index types lift into it. There is no limit/filtered
colimit index restriction in this statement.

Independent searches (queries different from the first worker's):

- msearch leansearch: "A sheaf of modules on a ringed space with acyclic Cech
  complexes on arbitrary open covers has zero derived global sections in
  positive degrees". Service unavailable (Internal Server Error), recorded
  as unavailable; no mathematical verdict based on that result.
- msearch leanfinder: "Cech acyclicity on covers of every open subset implies
  acyclicity for right derived functors of sections of a module sheaf".
  Eight hits: Grothendieck/abelian category instances and abelian-sheaf
  cohomology definitions, none states this criterion.
- msearch loogle: `"cech"`. Twelve hits, including Cech nerves and unrelated
  Lean trace declarations; none states the criterion.
- msearch grep: `cohomology_isZero|exactAt_cechComplex|CechVanishing|cech_vanishing`:
  no Mathlib hits. Independently rg searched upstream WeilConjectures,
  project Sheaf, and dag/lean_names_upstream.json with the same pattern.
  I opened both upstream CechCriterion modules and their theorem signatures.
  They use abelian-sheaf Ext cohomology and a finite-family refinement
  hypothesis, not derived O_U-module cohomology for all opens with arbitrary
  covers. The project EtaleCechVanishingCriterion is for the etale site.
  None can be recorded as this node's exact existing declaration. No name
  collision was found. Existing shared definitions are used throughout.

No new nodes or dependency modules are delivered, and no statement_change
exists or is needed. The sandbox node differs from the base only in `lean`.
The module introduces no definitions, local notation, local instances, or
private copies. Its sole theorem remains `by sorry`; its docstring includes
both source places, the blueprint id, and all nine proof steps and their
DAG references. Lines are at most 100 characters. The node's lean.statement
was checked by exact string comparison with the file's signature.

Validation: lcompile.py compiled the module successfully (exit 0, 1.8 seconds),
without warnings or errors under the project's explicit-variable options.
The delivery dry run and server compilation are recorded by deliver2.py.
