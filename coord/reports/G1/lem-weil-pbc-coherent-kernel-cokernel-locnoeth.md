## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian` states
`AlgebraicGeometry.Scheme.Modules.isCoherent_kernel_cokernel_biprod_and_submodule`.
Its proof is exactly `sorry`; no definition or proof is added. The node is unchanged except
for its `lean` field. No new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause matching:

- The locally Noetherian scheme is `(X : Scheme.{u}) [IsLocallyNoetherian X]`.
  There is no global Noetherian, quasi-compactness, separatedness, field, or base hypothesis.
- The category `Mod(O_X)` is `X.Modules`, Mathlib's scheme specialization of
  `SheafOfModules.{u} X.ringCatSheaf`. Its morphisms are module-sheaf morphisms.
  Mathlib's existing abelian structure supplies the actual ambient kernels, cokernels
  and binary biproducts; no category of coherent modules is substituted.
- Part (1) quantifies over arbitrary `F G : X.Modules`. Coherence of each is rendered by
  `RingedSpace.IsCoherent X.toRingedSpace F` and the corresponding expression for `G`.
  For every `φ : F ⟶ G`, the conclusion gives coherence of `kernel φ` and `cokernel φ`.
  The separate final conjunct gives coherence of `F ⊞ G`, the binary direct sum.
- Part (2) quantifies independently over `F F' : X.Modules` and `i : F' ⟶ F`.
  Its hypotheses are coherence of `F`, `Mono i` (the inclusion of a submodule), and
  `SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F'`.
  Its two conclusions are coherence of `F'` and of `cokernel i`, exactly `F/F'`.
  A monomorphism represents a submodule up to its canonical identification with its image;
  all literal submodule inclusions are covered, and every such monomorphism is an inclusion
  after this identification. No coherence or finite-type assumption is imposed on `F'`.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`. The full class and docstring say Noetherian
  sections on all affine opens; its recorded affine-cover equivalences identify this with
  the node's definition.
- `def-weil-sheaf-of-modules-category`: `SheafOfModules`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`; read its structure, `Hom`, category instance,
  and the abelian instance in `.Sheaf.Abelian`. Its specialization is `Scheme.Modules`
  in `Mathlib.AlgebraicGeometry.Modules.Sheaf`, read together with its abelian, limits,
  and colimits instances. These are imported transitively through `Coherent`.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`,
  `Sheaf.AlgebraicGeometry.Coherent`. Its full definition is finite type plus finite-type
  kernels of every finite free map on every open. The same module uses Mathlib's
  `SheafOfModules.IsQuasicoherent` for quasi-coherence. Its carrier on `X.toRingedSpace`
  is definitionally the carrier of `X.Modules`; no replacement predicate is defined.

Sources checked: the local Stacks checkout is absent on this machine, so opened
https://stacks.math.columbia.edu/tag/01Y0 and https://stacks.math.columbia.edu/tag/01Y1.
01Y0 gives kernels and cokernels (and extensions, hence binary sums); 01Y1 gives
quasi-coherent submodules and quotients. The module docstring includes all three proof
steps of the node and names every proof dependency used there.

Edge cases checked before writing: the empty scheme is allowed; zero modules, zero maps,
the zero submodule, and the whole submodule are allowed. The theorem has no positive-rank,
nonempty, integrality, or characteristic restriction. Non-quasi-coherent submodules are
correctly excluded: quasi-coherence is a real hypothesis, as also explained in the comments
on Stacks 01Y1. `u` is explicitly declared and all objects and morphisms are explicitly bound.
No independent small universe is introduced for any test object.

Searches (executed via `/home/ubuntu/weil-launcher/msearch.py` and recorded in
`searches.jsonl`):

- LeanFinder: "Kernels cokernels direct sums of coherent modules on a locally Noetherian
  scheme are coherent and quasi-coherent submodules are coherent": eight hits, including
  `Scheme.Modules.instAbelian`, `SheafOfModules.IsFiniteType`, `IsQuasicoherent` and
  `instIsQuasicoherentOfIsFinitePresentation`; none is the closure statement.
- Loogle: `SheafOfModules.IsCoherent, kernel, cokernel`: zero hits, unknown identifier
  `SheafOfModules.IsCoherent`.
- LeanSearch: "coherent sheaves kernels cokernels quasi-coherent submodules locally
  Noetherian scheme": service unavailable, Internal Server Error. No negative verdict
  inferred from the unavailable service.
- Mathlib grep: `IsCoherent|coherent.*(kernel|cokernel)|isCoherent`, in AlgebraicGeometry:
  one unrelated ideal-sheaf comment about the largest quasi-coherent ideal in a kernel.
- Source repository `rg` for `isCoherent|IsCoherent` and for the item id: the latter has no
  matches; the former finds `WeilConjectures/AlgebraicGeometry/Modules/Coherent.lean` and
  uses in duality/cohomology. Read the source definition: it is quasi-coherence plus finite
  presentation, not the dependency's Stacks predicate. No identical closure statement found.
- Project `rg` for coherent kernels/cokernels and coherence: found the dependency module,
  finite-presentation siblings and docstring uses of this item, but no identical theorem.
- Name-collision `rg` for `isCoherent_kernel_cokernel_biprod_and_submodule` in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches.

Validation: server compilation is used; an initial ring-sheaf inference error in the
quasi-coherence expression was repaired by explicitly giving `(R := X.ringCatSheaf)`.

## Second reading by G1

Read the sandbox node and module independently, then opened all three statement dependency
nodes and their recorded declarations. No mathematical mismatch was found; the Lean module,
node statement, and recorded signature are retained. This second reading adds this audit only.

Objects, hypotheses, and conclusions of the node, matched individually:

1. An arbitrary scheme X: `(X : Scheme.{u})`. Verdict: same object, with an explicitly bound
   universe; no affine, integral, separated, base-ring, or field restriction.
2. X locally Noetherian: `[IsLocallyNoetherian X]`. Verdict: exact. Read the class in
   `Mathlib.AlgebraicGeometry.Noetherian` (Noetherian sections on every affine open), and its
   recorded affine-cover equivalence; these give the node's existential affine-cover notion.
   Global Noetherianity and quasi-compactness are not assumed.
3. The ambient category Mod(O_X), with O_X-linear morphisms: `X.Modules` and `F ⟶ G`.
   Verdict: exact. Read `Scheme.Modules`, its `Hom`, category, Abelian, limits and colimits
   instances in `Mathlib.AlgebraicGeometry.Modules.Sheaf`, and `SheafOfModules` and its `Hom`
   in `Mathlib.Algebra.Category.ModuleCat.Sheaf`. These are the recorded dependency's
   sheaves of modules and sectionwise linear maps, not a coherent full subcategory.
   The Abelian structure comes from Mathlib's sheafification adjunction; the scheme forgetful
   functor to presheaves preserves limits. Thus categorical kernels give sectionwise kernels
   and categorical cokernels give the sheafified sectionwise quotients required by the node.
4. Part (1), coherent F and G: independent arbitrary `(F G : X.Modules)` followed by
   `RingedSpace.IsCoherent X.toRingedSpace F` and the same predicate for G. Verdict: exact.
   Opened `Sheaf.AlgebraicGeometry.Coherent`: its predicate is finite type plus finite-type
   kernels of every finite free map on every open, exactly `pqf-def-coherent`. Its carrier
   uses `moduleRings X.toRingedSpace`, definitionally the scheme ring sheaf. The upstream
   `Scheme.Modules.isCoherent` is quasi-coherence plus finite presentation; it is not used
   as a substitute for the dependency's general Stacks definition.
5. Every O_X-linear map between these objects: `(∀ (φ : F ⟶ G), ...)`. Verdict: exact,
   with no monomorphism, epimorphism or nonzero hypothesis.
6. Kernel coherent: `RingedSpace.IsCoherent X.toRingedSpace (kernel φ)`. Verdict: exact.
7. Cokernel coherent: the accompanying conjunct with `(cokernel φ)`. Verdict: exact.
8. Binary direct sum coherent: the separate conjunct with `(F ⊞ G)`. Verdict: exact;
   this is the ambient binary biproduct. Both coherence hypotheses scope over this clause,
   independently of any choice of φ.
9. Part (2), coherent F and submodule F': independent `(F F' : X.Modules) (i : F' ⟶ F)`,
   coherence of F, then `Mono i`. Verdict: exact subobject formulation. A module-sheaf
   monomorphism identifies its source with its image subsheaf; every literal subsheaf
   inclusion is a monomorphism. No hypothesis is placed on an unrelated embedding or map.
10. F' quasi-coherent: `SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F'`.
    Verdict: exact. Read the Mathlib class and its local-presentation definition in
    `Sheaf.Quasicoherent`, and the dependency's identification with affine-local tilde
    modules on schemes. No finite-type or coherence hypothesis on F' has been added.
11. F' coherent: `RingedSpace.IsCoherent X.toRingedSpace F'`. Verdict: exact.
12. Quotient F/F' coherent: the final conjunct with `(cokernel i)`. Verdict: exact quotient
    of the inclusion, not an arbitrary independently quantified quotient. Both conclusions
    have precisely the three hypotheses of part (2); the two parts are independent conjuncts.

Source reading: the local Stacks .tex checkout is absent. Read the actual `coherent.tex`
from https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex at
`lemma-coherent-abelian-Noetherian` and
`lemma-coherent-Noetherian-quasi-coherent-sub-quotient`, as well as the rendered
https://stacks.math.columbia.edu/tag/01Y0 and https://stacks.math.columbia.edu/tag/01Y1.
Both lemmas explicitly assume locally Noetherian X; neither assumes a field, separatedness,
quasi-compactness, or an extra ambient hypothesis. The sum clause follows from the extension
clause of 01Y0. The node takes the submodule and its quotient consequence of 01Y1; the Lean
renders that exact node, rather than adding the source's separate arbitrary-quotient clause.
There is no statement correction and therefore no corrected-citer audit to perform.

Edge cases: empty schemes, zero modules, zero maps, zero submodules and identity inclusions
are all quantified over. The binary sum includes sums with zero; no index set is introduced,
so empty-index cases impose no hidden assumption. The dependency's free rank n is arbitrary
including n = 0. No characteristic restriction occurs. All scheme, module and morphism
universes are the standard Scheme.{u}/X.Modules ones with arbitrary explicit u; there is
no smaller independent test universe and no unbound variable. Quasi-coherence of F' remains
necessary: arbitrary subsheaves of a coherent sheaf need not be quasi-coherent.

Independent searches, with different words from the worker's queries, recorded by msearch:

- LeanFinder: `Noetherian schemes coherent sheaf closure under subobjects and finite
  biproducts`: eight hits, including IsLocallyNoetherian, IsNoetherian, IsFiniteType and
  affine-cover Noetherian criteria, no closure statement.
- Loogle: `"coherent", "kernel"`: zero hits.
- LeanSearch: `Coherence preserved by binary sums and quotients of module sheaves on
  Noetherian schemes`: service unavailable (Internal Server Error); no negative conclusion
  is inferred from that failure.
- Mathlib grep: `coherent.*(subobject|biprod|cokernel|kernel)|IsCoherent` in AlgebraicGeometry:
  only an unrelated ideal-sheaf kernel comment.
- Independently searched all `WeilConjectures` and the project's `lean/Sheaf` for IsCoherent,
  isCoherent and coherent kernel/cokernel/sum/submodule expressions. Opened upstream
  `Modules.Coherent` and `Modules.QuasicoherentKernel.isFinitePresentation_kernel`.
  The latter proves only finite presentation of a kernel (with a finitely presented source
  and quasi-coherent target); it is not the full conjunction or the dependency's predicate.
  Other results concern specialized coherent cohomology or ideal sheaves. In this project,
  the matches are the coherence definition and documentation citing this item, not a second
  existing closure theorem. No additional definition or dependency module is needed.

H5/H6/H8/H9: the delivery has no definitions, no hollow data and one theorem whose entire
proof is `sorry`. The module and theorem docstrings give 01Y0/01Y1 and the item's blueprint
id; the theorem docstring follows all three proof steps and names their dependencies.
Imports supply coherence, ambient module operations and local Noetherianity; names and
100-character lines follow the conventions. The node's lean.statement matches the file's
signature verbatim. No mathematical or Lean changes were necessary.

Validation: ran scompile from the sandbox on the delivered module; server compilation
succeeded in 2.4 seconds with exit code 0 and no warnings. The initial invocation from the
read-only repository used a nonexistent relative sandbox path; rerunning with the sandbox
working directory resolved that invocation error without changing any project file.
