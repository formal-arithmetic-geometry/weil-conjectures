## Worker report

Stage 2 for lem-sfb-scalar-dual-evaluation-descent. The Q60 reviewed record is a stage-1
split, not a Lean statement: the live node has `reviewed` but no `lean` or `reviewed_lean`.
This delivery preserves the complete stage-1 statement and proof and supplies its Lean
statement. No reopening or second split is requested.

Module: `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarDualEvaluationDescent`.
Main declaration: `SheafOfModules.exists_scalarDualEvaluationDescent`.
Only this theorem has `sorry`. Its docstring contains all five proof steps and the
source places. All auxiliary definitions have real data and express parts of this same
node, so no independent new notion, new node, or dependency repair is needed.

Hypotheses and clauses, in order:

1. The commutative ring is `R : Type (max u v)` with `[CommRing R]`. The site is
   `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`, the usual sieve presentation
   used by Mathlib and the dependency records. Objects and arrows have independent
   universes and both fit in the module universe `max u v`. There is no terminal-object,
   subcanonical, pullback, finiteness, nonempty-site, or characteristic hypothesis.
2. The sheaf of commutative rings is `B : Sheaf J CommRingCat.{max u v}`. The scalar map is
   `α : (constantSheaf J CommRingCat).obj (CommRingCat.of R) ⟶ B`.
3. Ordinary modules are `ModuleCat.{max u v} R`. Constant module sheaves use the recorded
   `siteConstantModuleFunctorGeneral J R`, via the already defined transparent coefficient
   transport `constantModuleHomFunctor J R`. That transport uses
   `constantModuleHomRingIso J R`; it is the existing constant-ring sheafification
   comparison, not an assumed isomorphism or a choice of new constant module functor.
4. `scalarConstantRealization J R B α V` abbreviates
   `changeOfRingsOfUniverses α ((constantModuleHomFunctor J R).obj V)`, exactly
   `B ⊗_{R̲} V̲`. This ordinary sheafification of sectionwise scalar tensor has the
   specified target B-module action. `scalarConstantRealizationMap` is its existing
   map on the constant module morphism.
5. `V*` is `ModuleCat.of R (V →ₗ[R] R)`. The target
   `scalarDualEvaluationTarget J R B α V` is the recorded `homObj (R := B)` of
   `C_B(V)` into `SheafOfModules.unit` of the underlying ring sheaf of B. The latter
   has exactly B's sections and restriction maps, with multiplication as its module action.
6. `scalarConstantGenerator ... V U b x` first uses `constantModuleHomUnit` to insert
   x in V̲(U), then uses the already defined `scalarExtensionRingIsoTmul` to insert
   `b ⊗ x` through the scalar-tensor sheafification unit. Despite its owning module's
   name, this helper takes any ring-sheaf morphism α and requires no isomorphism.
7. The first conjunct quantifies over every module V and states `∃! β, ...`, where β
   is a morphism of the actual B-module sheaf category with the displayed source and
   target. Its characterization is `ScalarDualEvaluationFormula ... V β`.
8. That formula quantifies over `U T : C`, every `a : T ⟶ U`, local coefficients
   `b : B(U)`, `b' : B(T)`, and arbitrary `φ : V →ₗ[R] R`, `x : V`. It evaluates the
   internal-Hom section at `op (Over.mk a)` on the generator `b' ⊗ x` and equates it
   to `B(a)(b) * b' * α_T(constant (φ x))`. For `a = id` this is exactly the node's
   `bb'α(φ(v))`; arbitrary a gives the same evaluation after every restriction.
   The constant scalar is explicitly the image under `toSheafify` of the constant
   commutative-ring presheaf, followed by α. No algebra structure is silently chosen.
9. β is a sheaf morphism, so its components already commute with all restrictions.
   Its internal-Hom sections are themselves natural maps on `C/U`. Thus the formula
   for every a simultaneously records the displayed evaluation on every localized site
   and its compatibility with relocalization. The restriction maps are the dependency's
   sectionwise `over` maps; no arbitrary comparison between unrelated local objects occurs.
10. The second conjunct quantifies over every `f : V ⟶ W` and every βV and βW satisfying
    that characterization. It asserts
    `βW ≫ homObjMap (scalarConstantRealizationMap ... f) (𝟙 _) =
     scalarConstantRealizationMap ... (ModuleCat.ofHom f.hom.dualMap) ≫ βV`.
    Lean's composition order is left-to-right. `f.hom.dualMap` is precomposition
    `ψ ↦ ψ.comp f.hom`, so this is exactly the contravariant naturality equation.
11. The last conjunct quantifies over arbitrary γ and γ' with the displayed source and
    target. Agreement of their evaluations on the same generators for every U,T,a,b,b',φ,x
    implies `γ = γ'`, with no assumption that either satisfies the scalar formula.
12. No `Module.Finite`, `Module.Projective`, `Module.Flat`, or finite-presentation
    instance occurs anywhere in the theorem's hypotheses.

Dependency declarations read and used:

- def-weil-size-convention: the recorded universe convention; implemented explicitly
  by u,v and module universe max u v, without identifying u and v.
- def-weil-pbc-sites-and-cohomology: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its unchanged Grothendieck-topology
  and sheaf conventions are used here. There is no covering-family data used by this node.
- def-weil-pbc-constant-sheaf: `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`; scalar constants use its `toSheafify` unit.
- def-sf-site-constant-module-functor:
  `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`,
  `siteConstantModulePresheafGeneral` and `siteConstantModuleFunctorGeneral`.
  `Sheaf.CategoryTheory.SiteConstantModuleHom` supplies the existing coefficient transport
  `constantModuleHomRingIso`, `constantModuleHomFunctor`, and constant section unit
  `constantModuleHomUnit`. No conclusion of its finitely presented Hom theorem is used.
- def-weil-sheaf-of-modules-category: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- def-pur-sheaf-tensor-product:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, retaining its public
  `TensorProductOfUniverses` interface: `SheafOfModules.changeOfRingsOfUniverses` and
  `changeOfRingsHomOfUniverses`. The existing pure-tensor unit is
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`,
  `SheafOfModules.scalarExtensionRingIsoTmul`. No conclusion of that module's
  ring-isomorphism theorem is used.
- def-pur-sheaf-hom:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`,
  `SheafOfModules.homObj`, `homObjMap`; its sections are the actual module morphisms
  on the slice, via `PresheafOfModules.restrictOver`.
- def-pur-localized-ringed-site:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`, `overFunctorMap`;
  `Over.mk a` expresses evaluation on the same slice objects.

The theorem nodes owning the two reused helper interfaces are not added as mathematical
statement prerequisites: only their definitions implement the already cited constant-module
and scalar-tensor notions, and their theorem conclusions supply no hypothesis or data.
All five same-node helper declarations are listed in `lean.declarations`.

All stated proof dependencies remain represented by imports: module sheafification and
its adjunction from Mathlib's `Presheaf.Sheafification`; tensor-sheafification comparison
from `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`;
bilinear descent from `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`;
slice tensor normalization from `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`;
constant restriction via `Mathlib.CategoryTheory.Sites.CoverLifting` and the `Over` framework.
These imports are proof-only when they do not define the statement's objects.

Sources checked locally: sites-modules.tex, definition-localize-ringed-site (03DH),
lemma-sheafification-tensor (0GMW), section-internal-hom (04TT), and sites-cohomology.tex,
lemma-dual-perfect-complex (08JJ). The latter's last comparison is the parent motivation;
the node is its explicit agent-written scalar specialization, rather than an assertion
that arbitrary V has invertible scalar evaluation.

Edge cases checked before writing:

- V = 0 and the zero coefficient ring: the formula gives zero, with no nonzero hypothesis.
- Infinite modules: all modules and all linear forms are quantified; no finite basis or
  expression by finitely many fixed generators is chosen.
- R = Z, V = Z/2, B = constant Z/2: V* = 0, so β is the zero map, which the statement
  allows. It asserts no isomorphism, injectivity, surjectivity or flat base change.
- Empty site and empty covering families: no object or section is selected; all local
  formulas are universal, and the zero/terminal sheaf cases remain included.
- Identity arrows, arbitrary restrictions, and nonidentity endomorphisms are all included
  by quantification over every `a : T ⟶ U`. Naturality includes zero and identity maps.
- Independent object and arrow universes are retained. Explicit universe arguments on
  `changeOfRingsOfUniverses.{v, u, max u v, max u v}` resolve an elaboration ambiguity;
  this adds no equality or size restriction to the mathematical statement.

Searches (2026-10-22):

- msearch.py leanfinder, "A balanced scalar evaluation pairing on constant module sheaves
  descends to the internal Hom sheaf and is natural in arbitrary modules": 8 hits,
  including ModuleCat.ihom_ev_app, LightCondensed internal-Hom points and
  SheafOfModules.unitHomEquiv variants. None states arbitrary scalar constant-module
  descent on a general site.
- msearch.py loogle, "Module.Dual.baseChange, SheafOfModules.homObj": 0 hits,
  unknown identifier SheafOfModules.homObj in the search service. The local upstream
  implementation of that declaration was read directly and reused.
- msearch.py grep, "dual|internalHom|evaluation", Algebra/Category/ModuleCat/Sheaf:
  6 hits on free sheaf evaluation and limits; no scalar-dual descent statement.
- rg in lean/WeilConjectures and lean/Sheaf for the exact item id and
  `scalarDualEvaluation`: no match. Broader scalar/evaluation and constant-module
  searches found the interfaces listed above, which are reused, but no exact theorem.
- rg in Mathlib's LinearAlgebra/Dual found the existing `LinearMap.dualMap`, used for f*.

No STATEMENT-DISPUTED flag or mathematical node fault was found. No node text was corrected.
The example CompactObject Sheaf module is now withdrawn; its node points to the upstream
WeilConjectures module, whose header, source docstrings and namespace conventions were read.

Validation: scompile.py compiled this module both in its private sandbox and at its
intended module path with no errors or warnings. The intended-path compile took 4.9 s.
The delivery dry run and push are recorded by the prescribed deliver2.py wrapper.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
