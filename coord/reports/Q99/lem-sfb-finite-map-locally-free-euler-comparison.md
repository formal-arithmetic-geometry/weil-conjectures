## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteMapLocallyFreeEulerComparison` states
`AlgebraicGeometry.Scheme.Modules.finite_map_locally_free_euler_comparison`.
Its only theorem has proof `sorry`; there are no new definitions or other holes.
The node changes only in `lean`. No statement correction, dependency repair, or
new DAG node is needed. No statement dispute was found.

The source was read at Stacks `cohomology.tex`, lemma-projection-formula (01E8),
including the final local-free argument; `coherent.tex`,
lemma-relative-affine-cohomology (089W); and the recorded dependency declarations.
The current blueprint unit sk-thm-sf-ctf-stability was also read. This is its
already reviewed descendant finite-map tool, not a change to the unit.

Hypotheses, with every clause matched:

- Field k: `(k : Type u) [Field k]`.
- Schemes X and Y over k: `{X Y : Scheme.{u}}`, with
  `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]`.
- Properness of both structure morphisms: the two `IsProper` binders.
- Local Noetherianity: `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]`.
- Finite k-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsFinite f]`.
  The IsOver condition asserts compatibility with exactly the supplied structure
  maps. There are no flatness, dominance, dimension, or integrality binders.
- Variable-rank finite locally free E: `(E : Y.Modules)` with
  `[SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]`. The existing predicate has
  local finite generating sets whose sizes can vary; it includes rank zero.
- Any coherent N: `(N : X.Modules)` and
  `(hN : RingedSpace.IsCoherent X.toRingedSpace N)`.

Conclusions, in their Lean order:

- `SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((tensorPullback f).obj E)`
  is finite local freeness of ordinary pullback.
- `E.IsInvertible → ((tensorPullback f).obj E).IsInvertible` is the conditional
  rank-one clause. Invertibility is not assumed for the other conclusions.
- The six successive `RingedSpace.IsCoherent` conjuncts are, respectively, E,
  f*E, f_*N, f*E tensor N, f_*(f*E tensor N), and E tensor f_*N. They use the
  exact finite-type-plus-finite-type-kernel predicate, not merely finite type.
- The existential isomorphism `α : E ⊗ (pushforward f).obj N ≅ ...` has the
  exact source and target of the projection map. Its hom on **every** open U
  sends `tmulSection e n` to `tmulSection (eta(e)) n`, where eta is the unit of
  the recorded section-normalized `tensorPullbackSectionAdjunction f`.
  This specifies the canonical projection, rather than an unconstrained
  isomorphism. Tensor sections generate locally by tensor sheafification, so
  the displayed rule uniquely determines the morphism. It does not assert that
  arbitrary sections are pure tensors or choose an arbitrary comparison map.
- For each `G = N ∨ G = (tensorPullback f).obj E ⊗ N` and `q : ℕ`, the next
  conjunct asserts `IsIso (moduleCohomologyEdgeMap f G q)`. This is exactly
  the recorded identity h-map edge map, not an abstract cohomology equivalence.
  The accompanying equality for every `a : k` and cohomology element x says
  that it intertwines the scalar actions through
  `Scheme.globalSectionsRingHom k (X := Y)` and `(X := X)`. Together with the
  additive-group isomorphism, this is exactly a k-vector-space isomorphism.
  The explicit `@id` fixes the target's global-function module interpretation.
- For each of the two modules on X, finite dimensionality in every degree is
  `FiniteDimensional k` on the recorded `RingedSpace.moduleCohomology` object
  after `ModuleCat.restrictScalars` along the structure ring homomorphism.
  Eventual vanishing is `∃ b : ℕ, ∀ q : ℕ, b < q → Subsingleton ...`.
- The corresponding Y clause covers f_*N, f_*(f*E tensor N), and
  E tensor f_*N, with the same scalar restriction and eventual vanishing.
  These are the cohomology groups in the displayed comparisons and the
  projection-isomorphic Euler expression. The bound can depend on the module;
  the finite list also admits a common bound by taking a maximum.
- The final two equalities use the existing `eulerChar k` for precisely
  `N`, `(pushforward f).obj N`, `(tensorPullback f).obj E ⊗ N`, and
  `E ⊗ (pushforward f).obj N`. This retains the dependency's existing Euler
  definition. Its underlying abelian-sheaf cohomology is canonically identified
  with module-derived cohomology; no second Euler or cohomology definition is
  introduced.

Statement-dependency interfaces read and used (names without namespace below are
in `AlgebraicGeometry.Scheme.Modules`, except as explicitly qualified):

| Node | Module | Declaration/interface used |
| --- | --- | --- |
| def-weil-field | Mathlib.Algebra.Field.Defs | `Field` |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | `AlgebraicGeometry.IsFinite` |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | `AlgebraicGeometry.IsProper` |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | `AlgebraicGeometry.IsLocallyNoetherian` |
| def-sc-finite-locally-free-sheaf | WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree | `SheafOfModules.IsFiniteLocallyFree` |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType | publicly exposes `AlgebraicGeometry.RingedSpace.IsCoherent` from WeilConjectures.AlgebraicGeometry.Coherent |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | publicly exposes `tensorPullback`; `tensorPullbackSectionAdjunction` fixes its unit on sections |
| def-pur-sheaf-tensor-product | Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses | public existing sheaf-tensor monoidal interface; `⊗` uses the scheme's existing localization tensor |
| def-sc-invertible-module | WeilConjectures.AlgebraicGeometry.Modules.Invertible | `IsInvertible` |
| def-weil-pbc-module-cohomology-fmap | WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap | `moduleCohomologyEdgeMap` |
| pqf-def-cohomology | WeilConjectures.AlgebraicGeometry.PQFCohomology | `sheafCohomologyAndHigherDirectImages` identifies the existing `RingedSpace.moduleCohomology` |
| def-pc-euler-characteristic | WeilConjectures.AlgebraicGeometry.Cohomology.Defs | `eulerChar`, `Scheme.globalSectionsRingHom` |

`WeilConjectures.AlgebraicGeometry.Modules.TensorSection.tmulSection` is the
existing section operation for the same sheaf tensor; it is not redefined.

Every recorded proof-dependency module is imported, with plain imports for those
needed only by the postponed proof. In addition to the statement dependencies,
these are CoherentFiniteTypeLocallyNoetherian
(`isCoherent_iff_isQuasicoherent_and_isFiniteType`), FinitePushforwardCoherent
(`isCoherent_pushforward_of_isFinite`), CoherentModuleLocalOnOpenCover
(`AlgebraicGeometry.coherent_module_local_on_open_cover`), CoherentKernelCokernelSum
(`RingedSpace.coherent_kernel_cokernel_sum`), Modules.PullbackFreeGenerator
(`Hom.isIso_of_forall_bijective_app`), AffineMorphismCohomologyEdge
(`affine_morphism_cohomology_edge`), and Cohomology.EulerCharProper
(`finite_setOf_nontrivial_H_of_isProper`, `finite_support_finrankH_of_isProper`),
all under WeilConjectures.AlgebraicGeometry. Their signatures and docstrings were
read. The theorem docstring reproduces all seven steps of the accepted split.

Edge cases checked mathematically before writing: zero local rank makes both
projection sides zero; variable ranks require no common rank binder; E invertible
is only an implication; N=0 has zero cohomology and Euler characteristic. Empty X
and empty Y are allowed, with no Nonempty assumptions. Degree q=0 is included.
Finite nonflat closed immersions and nonreduced proper schemes are allowed.
There is no smoothness or characteristic assumption. All size variables are
explicit; the coefficient and scheme universe u is the existing ordinary-module
interface and can be raised to contain any given field and schemes. The initial
compiler inference of finite-local-freeness at universe zero was repaired by its
explicit universe arguments, without restricting u.

Searches on 2026-10-24 through the prescribed msearch.py wrapper:

- LeanFinder: `finite morphism proper schemes finite locally free sheaf projection
  formula Euler characteristic coherent cohomology`. Eight hits concerned finite
  morphism infrastructure (IsFinite, finite fibres, composition/base change), with
  no matching theorem.
- Loogle: `"projectionFormula"`. Zero hits.
- Mathlib grep: `projectionFormula|projection_formula|euler.*pushforward|pushforward.*euler`.
  Zero hits.
- LeanSearch: `finite morphism proper schemes finite locally free projection formula
  coherent Euler characteristic`. Eight hits concerned IsFinite/IsProper and their
  affine characterizations; no matching comparison theorem.
- rg in the project's WeilConjectures and Sheaf trees for projectionFormula,
  projection_formula, Euler/pushforward combinations, tensorPullback, and the item
  id. No copy of this statement or declaration was found. The existing
  Modules.ProjectionFormula.projectionHom uses Mathlib's ordinary pullback with
  opposite tensor order, and its isomorphism theorem assumes an invertible module.
  It does not give this finite-variable-rank tensorPullback statement, including
  all coherence and canonical edge/Euler clauses. Derived etale/proetale projection
  statements likewise concern different categories and coefficient objects.

Validation: scompile.py compiled the one delivered file both as a sandbox module
and at its actual library module path, with no errors or non-sorry warnings.
No local Lean build, shared-source edit, or direct Git mutation was performed.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
