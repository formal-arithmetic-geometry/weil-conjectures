## Worker report

The module `Sheaf.AlgebraicGeometry.ClusterProductObstruction` states
`AlgebraicGeometry.Scheme.Modules.exists_subcluster_cohomology_obstruction`, with
its proof `sorry`. The three supporting definitions have real data:
`clusterSections` restricts the scalars of the existing section module;
`clusterCohomologyDimension` takes the finrank of the recorded module cohomology
with its induced k-action; `clusterQuadraticRestriction` constructs the canonical
function from the k-tensor product to the sections of the restricted tensor square.
No dependency is replaced, no extra theorem is postponed, and there is no new DAG
node or statement correction.

Source checked: Franciosi--Tenni, *The canonical ring of a 3-connected curve*,
Section 2, Lemma 2.12 and Remark 2.11, printed pp. 42--43, in the
[primary author PDF](https://pagine.dm.unipi.it/franciosi/lavori/franciosi-tenni2.pdf).
The paper's conventions in Section 2 were checked too. The DAG specializes the
source to reduced nodal curves and reduced clusters with smooth support. It
states the target as the restricted line itself, avoiding the source's choice of
an identification of that line on a zero-dimensional scheme. The six-step
natural-language proof in the docstring is the accepted DAG's diagonal-pairing
proof, including its characteristic-two check.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| k-scheme C and its structure | `(C : Scheme.{u}) (f : C ⟶ Spec (.of k))` |
| Projective | `[IsHProjective f]`, the dependency's finite-projective-space embedding convention |
| Nonempty and connected | `[ConnectedSpace C]`; this Mathlib class includes `Nonempty C` |
| Reduced | `[IsReduced C]` |
| Pure dimension one | `hpure` gives `topologicalKrullDim Z = 1` for every irreducible component with its subspace topology |
| Smooth except at ordinary nodes | `hnodal` quantifies over every point outside `f.smoothLocus` and requires its maximal-ideal-adic completed local ring to be isomorphic to the specified power-series quotient |
| Completed local node ring | `AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x)` and `MvPowerSeries (Fin 2) k ⧸ Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}` |
| Invertible O_C-module | `(L : C.Modules) [L.IsInvertible]` |
| A global section nonzero on every component generically | `heffective : ∃ s : Γ(L, ⊤), ∀ x : C, x ∈ genericPoints C → L.presheaf.germ ⊤ x trivial s ≠ 0`; `genericPoints` is Mathlib's set of component generic points |
| Closed subscheme S of C | `(S : Scheme.{u}) (i : S ⟶ C) [IsClosedImmersion i]` |
| Finite over k | `[IsFinite (i ≫ f)]`; finite means finite as a scheme over k, as confirmed by the DAG proof |
| Reduced S | `[IsReduced S]` |
| Support in the smooth locus | `hsmooth : ∀ x : S, i x ∈ f.smoothLocus` |
| S may be empty | No nonemptiness assumption on S |
| Quadratic product on H^0(C,L) tensor over k | `TensorProduct k (clusterSections f L) (clusterSections f L)` is the source of `clusterQuadraticRestriction` |
| a tensor b maps to restricted ab | `TensorProduct.mapOfCompatibleSMul` first sends each pure tensor to itself over Gamma(C,O_C); `tensorSectionsMap L L ⊤` is precisely the `tmulSection` product used by the recorded section ring; the unit of `tensorPullbackSectionAdjunction i` then restricts this actual section |
| Actual restricted tensor-square line as target | `Γ((tensorPullback i).obj (L ⊗ L), ⊤)`, without any chosen trivialization |
| Product restriction not surjective | `hquadratic : ¬ Function.Surjective (clusterQuadraticRestriction f i L)` |
| A nonempty closed T contained in S | `∃ (T : Scheme.{u}) (j : T ⟶ S), IsClosedImmersion j ∧ Nonempty T ∧ ...` |
| Ideal I_T as an O_C-module | `(j ≫ i).ker.toModules` is the recorded closed-immersion kernel ideal sheaf and its existing module realization |
| I_T tensor L | `(j ≫ i).ker.toModules ⊗ L` using the existing sheaf tensor product |
| h^q(C,F) | `clusterCohomologyDimension f F q` is `Module.finrank k` after restricting scalars on `(RingedSpace.moduleCohomology C.toRingedSpace q).obj F` along the actual structure map |
| The full inequality | The sum of dimensions for q=0,1 of the ideal tensor L is at least the sum of dimensions for q=0,1 of L |

The scalar ring homomorphism in both scalar wrappers is
`((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom`. The quadratic function retains
the Gamma(C,O_C)-module structure on the underlying sections explicitly, with
`IsScalarTower.of_compHom`; these are inherited structures, not extra hypotheses.
On pure tensors its formula is the section-normalized pullback unit applied to
`tmulSection a b`. The target sections need no chosen k-action to state
surjectivity. H^0 is written as ordinary global sections using its canonical
identification with degree-zero module cohomology; positive cohomology and all
four dimensions use the recorded module-sheaf cohomology, never the alternative
abelian-sheaf Ext encoding. Proper coherent cohomology makes all dimensions
appearing in the inequality finite, so finrank has no infinite-dimensional
fallback in this setting.

Dependency declarations and inspected sources:

- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` (full signature and docstring).
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim` (including its `WithBot ℕ∞` codomain).
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  actual section normalization `tensorPullbackSection`; its public import gives
  the original `tensorPullback` functor.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`; the scheme specialization is the
  existing `Scheme.Modules` tensor supplied by the invertible-module module.
- `def-sbc-closed-immersion-ideal-sheaf`: `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`,
  `AlgebraicGeometry.Scheme.Hom.ker`; the existing realization `toModules` is
  publicly imported from `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-sc-invertible-section-ring`:
  `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`,
  `AlgebraicGeometry.Scheme.Modules.sectionRingGMul` and `InvertibleSectionRing`;
  the used tensor-section operation and tensorator `tensorSectionsMap` are
  publicly imported from `WeilConjectures.AlgebraicGeometry.Modules.TensorSection`.
  The target `L ⊗ L` is the tensor square itself; no tensor-power unit factor or
  arbitrary isomorphism is inserted.
- `def-sc-ringed-space-module-cohomology`:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, the recorded right derived
  functor of `RingedSpace.globalSectionsFunctor`.
- `def-weil-algebraic-closure`: the Mathlib match includes `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, which is the predicate used here.
- `def-weil-connected-scheme`: its `mathlib_match` is `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`; the class includes nonemptiness.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`, with the ring structure from `.Algebra`.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`, specialized to `Fin 2`.

Every recorded proof dependency has its module imported privately, including the
Artinian decomposition, separating functional, orthogonal dimension and
rank-nullity Mathlib leaves. None is replaced or restated. There is no omitted
import due to a cycle.

Edge cases checked before writing:

- Empty S is allowed. Its target section group is zero, so the unique function
  onto it is surjective and the nonsurjectivity hypothesis is false.
- Empty C is excluded by the node and by `ConnectedSpace C`; no extra independent
  nonemptiness binder has been added.
- Reducible curves are covered: effectivity tests every component generic point,
  and pure dimension tests every component separately; no integral-curve instance
  is assumed.
- Disconnected subclusters T are allowed. Nonempty is the only connectedness-type
  condition imposed on T.
- A global section need not be nonzero at any chosen smooth point. The effectivity
  assumption concerns component generic points only.
- In characteristic two the nondegenerate diagonal pairing still gives
  W contained in W-perp and 2r <= |T|; the construction never divides by two.
- On P^1 with L=O and two distinct reduced points, the restricted product space is
  the diagonal line, and T equal to both points gives the equality case
  h0(O(-2))+h1(O(-2)) = 0+1 = h0(O)+h1(O).
- All schemes, coefficients and sheaf sections use the common explicit universe u;
  finite closed subschemes fit this universe. No hidden auto-bound variables or
  independent smaller test universe occur.

Searches performed before adding the module:

1. `msearch.py NE lem-sfb-cluster-product-obstruction leanfinder` with query
   "Failure of quadratic section multiplication restricted to a finite cluster on
   a projective curve gives a nonempty subcluster with h0 plus h1 of its ideal tensor
   line bundle at least h0 plus h1 of the line bundle": eight unrelated elliptic-curve
   hits, no matching statement.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.Scheme.Modules, TensorProduct.lift, Module.finrank`:
   zero hits.
3. `msearch.py ... grep` with query `cluster|nodal|quadratic.*restriction`,
   subdirectory `AlgebraicGeometry`: zero Mathlib hits.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the node id:
   no matching declaration. Searches for nodal curves, generic nonvanishing,
   cohomology scalar restriction and tensor sections found the existing APIs used
   above, including the neighboring nodal very-ampleness statement and its
   completed local-ring signature, but no quadratic cluster obstruction.
5. Exact-name searches over Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for
   `clusterSections`, `clusterCohomologyDimension`, `clusterQuadraticRestriction`
   and `exists_subcluster_cohomology_obstruction`: no existing declarations.

Validation: `scompile.py NE lem-sfb-cluster-product-obstruction` compiled the
sandbox file and named library module cleanly. During construction a nonexistent
Mathlib ideal-module import was replaced by the actual upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`; this was an import
repair, with no change to any definition or statement. The scalar-tower
construction uses existing structure terms and has no postponed proof.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
