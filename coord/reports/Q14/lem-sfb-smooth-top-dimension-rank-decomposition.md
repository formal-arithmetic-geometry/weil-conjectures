## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothTopDimensionRankDecomposition` states
`AlgebraicGeometry.Scheme.Modules.exists_smoothTopDimension_rank_decomposition`.
It has one theorem, with proof `sorry`, and three explicit Prop-valued definitions
belonging to the conditions introduced in the item's own statement. No extra node,
dependency repair, statement correction, or mathematical proof is delivered.
The theorem docstring carries all eight steps of the accepted natural-language proof.

The inherited BLOCKED ending concerned the stage-1 split: the current node has
`reviewed.result = pass` by Q51, no `lean`, no `reviewed_lean`, no released repair
note, and its queue entry is stage 2, action `state`. The handoff rule at the start
of coord/brief-stage2.md expressly permits recording its Lean statement. This
packet preserves every accepted stage-1 field.

Statement matching, hypothesis by hypothesis and clause by clause:

* Affine schemes S and X: `{X S : Scheme.{u}} [IsAffine X] [IsAffine S]`.
* The map is `(g : X ⟶ S)`. The nonnegative constant dimension is `(a : ℕ)`;
  `[SmoothOfRelativeDimension a g]` includes smoothness itself, using the recorded
  definition, without an additional hypothesis. `[GeometricallyIrreducible g]`
  gives geometrically irreducible **nonempty** fibres: Mathlib's definition uses
  `IrreducibleSpace`, which includes nonemptiness. No separate surjectivity or
  nonempty-source assumption is added; an empty base remains admissible.
* The module is `(E : X.Modules) [E.IsQuasicoherent] [E.IsFinitePresentation]`.
  These are precisely quasi-coherence and finite presentation, with neither a
  Noetherian assumption nor coherence in a stronger sense.
* A test S-scheme is an arbitrary `T : Over S`. Its fibre product is
  `Limits.pullback g T.hom`; the structure map to T is `pullback.snd g T.hom`.
  Its module is `(tensorPullback (pullback.fst g T.hom)).obj E`, the recorded
  canonical tensor construction, not an arbitrary adjoint.
* `smoothGenericFreeRankCondition g E r T` defines the predicate of H_r. For
  every t and fibre point ξ satisfying `IsGenericPoint ξ Set.univ`, it requires
  an ambient open `W : (Limits.pullback g T.hom).Opens` containing the image of ξ
  under `fiberι`, and an isomorphism `E_T.over W ≅ SheafOfModules.free
  (ULift.{u} (Fin r))`. The `over` restriction and the free object use the same
  restricted ring sheaf. In particular the neighbourhood is in X_T, not just
  in its fibre; freeness is not imposed on the whole fibre or inverse image.
  Quantification over generic points equals the unique-point condition under
  the given geometric irreducibility and sobriety of schemes.
* `smoothTopDimensionFlatCondition g E a T` defines the predicate of F_a.
  At each x in X_T, `(a : Cardinal.{u}) ≤ Algebra.trdeg ...` is exactly the
  transcendence-degree threshold, using the algebra induced by
  `(pullback.snd g T.hom).residueFieldMap x`. The conclusion is `Module.Flat`
  on the actual E_T stalk with scalars restricted by the structure `stalkMap`.
  Thus the base point t is exactly the image of x, not an unrelated point;
  no arbitrary algebra or module structure is assumed. The general affine-local
  `IsFlatOver` predicate cannot express a condition only on the top-dimensional
  points, so the statement uses its underlying `Module.Flat` stalk formulation.
* H is a family indexed by all `ℕ`, and F and all H_r are sheaves for
  `Scheme.zariskiTopology.over S`. Their objectwise `Subsingleton` condition
  and `Nonempty ↔` the respective predicates say exactly singleton-or-empty.
  They determine their restriction maps uniquely, so there is no unspecified
  functorial action. Types in `Type (u+1)` permit the big site; all test schemes
  are `Scheme.{u}`, and no relation between independent universe parameters is
  imposed. There are no automatic implicit variables.
* `∃ c : ℕ` is one uniform nonnegative rank bound. For all r greater than c,
  `Nonempty (IsInitial (H r))` says H_r is the initial sheaf. This is the
  meaning of empty in the accepted proof: empty on nonempty test schemes,
  singleton on the empty test scheme. Literal objectwise emptiness even at the
  empty scheme would contradict the very definition of H_r; the accepted proof
  already explicitly resolves that convention, so no statement change is needed.
* `∃ ι : ∀ r : Fin (c+1), H r.val ⟶ F, Nonempty (IsColimit (Cofan.mk F ι))`
  is exactly the sheaf coproduct identity. It includes existence of the canonical
  inclusions: their source and target are subterminal, so any such morphism is
  unique. Stating the colimit universal property avoids any unnecessary
  assumption that a generic sheafification construction is available on this
  large site. It retains arbitrary target sheaves in the universal property.
* `smoothGenericRankPartition` takes `U : Fin (c+1) → T.left.Opens` and
  requires each carrier closed, pairwise disjointness, supremum top, and H_r
  on `Over.mk ((U r).ι ≫ T.hom)`. These open subschemes give exactly the stated
  rank-labelled decomposition. The final equivalence is between F_a(T)'s
  predicate and `∃! U, smoothGenericRankPartition ... U`. Equality of open
  subsets gives the stated unique decomposition as subschemes of T, rather
  than a stronger choice of arbitrary abstract representatives.

Dependencies read and used:

* def-pc-scheme and def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, and `Spec.map` (affine scheme
  predicate and residue-field fibres use this scheme convention).
* def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth` and `SmoothOfRelativeDimension` (the latter implies
  the former). The definition and its full signature were read.
* def-pc-geometrically-irreducible: its recorded
  Mathlib.AlgebraicGeometry.Geometrically.Integral import exports
  `AlgebraicGeometry.GeometricallyIrreducible`; the irreducible and integral
  signatures and docstrings were read. Only geometric irreducibility is assumed.
* pqf-def-coherent: Sheaf.AlgebraicGeometry.CoherentFiniteType,
  `Scheme.Modules.IsQuasiCoherentFiniteType` was read; it is the conjunction of
  the standard quasi-coherence and finite-type predicates. The current node
  needs the former and the separate stronger finite-presentation predicate,
  so no copy of that conjunction is made or assumed unnecessarily.
* def-weil-pbc-module-finite-type-presentation:
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators `SheafOfModules.IsFiniteType`
  and Quasicoherent `SheafOfModules.IsFinitePresentation`; the latter is used
  directly. Its definition is the local finite presentation by free sheaves.
* def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
* def-pc-module-pullback: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  `Scheme.Modules.tensorPullbackSectionAdjunction` and the publicly imported
  `tensorPullback` from WeilConjectures.AlgebraicGeometry.TensorPullback. Both
  modules and the tensor object construction were read.
* def-sc-generic-point: Mathlib.Topology.Sober `IsGenericPoint`, exactly
  `closure {ξ} = Set.univ` in the fibre.
* def-pc-scheme-module-flat-over:
  WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
  `Scheme.Modules.IsFlatOver`, whose docstring identifies it with the canonical
  base-local-ring stalk condition used here. `RingedSpace.moduleStalkFunctor`
  from WeilConjectures.Algebra.Homology.ModuleStalkFunctor supplies that actual
  stalk as a module over the structure stalk, with its canonical scalar action. Its general predicate is imported
  but is not incorrectly used to require flatness at all points of X_T.
* def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap` with its local-ring origin.
* def-kun-transcendence-degree:
  Mathlib.RingTheory.AlgebraicIndependent.Basic `Algebra.trdeg`, cardinal-valued.
* def-pc-zariski-sheaf-property has no Lean record and its exact mathlib_match
  is used: `CategoryTheory.Presieve.IsSheaf`. Mathlib's `Sheaf` packages its
  equivalent categorical sheaf predicate; BigZariski defines the topology and
  CategoryTheory.Sites.Over transports it to S-schemes as documented there.

All recorded statement-dependency modules are public imports; the modules of
all stated proof dependencies are ordinary imports. Mathlib leaves use their
recorded source modules, including affine permanence, smooth permanence,
quasi-separatedness, reduced localizations, and flat-lfp openness. The sole
unstated proof dependency is lem-sfb-smooth-generic-rank-locus-representability;
it is used only for functoriality of H_r in proof step 8 and has no module to
import. Its absence does not prevent stating the current node: no object is
borrowed from it, and the corresponding predicate is introduced by this node.

Searches for an existing exact declaration:

* msearch.py leanfinder, query "Flatness over base at fibre generic points
  decomposes into finitely many locally constant generic free ranks for a smooth
  affine morphism": eight results, including Algebra.Smooth.flat,
  AlgebraicGeometry.flat_iff, Flat.generalizingMap, Flat.iff_flat_stalkMap, and
  smooth chart results. None states the relative generic-free-rank decomposition.
* msearch.py loogle, query "AlgebraicGeometry.SmoothOfRelativeDimension,
  SheafOfModules.free, CategoryTheory.Sheaf": zero results.
* msearch.py grep, query "generic.*rank|rank.*generic|flat.*dimension" in
  AlgebraicGeometry: zero results.
* msearch.py leansearch, query "A smooth affine morphism with geometrically
  irreducible fibres has a finite clopen decomposition of the top dimensional
  flatness functor by free ranks near fibre generic points": eight results,
  smoothness definitions and composition, smooth-implies-lfp, RingHom.Smooth,
  and Flat.flat_appLE. No exact result.
* rg of lean/WeilConjectures and lean/Sheaf for GenericRank, genericRank,
  generic-rank, topDimension, TopDimension, FlatInDimension, flatInDimension,
  generic-free-rank and rank-decomposition phrases found absolute generic rank,
  GenericFreeBlowup, and Picard rank strata. These are distinct statements.
  The upstream `GenericRank.lean` concerns absolute rank on an irreducible scheme;
  `GenericFreeBlowup` changes the base by a blowup and does not supply this result.
* Search for the exact blueprint id in lean/WeilConjectures returned no hit.
  The four proposed fully qualified declaration names also have no hit in
  Mathlib, WeilConjectures, or Sheaf. Existing `SheafOfModules.free`, restriction,
  fibre, canonical residue-field map, and tensor pullback are reused.

Edge cases checked against the source and accepted proof:

* Empty T: the H_r and F_a predicates are vacuous. All sheaves have one section
  there, including initial H_r. Every rank piece is empty, and the partition is
  unique. Empty S and hence empty X are also allowed.
* Rank zero and the zero module: `Fin 0` gives the zero free sheaf. For zero E,
  choose c=0 and take U_0=T. No positive-rank hypothesis is hidden in the code.
* T disconnected: ranks may vary, because the partition is by clopen opens and
  the coproduct is in the sheaf category, not pointwise disjoint union of sets.
* a=0: no nonnegative transcendence degree is excluded, consistent with all
  fibre points of smooth zero-dimensional irreducible fibres being generic.
* On A¹ over a field, O/(x) is zero near the generic point, so rank zero is
  allowed despite not being free on the entire fibre. Over k[t], O/(t) at the
  fibre generic point over t=0 is not base-flat, so neither side holds on the
  full base; no field-fibre-only flatness condition is accidentally substituted.
* Tests may be nonaffine, non-Noetherian, or nonquasicompact: only X and S have
  affineness binders. There is no finite-cover restriction on the partition test.

No STATEMENT-DISPUTED flag or unhandled node fault remains. Validation uses only
scompile.py and deliver2.py; the repository and compiled library are read-only.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
