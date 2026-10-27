## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.invertible_fp_tensor_models` in
`Sheaf.AlgebraicGeometry.InvertibleFpTensorModels`. Its only proof is `by sorry`.
The original node is unchanged except for its `lean` record. No new notion, dependency
module, or statement correction is required.

Source read: Stacks `limits.tex`, `lemma-descend-invertible-modules` (Tag 0B8W),
including the proof of (2); `modules.tex`, `lemma-constructions-invertible` (01CT(2))
and `lemma-tensor-product-permanence` (01CE(4)). The node isolates the finite-presentation
models and the evaluation BEFORE the subsequent descent of evaluation and its inverse.
The source also obtains finite locally free models by a preceding argument, but this
node deliberately needs and asserts only finite presentation of its two models.

Hypotheses and clauses, in order:

- A small nonempty directed index set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The index and scheme universes are the same as required
  by the affine-limit size convention; no independent smaller test universe occurs.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. The arrow `D.map (homOfLE hij).op`
  goes from the stage j to the stage i. Functoriality encodes the transition identities.
- Each stage is quasi-compact by `[∀ i, CompactSpace (D.obj i)]`, and quasi-separated
  by `[∀ i, QuasiSeparatedSpace (D.obj i)]`. The latter is the scheme specialization
  of the recorded `QuasiSeparated` definition, as its mathlib_match specifies.
- Affine transitions are `[∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- The limit Z, projections, compatibility and universal property are exactly
  `c : Cone D` and `hc : IsLimit c`; Z is `c.pt` and q_i is `c.π.app (op i)`.
  IsLimit gives unique factorization from every compatible cone, not an arbitrary
  choice of projections without the universal property.
- `L : c.pt.Modules` is an actual Zariski sheaf of modules. `[L.IsInvertible]`
  is the recorded locally rank-one trivial notion. No affine, reduced, nonempty,
  Noetherian, flatness or finite-type assumption on any scheme is added.
- The notation N in the node is rendered literally as `dual L`, whose source
  definition is `homObj L (SheafOfModules.unit _)`. Thus N is the internal sheaf Hom,
  not an arbitrary tensor inverse supplied as extra data.
- N invertible is `(dual L).IsInvertible`; finite presentation of L and N is
  `L.IsFinitePresentation ∧ (dual L).IsFinitePresentation`. Mathlib's
  `SheafOfModules.IsFinitePresentation` means locally a finite-free cokernel, exactly
  the specified finite-generator, finite-relation presentation; it also supplies
  quasi-coherence as a consequence, not an extra hypothesis.
- Evaluation e is the existing `dualEvaluation L : L ⊗ dual L ⟶ 𝟙_ c.pt.Modules`.
  The clause `IsIso (dualEvaluation L)` asserts invertibility of this actual
  sectionwise evaluation, not merely existence of some isomorphism.
- `∃ (i : I) (A B : (D.obj (op i)).Modules)` gives the two models on ONE stage;
  `A.IsFinitePresentation ∧ B.IsFinitePresentation` gives both required properties.
- The existential binders `a : (tensorPullback (c.π.app (op i))).obj A ≅ L` and
  `b : (tensorPullback (c.π.app (op i))).obj B ≅ dual L` give the specified two
  isomorphisms. All pullbacks are the recorded tensor pullback, never an unrelated
  inverse-image functor. The proof plan uses its normalized composition comparisons
  when moving the two models to the common stage.
- P_i is inline `A ⊗ B`, the existing sheaf tensor. Its finite presentation is
  `(A ⊗ B).IsFinitePresentation`. Finite presentation of O_{Z_i} is
  `(𝟙_ (D.obj (op i)).Modules).IsFinitePresentation`.
- Epsilon is written out as the final `IsIso` argument. Its first arrow is
  `(Classical.choose (module_pullback_tensor (c.π.app (op i))) A B).hom`, its second
  is `(a.hom ⊗ₘ b.hom)`, and its last is `dualEvaluation L`. The theorem
  `module_pullback_tensor` specifies both naturality and the pure tensor section
  normalization, so this chooses the canonical comparison, not an arbitrary
  isomorphism. The adjunction used there is likewise normalized by its `1 ⊗ m`
  section equation in `exists_tensorPullbackAdjunction`. These section equations
  determine the maps by the sheaf tensor universal property. The final codomain
  is O_Z and the domain is the tensor pullback of P_i, exactly as displayed in
  the node. No invertibility or local freeness of A or B appears.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and its
  `tensorPullbackSectionComp`; the actual functor `tensorPullback`, its ring map,
  object formula, and map construction are publicly imported from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, exposing the same sheafified localization
  tensor. For schemes the existing instance in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible` specializes this tensor.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, publicly available from Dual.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff requirement).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`, and the recorded scheme specialization
  `QuasiSeparatedSpace`; `Mathlib.AlgebraicGeometry.Morphisms.Affine`:
  `AlgebraicGeometry.IsAffineHom`. These are exposed by AffineTransitionLimit.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for Mathlib's `SheafOfModules`. The statement uses
  its existing scheme specialization `Scheme.Modules`, without a second category.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`: `dual`, `dualEvaluation`,
  `IsInvertible.dual`, `isIso_dualEvaluation`, and the recorded proof-dependency
  declaration `nonempty_iso_dual_dual`, all in `AlgebraicGeometry.Scheme.Modules`.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.module_pullback_tensor`.
- Proof imports: `WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation`
  (`isFinitePresentation_tensorPullback`) and
  `Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent`
  (`finitePresentation_descent_affineLimit`). The proof-only node
  `lem-trf-fp-sheaf-tensor-product` has no recorded Lean declaration at reading time;
  its module cannot yet be imported. It is not needed to type this statement, and
  the proof docstring retains its role. Other recorded proof dependencies are
  already among the public imports because their constructions occur in the type.

Edge cases checked before drafting: I empty is explicitly excluded by the node;
I a singleton and constant systems are included. A non-antisymmetric preorder
is permitted. Empty limit and stage schemes are allowed: invertibility on the
empty scheme is locally vacuous and causes no nonzero-module hypothesis. The
structure module is allowed to be zero on the empty scheme. Finite presentations
allow zero generators and zero relations. Schemes in arbitrary characteristic,
nonreduced schemes, disconnected schemes and nonflat transitions are included;
only affineness of transitions is required. The limit is not assumed affine.
Models may fail to be invertible at the chosen stage; no clause assumes otherwise.
The module universe matches the existing Scheme.Modules interface and the index
universe matches the established affine-limit statement. No counterexample or
node fault was found.

Searches made via `/home/ubuntu/weil-launcher-all/batch2/msearch.py` (Q42 and this item):

- LeanFinder: "An invertible sheaf and its dual on an affine transition inverse limit
  of qcqs schemes admit finitely presented models at one stage with tensor product
  and pulled back evaluation isomorphism". Eight hits: affine-limit sections and
  Mathlib finite-presentation definitions; no theorem of these simultaneous models.
- Loogle: "AlgebraicGeometry.Scheme.Modules.IsInvertible,
  SheafOfModules.IsFinitePresentation". Zero hits, unknown project identifier
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; not treated as an absence proof.
- Grep: `invertible.*(limit|models)|finitePresentation.*tensor` in Mathlib's
  AlgebraicGeometry directory. Zero hits.
- LeanSearch: "Simultaneous finitely presented models of an invertible sheaf and its
  dual over an inverse limit of qcqs schemes with affine transition maps". Eight
  hits, all definitions and constructors for local finite presentations; no match.
- Direct rg searches in `lean/WeilConjectures` and `lean/Sheaf` for invertibility,
  tensor pullback, finite presentation, evaluation, and simultaneous/model keywords
  found the existing notions and the general descent lemma cited above. The later
  `invertible_affine_limit_descent` theorem only concludes an invertible model for
  L; it omits this node's dual, finite-presentation and specified composite clauses.
  No exact existing declaration was found.
- Exact id/name search in both source roots and `dag/lean_names_upstream.json` for
  `lem-trf-invertible-fp-tensor-models|invertible_fp_tensor_models|invertible.*tensor.*models`
  found no existing binding or declaration before creating the module.

Validation: scompile.py compiled both its sandbox probe and the library module on
2026-10-24, in 10.5 s and 3.5 s respectively, with no diagnostics. All variables and
universe u are explicitly bound, with autoImplicit and relaxedAutoImplicit disabled.

## Second reading by Q42

Author's second pass, as a dispatcher worker forbidden to start other agents;
independent review belongs to the maintainer. I reopened the node statement and
read the complete final signature against it. The four opening conjuncts give
N's invertibility, the two finite presentations, and invertibility of the actual
evaluation. Both models share the existential i; the isomorphism orientations
are q_i^*A to L and q_i^*B to its actual dual. The tensor and structure finite
presentations are both inside those same witnesses. Expanding the last IsIso
argument gives exactly comparison, then a tensor b, then evaluation, in that
order; no arbitrary evaluation or tensor comparison is introduced. The index
binder includes nonemptiness and directedness; the diagram includes qcqs stages
and affine transitions; the cone and IsLimit retain the universal property.
No unbound variable, extra flatness assumption, model invertibility, affine-limit
assumption, or omitted empty-scheme case was found. No signature change was
needed after the first clean compile. There is one named sorry and no definition
with postponed data. The source and proof are included in its docstring.
