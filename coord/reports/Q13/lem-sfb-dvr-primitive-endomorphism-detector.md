## Worker report

The delivery states `AlgebraicGeometry.dvr_primitive_endomorphism_detector` in
`Sheaf.AlgebraicGeometry.GroupScheme.DvrPrimitiveEndomorphismDetector`. Its only postponed
proof is that named theorem. The two supporting definition modules have real data and no
sorry. The item's natural-language statement, source, proof and proof dependencies are
unchanged. Its statement dependencies gain the two new definition nodes listed below.

Hypothesis and clause correspondence:

- The DVR A is `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
  Mathlib's DVR definition includes the nonzero maximal ideal condition, so fields are not
  silently included. The maximal ideal is `IsLocalRing.maximalIdeal A` and the residue field
  is the actual `IsLocalRing.ResidueField A`, with `[IsAlgClosed ...]`.
- H and all group-object diagrams are `H : Grp (Over (Spec (.of A)))`. Smoothness,
  affineness and local finite presentation are the three named morphism instances on
  `H.X.hom`. Since an affine morphism is quasi-compact and separated, the latter is
  equivalent here to finite presentation. No properness or completeness hypothesis is added.
- `hH : RingSemisimple.IsSplitSemisimpleSimplyConnected H` expands to the exact geometric
  fibre semisimplicity, central-isogeny simple connectedness and split torus/Borel
  existence in the node. Field semisimplicity uses the existing derived-series solvability
  and triviality of smooth connected solvable normal closed subgroups. The central-kernel
  condition quantifies over all commutative algebra points, including nonreduced rings.
  `geometricChange` uses the actual finite-product-preserving pullback functor on group
  objects; it does not choose an unrelated group with the same points. The pair has closed
  subgroup inclusions, compatible T→B→H, an isomorphism to the existing ring split torus,
  and the existing maximal-torus/Borel predicates on every geometric fibre.
- V is an arbitrary `(V : Type v)` with additive and A-module structures,
  `[Module.Free A V] [Module.Finite A V]`. Its rational structure is the counital,
  coassociative `ρ : RingRational.Coaction A Γ(H.X.left, ⊤) V`, using the canonical
  coordinate Hopf algebra derived from H's given group law, never an extra Hopf structure.
- `hv : ρ.map v = v ⊗ₜ[A] 1` is precisely fixedness. `hprimitive` says
  `v ∉ (maximalIdeal A) • (⊤ : Submodule A V)`, i.e. v is outside mV.
- The existential `(n : ℕ) (_ : 0 < n)` and coaction σ on `Fin n → A` present W in a
  finite basis. Every positive-rank finite free module is linearly isomorphic to one of
  these, and transporting its coaction and maps is harmless; no mathematical case is
  excluded by this presentation. The type already supplies a finite free module.
- φ is the required A-linear map `V →ₗ[A] Module.End A (Fin n → A)`.
  Equivariance is expressed without choosing an endomorphism coaction: for every x,w,
  `evaluateTensor (φ.rTensor C (ρ.map x)) (σ.map w) = σ.map (φ x w)`, C=A[H].
  Expanding gives Σ φ(x_i)(w_j) tensor c_i d_j = σ(φ(x)w), exactly equivariance of
  evaluation V tensor W→W. For any group this is equivalent to φ(hx)=hφ(x)h⁻¹.
  Indeed φ(hx)(hw)=h(φ(x)w), and the Hopf antipode supplies h⁻¹. Thus this is exactly
  conjugation-equivariance, not merely equivariance at A-points.
- `invariantEnd σ` is the kernel of T↦σ∘T−(T tensor 1)∘σ, so it is precisely End(W)^H.
  The existential linear equivalence e is fixed by `∀ a, (e a).val = a • LinearMap.id`:
  the canonical scalar map itself is an isomorphism, not an arbitrary abstract rank-one
  equivalence. This clause includes both injectivity and surjectivity.
- `(φ v).baseChange (IsLocalRing.ResidueField A) ≠ 0` is nonvanishing in the actual
  End_κ(κ tensor_A W). Mathlib places the scalar factor first; the canonical tensor flip
  identifies this with End_κ(W tensor_A κ) in the node. It is not merely φ(v)≠0 over A.
- Tensor, dual and symmetric powers in the node's introductory terminology specify the
  conventions used in the proof; none is a further quantified hypothesis or conclusion.
  The proof docstring retains the diagonal/contragredient conventions, the finite-basis
  tensor-Hom isomorphism, and the same characteristic-dependent weight choice throughout.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `CategoryTheory.Grp`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`, and
  `isAffine_of_isAffineHom` to expose the canonical coordinate Hopf algebra.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the tensor associator,
  right unitor, map/rTensor/lTensor and baseChange operations are the existing Mathlib ones.
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`, `ι`, `lift` and
  `algHom_ext`; the recorded graded declaration `SymmetricAlgebra.graded_by_tensor_images`
  in `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded` is imported for the inherited
  tensor/symmetric-algebra framework. These notions are not redefined.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- The new ring-group predicate reuses `IsSemisimpleGroupScheme` in
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`, `IsBorelGroupScheme` in
  `Sheaf.AlgebraicGeometry.GroupScheme.Borel`, `ReductiveTorusCentralizer.IsMaximalTorus`
  in `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`, and
  `RingGroupSchemes.splitTorus` in `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`.
- The coordinate structure calls the recorded `HopfAction.affineCoordinateHopfAlgebra`
  in `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`. Its body is the canonical
  Mathlib affine-group instance; no theorem asserting existence of a Hopf structure is used.

The four rho proof-dependency nodes have no recorded Lean declarations, so no unavailable
proof-only module is imported. Their proof plan is included in the theorem docstring.
They are not needed to elaborate this statement, so no dependency modules are introduced.

Source checked: primary PDF, Alper, Section 9.7, printed pp.526–528,
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf, especially the endomorphism
construction in Theorem 9.7.5. Its literal Lemma 9.7.2(2) omits primitivity; the assigned
node already explicitly supplies primitivity and chooses unbounded Steinberg weights, so
neither historical source omission is reproduced in the formal statement.

Edge cases checked before writing: V=0 and v=0 cannot meet primitivity; n=0 is explicitly
excluded only for the witness W as required. The trivial group is allowed (torus rank zero)
and reduces to an A-linear functional nonzero on the residual primitive vector, with W=A.
Residue characteristic 2 is allowed; the half-sum and Steinberg weights use integral
characters, not division by 2 in A. Both equal and mixed characteristic and noncomplete
DVRs remain included. Geometric test fields and their algebras live in the base universe u,
which contains algebraic closures of residue fields and of the fraction field, so no
small-test-universe vacuity occurs. V has its independent universe v, and finite-basis
presentation of W imposes no smallness restriction on the existential witness.

Searches made (the precise msearch return records also occur in each new node):

- LeanFinder, full plain-language primitive detector query: eight results concerning
  sl2 primitive vectors, abstract group norm maps, FDRep simplicity and Hom invariants;
  none is this integral group-scheme detector.
- Loogle `Comodule, HopfAlgebra, LinearMap.baseChange`: zero results; unknown `Comodule`.
- msearch grep `primitive.*endomorphism|endomorphism.*detector|SimplyConnected|SplitSemisimple`
  in Mathlib/AlgebraicGeometry: zero hits. msearch grep
  `Coaction|Comodule|SimplyConnected|Borel` in the same directory: zero hits.
- LeanSearch, rational representation over a commutative ring/coaction query: eight
  coalgebra or abstract representation results, no rational ring module notion.
- LeanFinder, commutative-ring counital coassociative Hopf module query: HopfAlgebra and
  HopfAlgCat results only, no comodule.
- LeanFinder and LeanSearch, split semisimple simply connected ring group/Borel/geometric
  fibre queries: Lie algebra/module semisimplicity and unrelated fibre facts only.
- `rg` over both project roots found the field-only existing coaction, semisimple, Borel,
  rational-module and rho-module APIs described above. The item-id search in
  lean/WeilConjectures found no declaration for this node.
- DAG definition searches and `tools/blueprint_refs.py search` found no ring-level versions
  of these two notions. The existing ring split torus and coordinate Hopf structures were
  found and reused; there is no private copy. `ancestor` returns `blueprint.from.node=None`,
  which is preserved in the new definition nodes rather than inventing a blueprint unit.

Validation: all three delivered files compiled separately through the prescribed
`scompile.py Q13 lem-sfb-dvr-primitive-endomorphism-detector <three paths>` in dependency
order; no errors or unexpected warnings. No local/global build was run, no shared source
was edited, and no direct git operation was used.

## New nodes

`def-sfb-ring-rational-module` owns RingRational.Coaction, its invariantEnd submodule and
coefficient evaluation, together with the adapter to the already canonical coordinate
Hopf structure. It is the ring-level rational-module notion used by Alper Section 9.7.
Existing HopfAction.ModuleCoaction and EquivariantCoherent.RationalModule require a field,
so neither can describe a DVR. All data are linear-map/kernel/tensor constructions, with
no choice from existence and no postponed theorem. Searches above establish absence of
a usable ring-level version; the canonical coordinate Hopf algebra itself is reused.

`def-sfb-ring-split-semisimple` owns geometricChange, the central-isogeny predicate
IsSimplyConnected, and IsSplitSemisimpleSimplyConnected over a commutative ring. The
existing field-only semisimple/Borel/maximal-torus predicates and ring split torus are used
on the actual geometric pullbacks. This packages exactly the terminology of the assigned
node and Alper Lemmas 9.7.2/9.7.4, without asserting existence or adding smoothness,
completeness, characteristic or positive-rank assumptions. Existing field-only predicates
cannot be applied to the base DVR; the searches above found no relative version.

## Second reading by Q13

A separate self-review reopened the three files and all node records. It checked the DVR,
residue field, group diagrams, morphism hypotheses, geometric semisimplicity, isogeny
centrality including infinitesimal kernels, fibrewise pair, free V, fixedness, primitivity,
positive-rank W, evaluation-equivariance, pinned scalar isomorphism, and residual rather
than integral nonvanishing against the node clause by clause. It checked that kernel
invariantEnd uses σ∘T−(T tensor 1)∘σ and that evaluateTensor multiplies Hopf coefficients.
The earlier submodule-closure proof was replaced by the actual kernel construction; no
helper theorem or proof was introduced. The canonical Hopf adapter explicitly derives
IsAffine from the affine structure morphism. All definitions contain real data, signatures
bind their variables and universes, and the only sorry is the item theorem. No statement
correction, disputed statement, or dependency replacement was needed. This is a self-review;
the dispatcher forbids starting other agents, and the maintainer supplies the independent
review after delivery.
