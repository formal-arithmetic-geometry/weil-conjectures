## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveSymmetricPowerDvrReduction`,
with the sole postponed theorem
`AlgebraicGeometry.reductive_symmetricPower_dvr_reduction`.
Its proof is exactly `sorry`; the docstring contains all six proof steps and their dependencies.
Two definition modules supply the previously missing arbitrary-ring lifting property and relative
geometric-fibre conditions. Every definition has actual data; neither helper module has a sorry.
The original item's natural-language statement, proof and proof dependencies are unchanged.

Source read: Alper's published original,
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
Lemma 9.2.5(5), printed p.522, and the reductions of Theorem 9.7.5, printed p.527.
The conditional reduction stops before the determinant argument. The source uses the unrestricted
module formulation in Lemma 9.2.5(5); finite free modules appear only in the later DVR proof.

Clause-by-clause correspondence:

- A commutative base ring is `R : CommRingCat.{u}` (and `A` in the DVR premise).
- A scheme over its spectrum is `[G.Over (Spec R)]`; its structure morphism is
  `G ↘ Spec R`. A group object is `[GrpObj (G.asOver (Spec R))]`.
  This is precisely the diagrams interface recorded by `def-sc-group-scheme`, used over a ring.
- Affine and finitely presented are `[IsAffine G]` and
  `[LocallyOfFinitePresentation (G ↘ Spec R)]`. Over affine Spec R the first is equivalent to
  `IsAffineHom`; it also supplies quasi-compactness and separatedness, hence quasi-separatedness,
  so locally finite presentation gives finite presentation. Smoothness is the recorded
  `[Smooth (G ↘ Spec R)]`. The premise additionally displays flatness as required for P(A,H).
  In the conclusion smoothness already implies flatness.
- The coordinate algebra is exactly `Γ(G, ⊤)` with Mathlib's canonical `HopfAlgebra` instance
  from `Mathlib.AlgebraicGeometry.Group.Affine`, dual to the specified group operations.
  No arbitrary Hopf structure or extra representation is assumed.
- A rational module is any `N : Type (max u v)` with `[AddCommGroup N] [Module R N]` and
  `ρ : N →ₗ[R] N ⊗[R] C` satisfying `InvariantSymmetricPower.IsCoaction`.
  Its first equality is the counit law via `TensorProduct.rid`; the second is coassociativity
  via `TensorProduct.assoc`. No finite, free, torsion-free or flat hypothesis is present.
- Equivariant surjectivity onto the trivial module is `Function.Surjective lam` together with
  `∀ m, lam.rTensor C (ρ m) = lam m ⊗ₜ[R] 1`. This is commutation with the trivial coaction.
- The symmetric algebra is the recorded `SymmetricAlgebra R N`. Its induced coaction
  `symmetricCoaction` is constructed by `SymmetricAlgebra.lift` on
  `(SymmetricAlgebra.ι R N).rTensor C ∘ₗ ρ`, so it has exactly the diagonal generator formula.
  Sym^n is the image of the n-th tensor grade under `SymmetricAlgebra.algHom`, literally
  the component in `SymmetricAlgebra.graded_by_tensor_images`.
- The witness is `∃ n, ∃ (_ : 0 < n), ∃ q, ...`; its three clauses state membership in that
  component, fixedness `symmetricCoaction ... q = q ⊗ₜ 1`, and `SymmetricAlgebra.lift lam q = 1`.
  The last map is Sym^n(lam) followed by the canonical Sym^n(R) = R identification: each
  generator m is evaluated to lam(m). The tensor/dual-module sentences are explanatory
  conventions; no tensor or dual object is quantified in this conditional theorem.
- The DVR hypothesis is universal over A with `[IsDomain A] [IsDiscreteValuationRing A]` and
  `[IsAlgClosed (IsLocalRing.ResidueField A)]`. Mathlib's DVR excludes fields, as the node does.
- Semisimplicity and simple connectedness in the premise are
  `RelativeReductive.HasSimplyConnectedSemisimpleFibres`: every algebraically closed field
  point is pulled back with `(Over.pullback s).mapGrp`, and the recorded
  `IsSemisimpleGroupScheme` supplies smoothness, connectedness and absence of nontrivial
  smooth connected solvable normal subgroups. Every central isogeny onto that actual fibre
  from a semisimple group is required to be `IsIso`. Its kernel is `GrpObj.ker f`, with
  `IsFinite` and commutation on every test scheme; nonreduced central kernels remain included.
- Splitness is `RelativeReductive.HasSplitBorelPair`. It gives the recorded
  `relativeSplitTorus S r`, a group B and inclusions iT, iB with j ≫ iB = iT, closed embeddings
  into G, smooth B, and fibrewise `IsMaximalTorus` and `IsBorelGroupScheme`. These predicates
  reuse the existing torus and scheme-theoretic derived-series definitions.
- The conclusion is the same `HasInvariantPowerLifting.{u,v,u}` as in the premise, for any
  R and smooth affine finitely presented group G with `HasReductiveFibres`. That predicate
  applies the recorded `ReductiveTorusCentralizer.IsReductive` to every geometric fibre,
  retaining connectedness and the exclusion of smooth connected normal unipotent subgroups.
  Its `SolvableGroupStructure.IsUnipotent` is a faithful matrix representation with
  `(u-I)^N=0`, N positive, on geometric points.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `IsMonHom`;
  `GrpObj.ker` is the scheme-theoretic kernel in the group-object interface.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom` and
  `isAffine_of_isAffineHom`, the affine-base equivalence;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs/Map`: `TensorProduct`, `LinearMap.rTensor`;
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`: `SymmetricAlgebra`, `ι`, `lift`, `algHom_ext`.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, the exact tensor-image grading.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` through the field predicates.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`;
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSemisimpleGroupScheme`,
  `IsSolvableGroupScheme`, `GroupSchemeDerivedLength`;
  `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`;
  `Sheaf.AlgebraicGeometry.RelativeSplitTorus`: `relativeSplitTorus`.
  These landed nodes are cited by the new relative-condition node.

Available proof dependencies are imported privately: integer prime localizations, strict
henselization triples, strict henselization DVR, faithful flatness, and etale local ring triples.
The grading dependency is already public through the lifting module. The algebraic-closure
existence/uniqueness mathlib leaf is already supplied by the relative-condition imports.
The five new reductive-reduction proof nodes have no recorded Lean declarations, so they cannot
be imported yet; their IDs and the complete proof instructions are retained in the docstring.

Edge cases checked before writing: R = 0 is allowed (all its modules vanish; n=1,q=0 maps to
1=0); degree zero cannot witness the property because 0<n; arbitrary torsion and infinite modules
are allowed; the trivial group and split torus rank r=0 are allowed. All characteristics and
nonreduced finite central kernels are included. Connected fibres use `ConnectedSpace`, so an
empty geometric fibre cannot pass. There are no geometric points over the zero ring, correctly
making its fibre condition vacuous. Universe v is arbitrary, and `max u v` prevents the module
quantifier being artificially smaller than the base ring; any module can be lifted to it.
Geometric points use F : Type u, the scheme universe, as in the existing group interfaces.

Searches performed with msearch.py: LeanFinder on the full DVR reduction; Loogle on
`Comodule, SymmetricAlgebra, GrpObj`; grep on
`IsReductive|IsSemisimpleGroup|SimplyConnected|symmetricPower`; LeanSearch on Hopf coactions;
LeanSearch on unrestricted rational-module invariant lifting; LeanFinder on relative reductive
fibres/Borel pairs; LeanSearch on the same relative conditions; Loogle on `TensorProduct,
LinearMap`; grep on `comodule|coaction|SymmetricAlgebra` in RingTheory. Returned results contain
existing tensor, symmetric algebra, Hopf coalgebra and unrelated simply connected topology
notions, but neither this conditional theorem nor the two new relative/ring-level notions.
Exact outputs are recorded in the new nodes. Repository rg/grep searches covered
lean/WeilConjectures (including this blueprint ID), lean/Sheaf, dag/nodes and
 dag/lean_names_upstream.json. blueprint_refs.py ancestor returned None; its searches for
`symmetric power` and `split torus` returned no relevant existing definition node.
The field-only `HopfAction` and `RelativeHopf.Coaction` definitions cannot express arbitrary-ring
rational modules; `EquivariantCoherent.RationalModule` is also field-only and finite-dimensional.
The canonical coordinate Hopf interface is already Mathlib and is reused directly.

Validation: scompile.py compiled all three delivered files separately in dependency order,
against the live publication. No errors or warnings remain. No statement correction or
STATEMENT-DISPUTED issue was needed.

## New nodes

`def-sfb-invariant-symmetric-power-lifting` owns IsCoaction, symmetricCoaction and
HasInvariantPowerLifting. It states the unrestricted rational-module coaction equations and
Alper Lemma 9.2.5(5), using Mathlib's symmetric-algebra lift and the recorded tensor-image grade.
The searches above found only field-specific coactions, not this ring-level notion. The module
contains no chosen data, theorem, or sorry; the induced symmetric coaction is an explicit lift.

`def-sfb-relative-reductive-conditions` owns HasReductiveFibres,
HasSimplyConnectedSemisimpleFibres and HasSplitBorelPair. These are the explicit geometric-fibre
and splitness conventions used in Alper Theorem 9.7.5, p.527. The existing field-level reductive,
semisimple, Borel and maximal-torus predicates and the existing relative split torus are reused.
The searches above found no arbitrary-base wrapper. The closed subgroup structure over an
arbitrary S is expressed as a bundled group homomorphism whose underlying map is a closed
immersion; the recorded `IsClosedSubgroupScheme` is specialized to a field base and is therefore
used only on geometric fibres through the existing predicates. No duplicate subgroup definition
is introduced.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
