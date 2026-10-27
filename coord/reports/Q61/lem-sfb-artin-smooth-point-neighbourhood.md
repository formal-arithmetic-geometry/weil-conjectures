## Worker report

The delivery states `AlgebraicGeometry.ArtinGeometry.exists_smooth_affine_neighbourhood`
in `Sheaf.AlgebraicGeometry.ArtinSmoothPointNeighbourhood`. Its sole theorem proof is
`sorry`; no mathematical assertion has been proved. The supporting definition module
`Sheaf.AlgebraicGeometry.ArtinGeometricAxioms` has real data and no `sorry`.

Source read: `literature/stacks-project/artin.tex`, Tag 07XY,
`lemma-get-smooth`, statement and complete proof; Tag 07XH,
`lemma-approximate-versal`; Tags 07WP (`definition-RS`), 07XF
(`definition-versal`), 07XQ (`definition-openness-versality`), and the axiom list
07XJ. The affine refinement is the principal-open refinement in the accepted DAG proof.
The new definitions record the existing source meanings, not stronger replacement axioms.

Hypothesis and conclusion audit (each item is part of the delivered signature):

- A commutative G-ring R: `(R : Type u) [CommRing R] (hR : IsGRing R)`.
  The recorded upstream `IsGRing` includes Noetherianity and regular maps from prime
  localizations to their maximal-ideal-adic completions. The base throughout is
  `Spec (.of R)`; no change of base to Z or to a field is imposed.
- Size convention: explicit universes `u v w`, schemes/rings in `u`, total-category
  homs in `v` and objects in `w`. Directed indices lie in `Type u`, with a nonempty
  directed preorder, so small affine-limit descent is not vacuous.
- Category fibred in groupoids: `F : BasedCategory.{v,w} (Over (Spec (.of R)))`
  and `hFibred : IsFibredInGroupoids F`. This is the existing total-category
  predicate: cartesian lifts exist and all arrows are strongly cartesian.
- Representable diagonal: `hDiagonal : HasAlgebraicSpaceDiagonal F`, the existing
  scheme-test 2-fibre-product formulation equivalent to the Isom-space formulation.
- (1): `hLimits : IsLimitPreserving F` is the conjunction of object descent,
  arrow descent with both chosen identifications retained, and eventual equality
  of stage arrows. These are essential surjectivity, fullness and faithfulness
  of the directed 2-colimit comparison. All diagrams and limiting cones are quantified.
- (2): `hRS : RimSchlessinger F` quantifies three Artinian local R-algebras of finite
  type, R-algebra maps `f` and `g`, with `g` surjective and nilpotent kernel,
  every spectrum pushout, and every pair of objects with their specified common
  restriction. It supplies a lifted pushout in the total category. The universal
  property gives unique gluing of all arrows, not just existence of objects.
- (3): `hInfinitesimal : FiniteInfinitesimalSpaces F` quantifies every field K,
  every R-algebra structure and `Algebra.FiniteType R K`, and every fibre object.
  `FiniteTangent` supplies coordinates bijective on marked isomorphism classes
  and respecting the sum/scalar operations from K⊕K, K⊕(K×K), and linear maps.
  `FiniteInfinitesimalAutomorphisms` supplies bijective finite coordinates on the
  actual identity-reducing automorphisms of each trivial deformation, respecting
  composition and the scalar pullback action. The split arrow `p` with
  `mark ≫ p = id` specifies triviality. No arbitrary vector-space structure or
  arbitrary finite-dimensional replacement space is used.
- (4): `hEffective : FormalObjectsEffective F` quantifies all complete Noetherian
  local R-algebras with finite-type residue field, using `IsAdicComplete`.
  `FormalSystem` has objects at A/m^(n+1), all transition arrows, and their unit
  and composition equations. The effective object's arrows agree with every
  transition. Index n=0 is the node's positive level 1, so no positive level is lost.
- (5): `hVersal : OpennessOfVersality F` quantifies every U locally of finite
  type over R, family x, and finite-type point at which x is versal. It gives an
  open neighborhood containing that point on whose finite-type points x is versal.
  `IsVersalAt` quantifies Artinian local R-algebras, surjective reduction with
  nilpotent kernel, surjective residue maps with maximal kernels, the canonical
  residue-field point equation, and the specified restriction identification.
  Its lift is an R-map and satisfies `b.val ≫ d.val = c.val`, preserving that
  exact identification. Residue maps are not coefficient-field embeddings.
- Given finite-type R-field and object: `(K : Type u) [Field K] [Algebra R K]`
  with `hK : Algebra.FiniteType R K`, and `x₀ : Object F (affine R K)`.
- Affine finite-type neighborhood: existential `U : Over (Spec (.of R))`,
  `IsAffine U.left`, `LocallyOfFiniteType U.hom`, and `QuasiCompact U.hom`.
- The object over U and induced morphism: `a : BasedFunctor (discreteModuli
  (yoneda.obj U)) F`; its object is `a.toFunctor.obj (CostructuredArrow.mk (𝟙 _))`.
  Fibred Yoneda identifies such functors with objects over U. Using this formulation
  retains the actual induced morphism without a choice of cleavage or an arbitrary map.
- Finite-type distinguished point: `u₀ : U.left` and both `LocallyOfFiniteType`
  and `QuasiCompact` of `U.left.fromSpecResidueField u₀`.
- Specified R-isomorphism κ(u₀) ≅ K: the ring equivalence `e`, and the R-map
  `α : affine R K ⟶ U` whose underlying map equals `Spec.map e ≫ fromSpecResidueField`.
  Being a map over Spec R forces e to respect the two R-actions, so this is exactly
  an R-isomorphism without adding a separate arbitrary R-algebra structure on κ(u₀).
- Fibre isomorphism: the existential arrow `b : x₀.val ⟶ a(identity)` with
  `F.p.IsHomLift α b`. Every arrow is cartesian by hFibred, so this is precisely
  the specified isomorphism x|u ≅ x₀ under e.
- Representability: `IsRepresentableByAlgebraicSpaces a`.
- Smoothness: for every T and map `t : h_T → F`, an actual algebraic-space
  presentation `Z,p` of its base change with `HasSpaceBaseChange a T t Z p`
  and `CategoryTheory.SpaceMapIsSmooth Z T p`. This last existing predicate
  tests Smooth on every representable étale scheme chart of Z.

Dependency declarations read and used: `IsGRing` from
`WeilConjectures.RingTheory.GRing`; `AlgebraicGeometry.Spec`, `Spec.map`, and
`Scheme` from `Mathlib.AlgebraicGeometry.Scheme`; `Field` from
`Mathlib.Algebra.Field.Defs`; `IsNoetherianRing` from
`Mathlib.RingTheory.Noetherian.Defs`; `AdicCompletion` and `IsAdicComplete` from
`Mathlib.RingTheory.AdicCompletion.Basic`; `Scheme.residueField` and
`fromSpecResidueField` from `Mathlib.AlgebraicGeometry.ResidueField`;
`Smooth` from `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
`LocallyOfFiniteType` and `QuasiCompact` from the corresponding Mathlib morphism
modules. The metatheoretic size-convention node has no declaration.
`AlgebraicSpace` and its scheme-chart predicates are imported through
`Sheaf.AlgebraicGeometry.AlgebraicSpace`. Existing fibred-groupoid and space
base-change declarations are from
`Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`; existing
`CategoryTheory.SpaceMapIsSmooth` is from
`Sheaf.AlgebraicGeometry.AlgebraicModuliStack`. These landed definition nodes
are dependencies of the new definition node as appropriate.
Proof-only imports include Mathlib affine opens, open immersions, pullbacks and
prime localizations; the four Artin helper theorems in the proof have no Lean
records yet, so no missing source module is guessed or imported for them.

Edge cases checked: R=0 admits no field R-algebra, so the assertion about each K
is vacuous; empty F similarly has no x₀. The resulting U cannot be empty because
u₀ is part of the conclusion. Tangent dimension zero is allowed (`n=0`, `Fin 0`).
No characteristic or separability restriction is present. The residue field need
not embed in the Artinian test rings, allowing mixed-characteristic tests.
For a field A the formal system has all the same positive quotients; n=0 is
A/m, not A/m^0. Identity surjections and zero nilpotent ideals are included.
Directed systems include singletons; index universes agree with scheme universes.
Arrows and automorphisms are retained, not only isomorphism classes of objects.
The conclusion asserts smoothness of one neighborhood, not that it is surjective.

Actual searches performed with msearch.py: LeanFinder on
“Artin representability smooth neighbourhood field valued object fibred groupoid
Rim Schlessinger effective versal deformation” returned eight scheme/ring smoothness
hits, no matching theorem; Loogle on `CategoryTheory.Fibered,
CategoryTheory.IsFibered, AlgebraicGeometry.AlgebraicStack` returned zero hits
(unknown CategoryTheory.Fibered); Mathlib grep on `IsFibered|IsFibred|Schlessinger|
Versal|FiberedInGroupoids` found Mathlib Functor.IsFibered and cartesian primitives,
not the Artin predicates; LeanSearch on the full list of geometric Artin conditions
returned eight generic Artinian-category/scheme hits. A second Mathlib grep for
`IsLimitPreserving|RimSchlessinger|FiniteInfinitesimalSpaces|FormalObjectsEffective|
OpennessOfVersality` returned zero hits. Actual rg of lean/WeilConjectures and
lean/Sheaf found only the integer-base predicates in the downstream
ArtinRepresentableDiagonalCriterion and the fixed-residue cofibred groupoid
IsRimSchlessinger of ArtinDeformationTestCategory. The item-id search in
lean/WeilConjectures returned no hits. DAG definition and blueprint searches found
no node for these five geometric predicates at arbitrary R. The new node records
these actual results. Its interface cannot import the downstream criterion without
closing the intended proof-import cycle.

No statement correction, disputed statement, dependency-record repair, or unit
statement change is needed. The original item's only deltas are `lean` and the
added definition-node dependency. Both files compiled cleanly through scompile.py:
ArtinGeometricAxioms (8.6 s sandbox, 17.0 s library) and
ArtinSmoothPointNeighbourhood (9.6 s sandbox, 11.3 s library).

## New nodes

`def-sfb-artin-geometric-axioms` defines precisely the five geometric predicates
in the item's hypotheses, over the actual affine base Spec R, with their supporting
marked deformations, formal systems, and versality. Its source is Artin's Axioms
07WP, 07XF, 07XQ, 07XJ, 07XY and the tangent operations in Formal Deformation Theory
06I1. All definitions use the existing scheme, ring, fibre, strongly cartesian,
quotient, square-zero extension, and directed-limit objects. This is not the
fixed-residue ArtinDeformationTestCategory notion and not the downstream Spec Z
specialization. The searches above found no usable general-base definition node.
Every declaration is listed in lean.declarations; no postponed theorem is introduced.

## Second reading by Q61

The dispatcher forbids spawning another agent, so this section is an additional
self-audit, not a claim of independent review. The maintainer's independent review
is still required. Re-read the item and both delivered files after compilation.
Checked all five predicates and all conclusion clauses using the mapping above.
The first compile exposed missing R-actions/scalar towers on square-zero extensions;
repaired those canonical maps with Algebra.restrictScalars and the existing
TrivSqZeroExt.map_inl law, without new hypotheses. The final files have explicit
universes and autoImplicit false, no file-local instances or notation, real
definitions, only the item's named theorem sorry, and no extra stack-descent,
size-bound, separability, or surjectivity assumptions. The residue-field isomorphism
is pinned to the actual R-point map α; the fibre isomorphism is pinned to that map.
