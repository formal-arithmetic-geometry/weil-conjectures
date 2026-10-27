## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveInvariantBoundaryIdeals` states
`AlgebraicGeometry.ProjectiveInvariantBoundary.projective_invariant_boundary_ideals`.
Its only postponed proof is this theorem, with `sorry`; the seven subordinate
helpers have real data and no postponed proofs. No node statement was corrected.
Only `lean` and two new definition-ownership additions to `stmt_deps` change on the item.
The delivery also adds those two existing:true definition nodes. The theorem nodes
remain in proof_deps and are not statement dependencies.

The statement is in coordinates, as the node explicitly permits by choosing a
basis. Set dim(V)=n+1 and identify V with k^(n+1). Every nonzero finite-dimensional
vector space has such a basis, including dimension one (n=0). The representation
is the existing `GeneralLinearGroup.RationalHom` on `ULift (Fin (n+1))`; lifting
the matrix indices only meets its universe convention. Polynomial coordinates
remain `Fin (n+1)` to use the recorded chart-fraction declaration unchanged.
There is no condition on characteristic or connectedness, and no extra universe
equality on the scheme or coefficient algebra. As in the representation dictionary,
individual schemes, coefficient algebras and vector spaces share universe u;
this includes the coordinate algebra and hence detects scheme morphisms.

Hypothesis-by-hypothesis rendering:

- Algebraically closed field k: `{k : Type u} [Field k]` and `[IsAlgClosed k]`.
- k-group scheme G: `(G : Scheme.{u}) [G.Over (Spec (.of k))]` and
  `[GrpObj (G.asOver (Spec (.of k)))]`.
- Affine, smooth, finite type: `[IsAffine G]`,
  `[Smooth (G ↘ Spec (.of k))]`, `[LocallyOfFiniteType (G ↘ Spec (.of k))]`,
  and `[QuasiCompact (G ↘ Spec (.of k))]`.
- Nonzero finite-dimensional represented space: the coordinate model with
  n+1 basis vectors, `(n : ℕ)`, and `ρ : GeneralLinearGroup.RationalHom ...
  (ULift (Fin (n+1)))` with `[IsMonHom ρ]`. This includes all positive dimensions.
- P(V)=Proj of the total-degree polynomial ring: `(space k n).left` unfolds to
  `Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) k)`. Its structural map is
  exactly `Proj.toSpecZero` followed by `Spec.map homogeneousSubmoduleZeroEquiv`.
  This packages existing Proj data; it does not introduce a second Proj construction.
- Induced action on lines: `a : ModObj ... (space k n)` and `ha : IsInduced G n ρ a`.
  The predicate prescribes the entire graded ring map on constants and variables
  over k[G], using the universal matrix `ρ.points Γ(G, ⊤) (genericPoint G)`.
  It sends z_i to sum_j ρ_ij z_j, without inversion, for the projective scheme action.
  The comparison e is an isomorphism with G times projective space; both projection
  composites are prescribed, using G.isoSpec.inv and the coefficient-change Proj map.
  Thus e cannot absorb a different action. This tests scheme morphisms, including
  their behavior on nonreduced algebras, rather than only their rational points.
- Reduced locally closed subscheme W: `W : Over (Spec (.of k))`,
  `[IsReduced W.left]`, `j : W ⟶ space k n`, and `[IsImmersion j.left]`.
- Scheme invariance of W: `aW : ModObj ... W` and `hj`, the equality
  `aW.smul ≫ j = (𝟙 G ⊗ₘ j) ≫ a.smul` of scheme maps over k.

Clause-by-clause rendering:

- Z is the reduced induced closed subscheme of the topological closure:
  `reducedClosed n (closureSet n j)`, where `closureSet` is the actual
  `Closeds.closure (Set.range j.left)` and `reducedClosed` uses the recorded
  `Scheme.IdealSheafData.vanishingIdeal T` construction.
- B is the reduced boundary: `∃ B : Closeds (space k n).left` with
  `(B : Set _) = closure (Set.range j.left) \ Set.range j.left`, and
  `reducedClosed n B`. This is the same reduced induced structure as forming B
  inside Z, by uniqueness of reduced induced closed subschemes.
- W identifies with Z minus B as a scheme: `jW` is an open immersion,
  `jW ≫ inclusion ... = j`, `jB` is a closed immersion,
  `jB ≫ inclusion ... = inclusion n B`, and
  `Set.range jW.left = (Set.range jB.left)ᶜ`. An open immersion identifies its
  domain with the open subscheme on its image, so this gives the required scheme
  identification, not just a homeomorphism.
- Z and B have restricted scheme actions: existential `aZ` and `aB` are `ModObj`
  structures, including the unit and associativity identities.
- All inclusions are equivariant: four displayed action-map equalities cover
  Z to P(V), B to P(V), W to Z, and B to Z; W to P(V) is the original `hj`.
- All d≥0: `∀ d : ℕ`.
- Polynomial action on S_d: existential `r : NaturalRepresentation ... S_d`.
  `polynomialTensor` is the actual base change of S_d's submodule inclusion,
  followed by `MvPolynomial.algebraTensorAlgEquiv k A`. Its injectivity follows
  from scalar extension over a field and the algebra equivalence; it is not an
  arbitrary encoding. The action formula for every tensor t says that its image
  is obtained by `MvPolynomial.aeval` substituting the linear forms for
  `(ρ.points A g)⁻¹`. Thus (g f)(v)=f(ρ(g)⁻¹ v), with the correct left-action order.
- Both C=Z and C=B: `∀ T ∈ ({closureSet n j, B} : Set (Closeds ...)), ...`.
- I(C)_d: existential `I : Submodule k S_d`, uniquely fixed by the following
  membership equivalence for every F: each pullback along `inclusion n T` of
  `projectiveClosedSubschemeChartFraction k n d F i` is zero. This is exactly
  F/z_i^d on C intersect D_+(z_i), using the dependency's existing declaration.
  The node explicitly gives this chart criterion as equivalent to vanishing of
  the restricted O(d) section; no point-only criterion replaces it.
- Finite dimensionality: `FiniteDimensional k I`.
- Every commutative k-algebra A and every g in G(A): the binders quantify over
  `(A : Type u) [CommRing A] [Algebra k A] (g : points ... A)` without reducedness,
  nontriviality, finite type or characteristic assumptions on A.
- Exact tensor-submodule preservation: `(I.baseChange A).map
  (r.action A g).toLinearMap = I.baseChange A`. Mathlib's `Submodule.baseChange`
  is the range of `I.subtype.baseChange A`, so this is precisely the actual image
  of A tensor I in A tensor S_d; switching tensor order uses the recorded symmetry.
- Rational restricted representation: `∃ s : NaturalRepresentation ... I` with
  the intertwining equality for the actual `I.subtype.baseChange A` over every A.
  The existing structure supplies group laws, inverses, and naturality.
- Group-scheme representation, explicitly: existential basis b of I and
  `τ : GeneralLinearGroup.RationalHom ... (ULift (Fin (Module.finrank k I)))`,
  `IsMonHom τ`, and the displayed equality identifying s.action on every tensor
  with the linear automorphism of `GeneralLinearGroup.homMulEquiv ... (g ≫ τ)`
  in the base-changed basis b. No arbitrary group-scheme map is accepted.

Dependencies used (module and declarations):

- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `CategoryTheory.ModObj`;
  cartesian products and equivariance use the existing Over monoidal structure.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`;
  scheme products are the cartesian product in `Over (Spec k)`, whose underlying
  scheme is the recorded fibre product.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` imports the existing
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`: `GeneralLinearGroup`
  and `GeneralLinearGroup.homMulEquiv`; the recorded GL/SL node's GL clause is this
  upstream GL, not a new scheme. Its `GeneralLinear.Lie` module supplies
  `GeneralLinearGroup.RationalHom` and `RationalHom.points`.
- `Mathlib.Algebra.MvPolynomial.Basic` / `.Eval`: `MvPolynomial`, `eval₂Hom`,
  `aeval`, and `algHom_ext`; `Mathlib.RingTheory.MvPolynomial.Homogeneous`:
  `homogeneousSubmodule` and its existing total-degree grading.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` / `.Functor`:
  `Proj`, `Proj.basicOpen`, `Proj.toSpecZero`, and `Proj.map`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, with the actual
  `vanishingIdeal`, `.subscheme`, and `.subschemeι` constructions it characterizes.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`,
  `LinearMap.baseChange`, `Submodule.baseChange`;
  `Mathlib.RingTheory.TensorProduct.MvPolynomial`: `MvPolynomial.algebraTensorAlgEquiv`.
- `Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`:
  `RationalRepresentation.NaturalRepresentation`, `.genericPoint`, and the
  `.dictionary` and `.finite_dictionary` proof interfaces. The exact natural-family type
  and universal point are owned in stmt_deps by
  `def-sfb-rational-natural-representation`; the dictionary theorem remains in proof_deps.
- `Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal`:
  `projectiveClosedSubschemeChartFraction` and
  `exists_projectiveClosedSubscheme_homogeneousIdeal`. The exact chart-fraction definition is
  owned in stmt_deps by `def-sfb-projective-chart-fraction`; the homogeneous-ideal
  theorem remains in proof_deps.

Available proof dependencies are imported, including
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`
(`Smooth.geometricallyReduced`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
(`IsClosedImmersion.existsUnique_fac_of_range_subset_range`), and
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(`eq_zero_of_forall_algHom_apply_eq_zero`). The latter node has an incomplete old
module attachment, so the actual upstream source was located and read. The
proof-only `lem-wf-affine-product-reduced` and
`lem-sfb-smooth-group-rational-point-subspace-test` have no recorded declaration;
no imports can yet be supplied for those nodes. They are not needed to type the
statement and are not replaced by private copies.

Searches made:

- msearch LeanFinder: "Invariant reduced projective closure and boundary
  homogeneous ideals are rational subrepresentations of polynomial representations".
  Eight hits on homogeneous ideals of projective spectra; no equivariant closure theorem.
- msearch Loogle: `MvPolynomial.homogeneousSubmodule, AlgebraicGeometry.Proj, Representation`.
  Zero hits.
- msearch grep: `projective.*action|contragredient|homogeneousSubmodule`, restricted to
  AlgebraicGeometry. One unrelated structure-sheaf hit.
- msearch LeanSearch: "algebraic group projective action linear representation
  homogeneous polynomials invariant ideals". Eight hits include the set-theoretic
  `Projectivization` action and homogeneous cores; none give the scheme assertion.
- msearch grep: `IsInduced|projective_invariant_boundary_ideals|ProjectiveInvariantBoundary|polynomialTensor`,
  AlgebraicGeometry. Zero hits.
- rg of the project's `lean/WeilConjectures` and `lean/Sheaf` for projective actions,
  contragredients, homogeneous ideals and rational representations located the
  recorded dictionary, homogeneous-ideal module, general linear group, and the
  relative diagonal projective boundary module. The latter is only a split-torus
  diagonal-action result over a Noetherian ring; it does not state this general
  smooth-group representation theorem. The item id has no upstream Lean occurrence.
- A DAG statement/title search found the diagonal projective action node and
  projective-embedding/attracting-cell nodes, with no general invariant-boundary
  duplicate. The existing diagonal-action predicate is restricted to its Laurent
  torus; the subordinate `IsInduced` predicate fixes arbitrary rho without copying
  its independent torus construction.
- rg of Mathlib tensor polynomial sources found `algebraTensorAlgEquiv`, which is
  reused instead of constructing a second coefficient-change equivalence.

Source checks: read the current `literature/blueprint/latest` direct-image proof
clause (3), Stacks constructions.tex `lemma-closed-in-projective-space` (03GL),
schemes.tex `lemma-reduced-closed-subscheme` (01J3), and the Milne PDF's Remark 4.1,
Corollaries 4.4--4.5, and Lemma 13.46. The combination is agent-formulated, as the
node says, rather than a claim that Milne states this entire theorem verbatim.

Edge cases checked: empty W gives empty Z and B, with full vanishing submodules;
empty B likewise gives all S_d. For d=0 and nonempty C the ideal piece is zero;
the zero-dimensional GL in the conclusion has empty matrix index and is supported
by the existing dictionary. n=0 is allowed, giving P^0. No connectedness, positive
characteristic exclusion, division by d, reducedness of A, or nonzero-algebra
condition occurs. Universal-point matrix substitution fixes the scheme action;
it cannot admit an unrelated action with the same set of invariant points.
No statement dispute was found.

Validation: the complete module compiled cleanly twice through the prescribed
scompile.py, including the explicit restricted group-scheme representation clause.
Only the main theorem is postponed. No global or local direct build was run.

## Second reading by Q91

This is the worker's separate second pass, not a claim of an independent agent
review; the dispatcher explicitly prohibited starting other agents. The
maintainer's independent delivery review remains responsible for that check.
I reopened the node statement and the entire module and matched each field and
clause above. The first compiling version had the natural restricted actions
but left their group-scheme realization to the finite dictionary. The second
pass made this explicit: basis b, monoid homomorphism τ, and its exact point-action
formula are now in the conclusion. I also checked the two signs: the projective
pullback uses rho, while the polynomial left action uses rho inverse. The chart
criterion uses section restrictions, not rational-point evaluation. All four
new inclusion equivariance equations and the existing W-to-projective equation
are present; the open immersion and complement equality give a scheme-level
open-complement identification. Both possible C and every d, A and g are quantified.
The definition bodies contain no sorry and use canonical maps; no helper theorem
has been added. All seven helper declarations and the theorem are listed in lean.


## Repair of returned head 23e70f25006a

H2 is repaired by adding `def-sfb-rational-natural-representation` and
`def-sfb-projective-chart-fraction`, both `existing: true`, on the already
published modules. These replace the two theorem-node additions to stmt_deps.
`lem-sfb-rational-representation-comodule-dictionary` and
`lem-sfb-projective-closed-subscheme-homogeneous-ideal` stay in proof_deps,
unchanged from current main. No definition is copied or relocated, and no
existing dependency node or library source is edited. The item was reconstructed
from current main, retaining all main fields except the authorized lean record
and the two added definition dependencies. Its statement, proof and proof_deps
are unchanged. The sandbox Lean module is byte-identical to the returned version;
SHA256: `c5e37fcff537a52f0d535b6155a9dd5d234a18a8a33172e657a28f22f92a98a6`.
The delivery wrapper refreshes main and builds the new delivery commit.

The immutable-head return independently accepted the Lean hypotheses, induced
scheme action, open complement, action restrictions, equivariance, polynomial
action, chartwise ideals, finite dimensionality, all-algebra stability and
restricted group-scheme representations. Its sole requested change was DAG
ownership of the three plain definitions; all three now have definition owners.

## New nodes

`def-sfb-rational-natural-representation` owns the existing
`AlgebraicGeometry.RationalRepresentation.NaturalRepresentation` and
`AlgebraicGeometry.RationalRepresentation.genericPoint` in
`Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary`.
Its statement takes a field k, an affine k-group scheme G and an arbitrary
k-vector space V, in the same universe convention as the existing declarations.
The `action` field is exactly a group homomorphism on every commutative
k-algebra R into the R-linear automorphisms of R tensor V. The `naturality`
field is exactly compatibility with the map alpha tensor identity, for every
algebra homomorphism alpha, point g, and tensor z. The second owned definition
is the universal coordinate-valued point induced by identity on k[G], with the
actual body `G.isoSpec.inv.asOver (Spec (.of k))`. Its full signature is:

```lean
noncomputable def genericPoint : points (G.asOver (Spec (.of k))) Γ(G, ⊤)
```

The main recorded signature `structure NaturalRepresentation` is verbatim up to
`where`. Its ambient variables are `{k : Type u} [Field k] (G : Scheme.{u})
[G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))] [IsAffine G]`, and
`(V : Type u) [AddCommGroup V] [Module k V]`. The structure fields are:

```lean
action : ∀ (R : Type u) [CommRing R] [Algebra k R],
  points (G.asOver (Spec (.of k))) R →* (R ⊗[k] V ≃ₗ[R] R ⊗[k] V)
naturality : ∀ (R T : Type u) [CommRing R] [Algebra k R]
  [CommRing T] [Algebra k T] (α : R →ₐ[k] T)
  (x : points (G.asOver (Spec (.of k))) R) (z : R ⊗[k] V),
  α.toLinearMap.rTensor V (action R x z) =
    action T (points.map (G.asOver (Spec (.of k))) α x) (α.toLinearMap.rTensor V z)
```

Source: Milne Chapter 4(a), pp.83--84 and Remark 4.1, reopened in the PDF for
this repair. No finite-type, smoothness, connectedness, finite-dimensionality or
nonzero-vector-space hypothesis is added. No comodule dictionary theorem is
claimed by this definition. Its statement cites precisely the field, group,
affine spectrum, scheme-over-base and module-base-change definition nodes.
LeanSearch and LeanFinder found only general affine-space and representation
interfaces; Mathlib grep found topological generic points and unrelated
representations. Project rg located these exact definitions in the published
module; a definition-owner scan of all DAG nodes found none. The blueprint
search `natural representation` found four unrelated nodes. All search outputs
are recorded verbatim in mathlib_searches, including the project rg results.

`def-sfb-projective-chart-fraction` owns the existing
`AlgebraicGeometry.projectiveClosedSubschemeChartFraction` in
`Sheaf.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal`. The statement
takes any commutative ring R, n,d natural, F in the degree-d homogeneous submodule,
and i in Fin(n+1). It specifies the actual regular function F/z_i^d obtained
by applying Proj.awayToSection to its degree-zero homogeneous localization class.
Its signature is copied verbatim from the existing module:

```lean
noncomputable def projectiveClosedSubschemeChartFraction
    (R : Type u) [CommRing R] (n d : ℕ)
    (F : homogeneousSubmodule (Fin (n + 1)) R d) (a : Fin (n + 1)) :
    Γ(Proj (homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) R) (X a))
```

Source: Stacks Tag 03GL, constructions.tex, homogeneous fractions in
`lemma-closed-in-projective-space`, reopened for this repair. The numerator is
F and the denominator is X a raised to d; both have degree d, so d=0 is included.
No closed subscheme, vanishing condition, reducedness or nonzero-ring assumption
is required. The statement cites exactly polynomial-ring and Proj definition
nodes. LeanSearch and LeanFinder found the general Proj.awayToSection and
homogeneous-localization interfaces; Mathlib grep found the same. Project rg
found the exact specialized definition already published. No DAG definition
owned that declaration; `blueprint_refs.py search chart fraction` returned eight
unrelated nodes. The node records these searches and their outputs verbatim.

Both new nodes use the item's chapter and unit, `import_flags: []`, and the
ancestor/via chain computed from current main. The ancestor command returns
None in this inherited chain; the records preserve that null ancestor with the
full computed chain and a concrete description of the boundary-ideal step.
No new Lean module is supplied for either existing:true record.

## Second reading by Q91 — repair

I reread the H2 return, the two new definition statements, their exact source
bodies, the item stmt_deps/proof_deps, and the unchanged Lean module. Both new
nodes describe only their recorded plain definitions: natural actions plus
naturality and the universal point, and the actual homogeneous chart fraction.
Their theorem modules are reused without treating their theorems as statement
definitions. The natural definition permits arbitrary V, including V=0; the
chart definition permits d=0, n=0 and the zero ring. The previous clause-by-clause
reading of the unchanged main theorem still applies. No second agent was started,
as the dispatcher prohibits it; the maintainer supplies independent review.
