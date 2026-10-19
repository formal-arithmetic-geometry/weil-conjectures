## Worker report

The saved packet has been retained and repaired. The module
`Sheaf.Paper.AcyclicFlatProperCoefficientModel` states the bounded acyclic-flat
model calculation, with its sole theorem `acyclicFlatProperCoefficientModel` left `sorry`.
All helper definitions have real data and belong to the constructions explicitly named
by this node. There are no new DAG nodes or dependency repair modules.

Hypothesis-by-hypothesis rendering:

- The schemes and morphism are `{W V : Scheme.{u}} (r : W ⟶ V)`; properness is
  `[IsProper r]`, and the two finite-affine-cover Noetherian conditions are
  `[IsNoetherian W] [IsNoetherian V]`.
- The finite commutative coefficient rings are `{A B : Type (u + 1)}` with
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`. The unital ring homomorphism
  is `φ : A →+* B`.
- The ordinary unbounded derived categories are the existing `DerivedCategoryModule`
  categories on `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` and its B analogue.
  The complex `C` belongs to the corresponding A-module-sheaf cochain category.
- `properCoefficientTensor` abbreviates the published `scalarExtension`.
  `properCoefficientPullbackComparison` abbreviates `scalarPullbackIso.symm`, giving exactly lambda
  in the node (its inverse is used in the transpose), and `properCoefficientMap` abbreviates
  its canonical derived adjunction mate `scalarMate`.
- `coefficientExtendedComplex φ W C` applies the published sheaf scalar-extension
  functor in each degree. This is the B-linear realization of `C tensor_A B`,
  with its usual balancing identification, not an arbitrary functor or map.
- `hC : IsAcyclicFlatProperCoefficientModel φ r C` contains exactly the five model
  assumptions. Its first conjunct is
  `∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (C.X n)`.
  The second is `∀ n, etaleFlat (C.X n)` and the third is the same flatness
  condition on `(lowerStar (ModuleCat A) r).obj (C.X n)`.
  Here `etaleFlat` is exactness of the existing sheaf tensor-right functor.
  The final two conjuncts assert `IsZero` of the q-th homology sheaf of
  `rightDerivedLowerStar` applied to the degree-zero single complex of every term,
  for all integers n and natural numbers q with `0 < q`, first over A and then
  over B on `(coefficientExtendedComplex φ W C).X n`.

Conclusion-by-conclusion rendering:

- `etaleKFlat C` and the same predicate on the degreewise A-direct-image complex
  mean exactly that total tensor with every acyclic complex is acyclic. The total
  tensor is the existing `CochainComplex.mapBifunctor` with `curriedTensor`.
- The next two `IsIso` conjuncts concern `properAcyclicComparison A r C` and
  `properAcyclicComparison B r (coefficientExtendedComplex φ W C)`.
  These are the canonical right-derived units on representatives, composed with
  the inverse homotopy-quotient factor. No arbitrary comparison is chosen.
- The two following `IsIso` conjuncts concern the existing
  `scalarExtensionRepresentative` on C and on the degreewise A-direct-image
  complex D. These are the specified flat-model identifications for T.
- `properSheafCoefficientMap` is the ordinary B-adjoint mate of the canonical
  scalar/pullback comparison and the A-counit. Thus its component at M has the
  stated adjunct: reassociation followed by `counit tensor identity`.
  `properCoefficientComplexMap` applies that natural transformation degreewise,
  including the standard functor-composition identifications. Its components
  therefore commute with the differentials and give precisely pi_C.
- Writing alpha_A and alpha_B for `properAcyclicComparison`, epsilon for
  `scalarExtensionRepresentative`, and Q for localization, the displayed equation is
  `T(alpha_A) ≫ q_r(QC) ≫ Rr_B(epsilon_C) = epsilon_D ≫ Q(pi_C) ≫ alpha_B`.
  All four comparison arrows are separately asserted invertible. This is exactly
  representation by the termwise map under the specified identifications, in
  D(B), retaining its B-linear action. No equation only after forgetting scalars
  substitutes for this assertion.
- The final quantified clause takes every C' with the same five model conditions
  and every chain map h. Its six equations express naturality of q_r, alpha_A,
  alpha_B, epsilon_C, epsilon_D, and pi_C, respectively. Together they express
  naturality of both the identifications and the representing square.
- There is no flatness or finite-projective-dimension assumption on B over A.

Recorded statement-dependency interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the public derived-category
  declarations, including `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, and root
  `DerivedCategory.homologyFunctor` and `DerivedCategory.singleFunctor`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  Its representative normalization supports the canonical scalar/pullback interface.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`; its unbounded right derived functor is the
  existing `rightDerivedLowerStar`/`Functor.rightDerivedFunctor` interface.
- Mathlib `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsProper`,
  `IsNoetherianRing`, and the corresponding scheme `IsNoetherian` condition.

The scalar constructions come from the existing public modules
`Sheaf.Paper.EtaleDerivedScalarTensor` (`scalarExtension`,
`scalarExtensionRepresentative`) and `Sheaf.Paper.PurEtaleScalarMateProjection`
(`scalarSheafPullbackIso`, `scalarPullbackIso`, `scalarMate`).
The module explicitly imports all recorded proof-dependency modules, including
`PreDerivedAdjointFunctorsGeneral`, `BoundedAboveFlatSheafKFlat`, and
`RingedTopoiDerivedPullback`. No proof-dependency import was omitted for a cycle.
Missing local upstream source files were read with `scompile.py --source`, as instructed.

Edge cases: the zero complex, an empty scheme, identity or zero chain maps, and an
empty finite interval are allowed. Only q > 0 is excluded from the vanishing assumptions;
q = 0 is not required to vanish. Zero rings and the identity ring map are allowed.
The non-flat finite coefficient map Z/4 to F_2 is permitted: no derived tensor is
replaced by ordinary tensor without the stipulated flat/K-flat model assumptions.
The coefficient universe u+1 matches the published small-etale six-functor category;
no site object/Hom universe equality or nonemptiness assumption was added.

Searches retained from the saved packet and checked against its searches.jsonl:

- `msearch.py leanfinder`, query "bounded acyclic flat proper coefficient model
  derived direct image projection map": eight irrelevant profinite/Nobeling hits,
  no matching theorem.
- `msearch.py loogle`, query "CategoryTheory.DerivedCategory,
  CategoryTheory.Functor.rightDerived": no hits; the tool reported the first
  qualified name unknown. Root DerivedCategory and the actual functor API were
  subsequently read directly rather than treating this malformed query as evidence.
- `msearch.py grep`, query "acyclic|KFlat|projectionFormula", subdirectory
  Algebra/Homology: generic K-injective/K-projective matches, no target statement.
- `rg` in WeilConjectures and lean/Sheaf for the item and construction names:
  no existing target or duplicate helper declaration. The existing scalar-mate and
  scalar-extension declarations were read in full and reused.
- Repeated `msearch.py leansearch` with "The canonical derived direct image comparison
  on a bounded complex of acyclic flat sheaves identifies change of coefficients with
  the termwise projection morphism": eight generic homology/projection hits, no match.
  A Loogle query for the upstream rightDerivedFunctorUnit was unknown to the Mathlib
  index; its full upstream source signature was therefore read directly.
- Direct Mathlib source reads of `Functor.mapHomologicalComplexCompIso` and
  `Functor.mapHomotopyCategoryFactors`, and upstream
  `Functor.rightDerivedFunctorUnit`, determined the directions of every factor.
- Direct source reads of the current flat-sheaf and K-flat records confirmed that
  their SheafOfModules predicates take a different presentation; the local transparent
  predicates express exactly the node's stipulated tensor tests on its required
  Sheaf(ModuleCat) categories, using existing exactFunctor and total tensor.

No statement correction or STATEMENT-DISPUTED flag is needed. The DAG statement
is unchanged; the repairs make the saved Lean statement render it fully.

## Second reading by NA

This is the dispatcher's required author self-check, not a claim of an independent
review or of another worker's involvement. I reopened the current node and the saved
module and compared each hypothesis and each conclusion. I found: the finite-ring
hypotheses were missing; the canonical acyclic-complex comparisons and their
invertibility were missing; the old projection equality after restriction of scalars
did not state the required B-linear termwise representation; and naturality mentioned
only q_r. The revision restores Finite A/B, constructs the actual canonical comparisons
and ordinary termwise mate, states all four comparison isomorphisms and the required
commuting square, and states all six naturality equations, restricted to maps between
models satisfying the hypotheses. The five model assumptions are unchanged inside
IsAcyclicFlatProperCoefficientModel. I also repaired the exact-signature metadata:
preflight expects the text before :=. The module now lives under Paper, as required for paper-specific material.
All helpers have source/blueprint docstrings;
the sole sorry theorem carries the node's eight-step natural-language proof.

The first prescribed dry run rejected the saved signature metadata. The subsequent
compilation caught an attempted inverse without a local IsIso instance; the square is
now written without inverses, retaining the separately asserted invertibilities.

## Maintainer review fix (2026-10-18)

The independent maintainer review (cc review service) made three changes. The Worker report
and the Second reading above describe the delivered version.

- H4, one definition per notion: the local predicates `etaleFlat` and `etaleKFlat` are removed.
  K-flatness of the two complexes is now stated with the project's existing K-flat predicate
  `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat` (WeilConjectures.FromJoel, used in
  WeilConjectures.CategoryTheory.DerivedCategory.FlatModel and in the normalization
  `scalarPullbackIso_existsUnique` that this statement relies on). Termwise flatness is written as
  `exactFunctor _ _ (MonoidalCategory.tensorRight _)` inline, which is the predicate the record of
  def-pc-flat-sheaf-modules prescribes for the Sheaf (ModuleCat Λ) encoding. No hypothesis or
  conclusion changes mathematically. The two predicates are equivalent through mapping cones,
  and the K-flat conclusion for D now feeds `scalarPullbackIso_existsUnique` directly; a scratch
  compile checked this.
- `properCoefficientPullbackComparison` was `scalarPullbackIso φ r`, which is
  `r_B^* T_V ≅ T_W r_A^*`, i.e. λ⁻¹, although its docstring calls it λ. It is now
  `(scalarPullbackIso φ r).symm : T_W r_A^* ≅ r_B^* T_V`, i.e. λ. Its `inv` equals
  `(scalarPullbackIso φ r).hom` by `rfl`. The coefficient map `properCoefficientMap` (the
  derived mate of `(scalarPullbackIso φ r).hom` = λ⁻¹) is unchanged.
- The theorem docstring's step 3 names the K-flat predicate. The lean record's `statement` and
  `declarations` were updated to match (`etaleFlat` and `etaleKFlat` were dropped).

The fixed module compiles cleanly with nt_compile.py: no error and no warning.
