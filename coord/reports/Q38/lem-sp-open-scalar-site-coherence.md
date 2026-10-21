## Worker report

Delivered module: `Sheaf.Paper.OpenScalarSiteCoherence`. The node is represented by
its eight theorem clauses, with `scalar_site_square` as the primary declaration;
all proofs are `sorry`. Five helper declarations contain actual canonical data.
The statement and the dependency lists are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and an open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`. Composition uses `k : V ⟶ U` with both open-immersion
  instances. No separation, compactness, dimension, or nonemptiness hypothesis is added.
- The finite commutative rings and their unital map are `A B : Type (u + 1)`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`, and `φ : A →+* B`.
  The common coefficient universe is the existing fixed-module convention, allowing
  all finite rings by universe lifting; it does not identify the site object and
  morphism universes, which remain u+1 and u.
- The ordinary constant-module categories are `Etale.DerivedCategoryModule A U`
  and `DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u+1} A))`.
  These are not intrinsically ringed-topos derived categories or adic categories.
- T on the etale site is the existing `Etale.scalarExtension φ X`; on the pro-etale
  site it is `pbcFixedScalarExtension (Scheme.ProEt.topology X) φ`. Both are the
  published left adjoint of the exact derived restriction-of-scalars functor.
  This is derived tensor with B, not ordinary tensor without resolution.
- N is `(comparisonUpperStar (ModuleCat A) X).mapDerivedCategory`.
  Delta is the existing `pbcComparisonReduction X φ`: the canonical invertible
  scalar adjunction mate of coefficient restriction commuting with comparison.
  No arbitrary natural isomorphism is assumed or selected.
- Etale t is the existing `Etale.openScalarExtension φ j`. The pro-etale t is
  `scalarOpen φ j`, constructed using the exact open adjunction and the same
  derived scalar adjunction. `restrictScalarsIso` identifies the two literal
  sectionwise restriction composites, transported through the published
  open-restriction identifications; its exact derived descent specifies the mate.
  On sheaves the transpose sends each extension generator s tensor b to the
  same indexed generator with section s tensor b, so this fixes the prescribed
  summand comparison. Deriving this mate gives its K-flat-model interpretation.
  These helpers belong to this node's comparisons, not new independent notions.
- The site e is reused verbatim as
  `mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso (ModuleCat R) j`
  from the published upstream OpenCover module. Its ordinary source is the
  comparison in the recorded dependency; no duplicate site comparison is defined.
- A complex P is explicitly bound, as is L. Boundedness is
  `∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)`;
  termwise flatness is `∀ n, Etale.etaleFlat U A (P.X n)`.
  `hrep : Nonempty (DerivedCategory.Q.obj P ≅ L)` means precisely that P represents L.
- `extension_flat_kflat` states four clauses: termwise flatness and K-flatness of
  etale j!P, and termwise flatness and K-flatness of pro-etale j!N(P).
  The etale flat/K-flat abbreviations expand to the recorded `IsFlatOnSite` and
  `IsKFlatIndependentCoefficients` predicates under the existing constant-module
  realization. For pro-etale coefficients `proRealization` composes the recorded
  `finiteCoefficientRealization` with restriction along the existing canonical
  `finiteCoefficientCommRingComparison`; this only transports RingCat continuous
  finite coefficients to the commutative constant ring sheaf needed by those
  same predicates. Its finite coefficient topology is explicitly discrete,
  constructed inside the helper, not an extra input hypothesis. Topology and R
  are explicit in the flatness predicate to retain the correct site universes.
- `scalar_site_square` has exactly the displayed equation. Lean's `≫` reads in
  execution order, opposite to written mathematical composition: its left route
  is `T_X.map e_A ≫ t_pro.app (N_U L) ≫ j!pro_B.map delta_U`; its right route is
  `delta_X.app (j!et_A L) ≫ N_X.map t_et ≫ e_B.app (T_U L)`.
  Both are morphisms in D(X_proet,B), with the same source and target. The equality
  is not obtained by assuming faithfulness of derived forgetting to A-modules.
- Naturality in L is already part of the types of every comparison: they are
  natural isomorphisms between the specified functors. Each route is therefore
  natural; equality is asserted for each object with its bounded flat representative.
- `etale_scalar_comp` and `proetale_scalar_comp` state the scalar composition law
  on their respective sites. They first apply T to the A-open compositor, then t_j
  at k!L, then j!_B of t_k, and finally the inverse B-open compositor; this equals
  t_(k≫j). Thus neither compositor has been silently replaced by a definitional
  identity. The etale compositor is reused, and `extensionComp` is exact descent
  of the recorded `proEtaleOpenExtensionComp`.
- `site_comp` states the corresponding derived e composition equation for a finite
  coefficient ring R, so it applies separately at A and B. The equation uses both
  open compositors and the actual N functors.
- `etale_scalar_id`, `proetale_scalar_id`, and `site_id` give the identity clauses
  after the canonical identity extension identifications. `extensionId` is exact
  descent of the pro-etale open-adjunction identity, while the etale identity is
  reused from upstream. This does not falsely assert definitional equality of
  chosen adjoints with identity functors.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the same module as the recorded
  `DerivedCategory.torsionCohomology`, whose torsion restriction is not imposed here).
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `finiteCoefficientRealization`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, with its fixed-module comparison inverse image.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its fixed-coefficient canonical tensor mate is the existing
  `ProEtale.pbcComparisonReduction` in `Sheaf.Paper.WitnessCompatibility`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`:
  `SheafOfModules.ringedSlice_extension_tensor`, used in the flatness/model proof plan.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, its derived scalar
  adjunction/K-flat computation, specialized by the published fixed-scalar functor.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparison_coherence`, `proEtaleOpenExtensionComp`.
  Its derived e is reused from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover`.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `Etale.openImmersionLowerShriekComp_coherence`; derived compositor and identity
  are reused from upstream `Etale.Derived.LowerShriekComposition`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.SixFunctors.EtaleOpenTensor`: `Etale.etaleOpenTensorComparisons` and its
  definition module's `openScalarExtension`, `etaleFlat`, `etaleKFlat`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientCommRing`, `finiteCoefficientCommRingComparison` are the
  canonical coefficient transport used by the pro-etale realization.
- Scheme and open immersion are the recorded Mathlib `Scheme` and `IsOpenImmersion`.
  The node's other published proof-dependency modules are imported for stage 3,
  including the exact localized-system theorem, bounded-flat K-flatness,
  comparison exactness, K-flat pullback, tensor/unit normalization, extension
  generators and sheafification, exact open extension, and projection formula.

Edge cases checked before finalizing: P=0; empty U (all extended terms zero);
empty X; identity open; identity coefficient map; the zero ring and its permitted
unital maps. No Nontrivial hypothesis is present. For Z/4 → Z/2, B need not be
A-flat; bounded flat P still computes its derived extension, and P tensor B is
never assumed A-flat. An L without a bounded flat representative is excluded only
from the square/flat-model assertion, exactly as in the node. Composition and
identity comparisons are canonical functor comparisons on the whole ordinary
module derived categories.

Sources opened: Stacks `sites-cohomology.tex`, lemma-j-shriek-and-tensor (0GL1),
and `proetale.tex`, lemma-jshriek-comparison (09AF). The former resolves on K-flat
models and the latter identifies the two left adjoints to the same right adjoint.
The module's theorem docstrings contain the seven-step proof plan, split among
flatness, the square, and composition/identity clauses. No source statement
correction and no STATEMENT-DISPUTED issue were necessary.

Searches:

- msearch leanfinder: `Open extension by zero derived scalar extension etale
  proetale comparison commutes naturally on bounded flat complexes`; eight
  ordinary algebra/formally-etale results, no matching square.
- msearch loogle: `CategoryTheory.Sheaf, CategoryTheory.Adjunction`; generic
  sheafification/adjunction results, no matching normalized geometric assertion.
- msearch grep in CategoryTheory: `openScalar|scalar.*comparison|extensionByZero.*tensor`;
  zero Mathlib hits for the requested whole statement.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for open/scalar/site comparison
  names located the existing etale t, site e, canonical fixed-scalar delta, and
  sheaf coherence inputs used above. Searching the item id in WeilConjectures
  found no statement of this node. Mathlib's generic tensor/adjunction machinery
  does not state this B-linear square with its flat-model and coherence clauses.
- A downstream finite-free projection exchange interface was also inspected but
  not imported: its DAG reaches this very node through coefficient compatibility.
  The missing pro-etale exact-open scalar mate is therefore constructed directly
  here from the already available adjunctions, without a cyclic dependency.

Validation: prescribed scompile.py compiled both the sandbox and the library
module successfully; the final delivery dry run is recorded by the delivery tool.
Only the expected theorem `sorry` placeholders remain. Definitions contain actual
functors, transformations, and canonical adjunction isomorphisms.

## Second reading by Q38

The dispatcher explicitly forbids starting other agents and assigns independent
review to the maintainer. This section records my second self-reading, not a
claim of an independent worker review. I checked every node clause against the
file after compilation, both source/target B-module categories of the square,
the direction of delta, both compositor directions, and identity normalization.
An initial elaboration issue in the pro-etale flatness predicate was repaired by
explicitly specifying its topology and commutative coefficient ring, retaining
the actual site object/morphism universes. Long lines were split. No mathematical
hypothesis, conclusion, dependency record, or node statement was changed.
