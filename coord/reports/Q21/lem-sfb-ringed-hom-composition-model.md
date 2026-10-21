## Worker report

Item: lem-sfb-ringed-hom-composition-model. One new module,
`Sheaf.Algebra.Homology.RingedHomCompositionModel`, with three theorem statements
whose proofs are `sorry`, and four definitions with specified data. No statement
correction, extra DAG node or dependency repair is needed.

Clause-by-clause correspondence:

- The arbitrary ringed site is `{C : Type c} [Category.{v} C]`,
  `J : GrothendieckTopology C`, `R : Sheaf J CommRingCat.{max c v u}`.
  Site objects, arrows and extra coefficient size remain independent. The module
  universe `max c v u` contains the site. `HasSheafify` and
  `WEqualsLocallyBijective` are the standard small-site sheafification interfaces.
- The category is the recorded `RingedTensorModules J R`, transparently the
  recorded `ringedSiteModules`, namely Mathlib `SheafOfModules`. The unbounded
  category and localization are `DerivedCategory` and `DerivedCategory.Q`, with
  explicit independent `[HasDerivedCategory.{w} ...]`.
- The ordinary Hom complex is exactly `homComplex (R := R)`; total tensor is
  `coefficientTotalTensor J R`, the recorded totalization of the sheaf tensor.
  No alternative Hom or tensor complex is introduced.
- The fixed derived Hom is `derivedInternalHomOfUniverses J R`.
  `ringedHomAugmentation` is precisely the augmentation of the existing
  `coefficientHomResolution`. `ringedHomRepresentativeMap E F` postcomposes
  by that augmentation and follows it by `coefficientHomResolutionIso.inv`.
  Thus the comparison is canonical, not an arbitrary representative isomorphism.
- The fixed closed monoidal data are `S : CoefficientClosedStructure ...`,
  `N : CoefficientTensorModels J R S`, the symmetry `β`, and their specified
  `D : RingedDerivedTensorCoherence J R S N β`. They are the data supplied by
  `ringedDerived_closed_symmetric_monoidal`, not new restrictions on E,F,G,T.
  The coefficient complex O is the imported `ringedTensorUnitComplex`; its
  derived unit identification is `D.unitIso`. O is only notation in this node.
- The displayed definition of c is already exactly `S.composition`: its body
  transposes the associator followed by `1 tensor evaluation` and evaluation,
  for the right-tensor adjunction. We reuse it without redefining composition.
- `ringedHomComposition_naturality` has three conjuncts, in order:
  contravariant naturality for every `a : K' ⟶ K`, covariant naturality for
  every `b : M ⟶ M'`, and the displayed dinaturality for every derived
  `f : L ⟶ L'`. In the last conjunct the common source is
  `H(L',M) tensor H(K,L)` and the common target is `H(K,M)`.
- For arbitrary complexes E,F,G (the node's E,J,I),
  `ringedHomComposition_existsUnique` asserts `∃! m` with
  `RingedHomCompositionFormula`. The predicate quantifies over every object U,
  degrees p,q,k,a,b and the three degree equalities. Applying the a-product
  projection to m on the actual sheafified tensor generator equals the
  q-component of g followed by the p-component of f on the slice over U.
  This is exactly `f^{a+q} ∘ g^a` with no sign. Equality is equality of slice
  module-presheaf morphisms, hence includes all local sections and restrictions.
  The independent equality proofs merely avoid dependent casts; the degree
  equations always supply them.
- `ringedHomComposition` selects the map from this unique characterization;
  the named existence theorem determines the object up to equality. This
  satisfies the no-hollow-data rule; no arbitrary mere-existence choice occurs.
- `ringedHomComposition_model` assumes exactly `[F.IsKInjective]`,
  `[G.IsKInjective]`, and the given `t : T ⟶ homComplex E F` with
  `IsKFlatResolutionIndependentCoefficients t` (quasi-isomorphism and K-flat T).
  Its left side is the canonical one-K-flat comparison `D.tensorIso`, then the
  two canonical Hom comparisons (including Qt on the second factor), then c.
  Its right side is Q of `(1 tensor t) ≫ ringedHomComposition E F G`, followed
  by the output Hom comparison. This is the exact requested representative square.
- There are no boundedness, perfectness, flat-term, or K-flat assumptions on E,F,G.
  In particular, Hom(F,G) need not be K-flat: `Or.inr ht.2` uses T alone.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `homComplex`,
  `homComplexFunctor`; its projection API `homComplexπ` is reused through
  `coefficientHomComponent`, not reconstructed.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  the existing coefficient tensor wrapper uses this totalization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `IsKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses` and its localization construction.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, its `composition`, `tensor`, `transpose`,
  `evaluation`; `CoefficientTensorModels`, `coefficientTotalTensor`,
  `coefficientTensorGenerator`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `coefficientHomComponent`, `coefficientHomResolution`,
  `coefficientHomResolutionIso`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedTensorModules`, `RingedDerivedTensorCoherence` (especially `tensorIso`),
  `ringedDerived_closed_symmetric_monoidal`.
- The size-convention dependency has a convention-only record, with no declaration;
  its role is rendered by the explicit c,v,u,w universe parameters.
- Every stated proof-dependency module is imported, including K-flat resolutions,
  Hom quasi-isomorphism invariance, native derived tensor, normalized tensor-Hom
  adjunction, sheaf tensor universes, and presheaf-module sheafification.

Edge cases checked before writing: zero complexes and the zero coefficient ring;
empty site; negative and zero p,q,a and total degree; p+q cancellation; unbounded
Hom products (componentwise composition involves no infinite sum); arbitrary
K-injective F,G rather than only the fixed resolution; arbitrary given K-flat
resolution t with no flat-term restriction; arbitrary derived middle morphism
f, not only a chain representative. The sign-free formula gives the usual
composition in degree zero and obeys the stated Leibniz rule in every degree.

Searches (2026-10-21):

- `msearch.py ... leanfinder`: “Composition of derived internal Hom on a ringed
  site agrees with composition of Hom complexes on K-injective and K-flat
  representatives”. Eight hits, including `SheafOfModules.comp_val`,
  `SheafOfModules.unitHomEquiv_comp_apply`, and light-condensed internal Hom
  evaluation. None supplies the sheaf-valued Hom-chain composition comparison.
- `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed, "comp"`.
  Twelve hits, notably `MonoidalClosed.enrichedCategorySelf_comp` and exponential
  comparisons. These identify abstract compositions, not this representative square.
- `msearch.py ... grep`: `homComplex.*[Cc]omposition|[Cc]omposition.*homComplex|enrichedCategorySelf_comp`.
  Only `Mathlib/CategoryTheory/Monoidal/Closed/Enrichment.lean:55` matched.
- `rg` in both project Lean trees for `homComplex.*[Cc]omp|[Cc]omp.*homComplex|HomComposition|homComposition`:
  found Hom projections, scalar composition and scheme transport, but no exact
  statement. Searching the item id in both trees found no declaration.
- `rg` for all seven proposed names in both Lean trees and
  `dag/lean_names_upstream.json`: no prior declaration or name collision.

Source checked directly: `literature/stacks-project/sites-cohomology.tex`,
`lemma-composition` (0A91) and `lemma-internal-hom-composition` (0A98), including
its arbitrary K-flat second-factor resolution; the proof in the node supplies
all-variable functoriality and agreement with the stipulated 08J9 normalization.

No STATEMENT-DISPUTED finding. The example CompactObject module is now withdrawn
in the shared checkout; its current file was read. The active module header and
public-section conventions were taken from the recorded dependency modules.

Validation: all compiles use the prescribed `scompile.py` server wrapper.
The initial elaboration fixes made the augmentation universe explicit and gave
explicit source/target product objects in one dinaturality tensor map. They change
no mathematical hypothesis or conclusion. The final module passed both sandbox and library compiles without warnings.
`deliver2.py Q21 lem-sfb-ringed-hom-composition-model --no-push` returned
`OK (dry run): commit 3bafb0a67ef passes the preflight and compiles; nothing pushed`.
The only changed field of the original node is `lean`; all Lean lines are at most
100 characters. The delivery wrapper repeats the compile and preflight before push.

## Statement self-check

This is a self-check by the dispatcher-started worker, not an independent second
reader. The brief forbids starting other agents and assigns independent review
to the maintainer. Re-reading the node and file confirms: naturality has the
correct variance, dinaturality starts at H(L',M) tensor H(K,L), the chain formula
composes g then f with no sign, uniqueness is uniqueness of that formula alone,
and the model square uses the actual fixed augmentation and the supplied t.
The arbitrary one-K-flat case and all independent universes remain present.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
