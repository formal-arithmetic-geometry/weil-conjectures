## Worker report

Item: `lem-sfb-hom-strict-numerator-transpose`, group Q80. The single module
`Sheaf.Paper.StrictHomNumeratorTranspose` states the strict normalized numerator
transpose as `WeilConjectures.SfbHomFilteredColimit.strict_numerator_transpose`.
Its proof is the only `sorry`. The preceding public data records and proposition definitions merely expand
its maps and laws; the abbreviations and map definitions contain actual data.
No mathematical correction, disputed statement, new DAG notion or dependency-module
repair is needed. The already-landed `def-pc-flat-sheaf-modules` is added to
`stmt_deps` to name the flat-term hypothesis explicitly.

Hypotheses and objects:

- The site has `C : Type u`, `[Category.{v} C]`, and `J : GrothendieckTopology C`.
  Rings and modules live in `max u v r`, so the site is small relative to them;
  the sheafification and locally-bijective-equivalence instances are those used
  by the recorded abelian module category. No equality of the site universes
  or of the derived morphism universe `w` is imposed.
- `R : Sheaf J CommRingCat.{max u v r}` is the given commutative ring sheaf.
  `Modules J R` transparently uses `CategoryTheory.ringedSiteModules` and
  Mathlib's `SheafOfModules`, not a different category.
- `P L : CochainComplex (Modules J R) ℤ` are the node's P and C respectively.
  `L` is used as a binder name to leave `C` available for the site category.
  `hP` is the recorded independent-coefficient K-flat predicate; `hflat`
  explicitly requires `SheafOfModules.IsFlatOnSite (P.X n)` in every integer
  degree. No other hypotheses are imposed on either complex.
- `[HasDerivedCategory.{w} (Modules J R)]` and `DerivedCategory.Q` are the
  recorded localization. `S` and `M` are exactly the normalized closed structure
  and its `CoefficientTensorModels`; their objects, adjunction and comparison
  are used directly.
- The universally quantified `T : Modules J R` in all scalar-evaluation and
  transpose fields is completely unrestricted. The recorded `tensor` uses
  `HomologicalComplex.single ... 0` and the actual `coefficientTotalTensor`.
  Thus T is in degree zero, B is `(homFixed J R P).obj L`, J is
  `(coefficientHomResolution J R).obj L`, A is `numeratorSource J R P L T`,
  and N = T tensor J is `numeratorTarget J R L T`.
- The map a_T is always `(comparison J R P L).app T`, the recorded unique
  normalized comparison. No map is supplied as a replacement assumption.

Every conclusion and its rendering:

- `StrictNumeratorData.evaluation` has source the actual total B tensor P and
  target the fixed I(L). the `evaluation_formula` clause of `StrictNumeratorLaws` says f tensor x
  maps to f(x), using `homValue` at the actual product projection and identity
  object of the localized site.
- `evaluation_derived` uses `coefficientHomResolutionIso ... .inv` to identify
  QB with the existing derived internal Hom. The actual closed evaluation,
  transported along `tensorIso B`, equals `Q.map evaluation` followed by
  `coefficientHomResolutionInverse L`. This is the specified inverse-augmentation
  normalization into QL, without replacing I(L) by another resolution.
- `StrictNumeratorData.scalarEvaluation` is the chain map h_T from the actual
  total A tensor P to N. `scalar_formula` is exactly
  `((t tensor f) tensor x) ↦ t tensor f(x)` on every object of the site and every
  homogeneous summand. The nested `tensorGenerator` and
  `coefficientTensorGenerator` are the actual sheafification-unit and coproduct
  inclusions, not an assertion that all sheaf-tensor sections are globally pure.
- `uncurry_formula` characterizes the chain uncurrying of the fixed a_T on
  arbitrary sections of A, using the actual product-Hom projection. `uncurry_eq`
  identifies this map with `scalarEvaluation T ≫ (resolutionUnit J R).app N`.
  Categorical composition is left-to-right, so this is precisely eta_N composed
  with h_T.
- `transpose_derived` writes the inverse of the actual `S.transpose` Hom
  equivalence applied to `Q.map a_T` and the fixed Hom representative factorization.
  Precomposing by `tensorIso A` gives exactly `Q.map (scalarEvaluation T)`.
- `tensorIso X` identifies `Q(total(X tensor P))` with the given derived tensor
  for every unrestricted first complex X. `tensor_natural` makes this a natural
  extension; `tensor_normalized` sets its restriction on every K-flat X equal
  to `CoefficientTensorModels.iso` verbatim. These conditions determine the
  canonical comparison by a K-flat resolution of X; an arbitrary isomorphism
  disconnected from M would not satisfy this proposition. In particular X = A is
  allowed without a flatness or K-flatness hypothesis.
- `StrictNumeratorNaturality` quantifies over simultaneous `b : P' ⟶ P`,
  `c : L ⟶ L'`, and `a : T ⟶ T'`. Its evaluation, scalar, comparison and uncurry
  squares express contravariance in P and covariance in L and T. Its tensor
  square gives the corresponding naturality of the one-sided comparison in P;
  naturality in X is already in `tensor_natural`. `numeratorHomMap` uses exactly
  precomposition by b followed by resolved postcomposition by c. These are chain
  equalities, hence also equalities after localization. Combining them with the
  two derived equations gives the naturality squares for the identifications.
- `invertible_changes` explicitly states that quasi-isomorphisms b and c give
  quasi-isomorphisms of B, I(L), A, N and both total-tensor changes occurring in
  the scalar square. Q therefore inverts all the changes, including those
  tensored with non-flat T. The same square equations commute with inversion
  by composing with these inverses; no flatness of T is used.
- For compatible coefficients, `StrictNumeratorCoefficientMaps` uses an actual
  ring-sheaf map `φ : R ⟶ R'` and linear arrows into the actual scalar restriction
  functor, so its section maps are semilinear over φ. Supplied tensor and Hom
  comparisons must satisfy `StrictNumeratorCoefficientCompatible`: preservation
  of evaluation on actual projections, the A and N tensor generators, the
  total-tensor generators and the fixed augmentation square. These hypotheses
  are exactly the evaluation-preserving comparisons of proof step 7, not a claim
  about arbitrary extension through infinite Hom products. The theorem concludes
  `StrictNumeratorCoefficientSquares`, giving evaluation, scalar evaluation
  and uncurrying squares as exact chain equalities (a_T enters through its uncurrying). Applying Q and using
  `transpose_derived` gives the coefficient square for the derived transpose.
  The second coefficient system has its own independent derived universe `w2`.
  Identity and composite compatible comparisons obey the same universally
  quantified equations.
- The tensor order in every source is `(A, P)` or `(B, P)`; the generator formulas
  contain no permutation and no interchange sign. All integer degrees, unbounded
  complexes and arbitrary modules are admitted. There are no boundedness,
  finite-generation, flatness-of-T or continuity binders.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the Mathlib `SheafOfModules` category and its abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, its `tensor`, `evaluation`, `transpose`,
  `coefficientTotalTensor`, `coefficientTensorGenerator`,
  `CoefficientTensorModels` and `CoefficientTensorModels.iso`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `coefficientHomResolution`, `coefficientHomResolutionIso`,
  `coefficientHomResolutionInverse`; the recorded `coefficientHomSectionEvaluation`
  was read and its underlying actual projection is used through `homValue`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Paper.DerivedInternalHomFilteredColimitData`:
  `Modules`, `tensor`, `tensorFixed`, `homFixed`, `tensorGenerator`, `homValue`,
  `resolutionUnit`, `Normalized` and `comparison`. These are public imports.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (the added, already-landed statement dependency).
- Proof dependencies already exposed by the public imports include the functorial
  K-injective resolutions, sheaf tensor, total tensor, and actual Hom complex.
  The recorded modules for `isKInjective_homComplex_of_isKFlat`,
  `quasiIso_homComplex_map` and Mathlib's `IsKInjective.quasiIso_iff` are imported
  for the future proof. `lem-sfb-hom-kflat-chain-transpose` has no recorded module
  or Mathlib match yet; it is a proof dependency only. No object used in this
  statement waits on it, and no module is invented for it.

Edge cases checked against the signatures and source calculation:

- T = 0, P = 0, L = 0 and the empty site are admitted; all displayed maps become
  the corresponding zero maps, and no Nonempty site or section assumption appears.
- Degree-zero complexes give ordinary `(t tensor f) tensor x ↦ t tensor f(x)`.
  Negative and odd homogeneous degrees are included; the differential formula in
  the theorem docstring cancels the two `(-1)^n f(d_P x)` contributions.
- A non-flat coefficient module such as Z/2 over Z is permitted. No tensoring of
  an arbitrary quasi-isomorphism by T is asserted: the representative changes
  used here are homotopy equivalences between K-injectives.
- Fully unbounded P and L, products in the Hom degree and coproducts in the total
  tensor are retained. The section formulas are checked before sheafification.
- Identity and zero maps in each naturality variable are covered, as are identity
  and composite compatible coefficient maps. Independent site and derived
  universes remain bound explicitly, with `autoImplicit false`.

Searches for an existing statement (2026-10-21):

- `msearch.py ... leanfinder`: “For an arbitrary module sheaf T and K-flat complex P
  the derived transpose of T tensor Hom(P,I(C)) to Hom(P,I(T tensor I(C))) is scalar
  evaluation”. Eight hits: ordinary ModuleCat evaluation/co-evaluation, Ext and
  flat-module/Tor infrastructure. No strict normalized unbounded sheaf statement.
- `msearch.py ... loogle`: `MonoidalClosed.uncurry, homTensorUncurry` gave zero hits
  and an unknown-name diagnostic. The corrected query `"MonoidalClosed", "uncurry"`
  gave twelve generic monoidal-closed curry/uncurry lemmas, without the fixed
  ringed-site Hom representative or inverse augmentation.
- `msearch.py ... grep`: `homComplex.*(transpose|uncurry)|homTensorUncurry|homTensorCurry`
  gave zero Mathlib matches.
- `msearch.py ... leansearch`: “The derived transpose of a normalized tensor Hom
  comparison on unbounded complexes of sheaves is scalar evaluation for an arbitrary
  coefficient module” gave eight dual-module contraction/transpose and polynomial
  tensor hits, none matching this assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: searched strict numerator,
  `homTensorUncurry`, `homTensorCurry`, tensor comparisons, `StrictNumerator`,
  `strict_numerator_transpose` and `scalarEvaluation`; read the native
  `HomTensorDegreewise`, `HomTensorTotal`, fixed strict data and coefficient model.
  Native Hom-total comparison has a smaller coefficient-universe API and states
  a different internal Hom isomorphism, not this normalized coefficient numerator.
  The completed/pro-etale coefficient modules concern other objects and maps.
  `grep -rn` for the exact item id under `lean/WeilConjectures` found no declaration.
  No duplicate of any delivered declaration was found.

Validation: every delivered Lean file is compiled via the prescribed `scompile.py`;
final dry-run and delivery results are recorded by the launcher wrapper. All work
is confined to the named sandbox; no direct git command or live-source edit was used.

## Second reading by Q80

This is a second self-reading with the node and final Lean source open; the
independent maintainer review is still required. No additional agent was started,
as the dispatcher expressly forbids it. Rechecked each hypothesis and clause
against the mapping above, the inverse-augmentation orientation and the mixed
variance squares. The one-sided tensor isomorphisms are constrained by naturality
and the existing normalized comparison. The coefficient assertion concerns supplied
evaluation-preserving comparisons, and its chain squares represent the derived
transpose via the actual Q(h). Flatness is required only of every term of P;
T and A are unrestricted. Every helper belongs to this node's map/law package,
and every actual tensor, Hom, resolution and section generator is imported.
During this reading the tensor-map source/target annotations and all flatness
universes were made explicit. Proposition-valued records were changed to conjunction
definitions, preserving their clauses while avoiding expensive generated recursors.
The two evaluation equations were rechecked explicitly after this conversion.
The theorem's proof docstring was checked
against all seven proof steps. There is no statement correction or disputed claim.

## Maintainer review correction (stage-2 second reader, 2026-10-21)

The coefficient conclusion `StrictNumeratorCoefficientSquares` contained a `comparison`
square `a_T ≫ augmentedHomMap = sourceMap ≫ restrict(a'_{T'})` for a supplied arrow
`augmentedHomMap` between the Hom representatives, constrained only by evaluation at the
image of the supplied map of P. That square is false: with φ = 𝟙, all supplied maps zero
except `augmentedHomMap` (an isomorphism onto the restricted Hom complex), every
compatibility clause holds while the square says a_T = 0, which fails for T = R,
P = L = R[0]. The square, the field `augmentedHomMap` and its `augmented_evaluation`
hypothesis (used only by that square) were removed. The node's coefficient claim for a_T
is still rendered by the `uncurry` square (uncurried a_T = η_N ∘ h_T, proof step 7), and the
derived transpose by the `scalar` square together with `transpose_derived`.

