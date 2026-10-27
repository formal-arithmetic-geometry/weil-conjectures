## Worker report

The module `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology` states
`SheafOfModules.FlatSingleTensor.ringed_flat_single_tensor_cohomology`.
The theorem is the only postponed proof. Seven transparent abbreviations name
existing functors, maps and comparisons; none introduces a second tensor,
localization, cohomology functor, flatness predicate or K-flatness predicate.
All declarations carry source and blueprint docstrings; the theorem docstring
contains the six-step proof of this node. No source statement was corrected.

Hypotheses and clauses, in order:

* A site small relative to modules is `{S : Type u} [Category.{v} S]`,
  `{J : GrothendieckTopology S}` and `[EssentiallySmall.{r} S]`.
  These are independent universes: object and morphism universes are never
  identified with one another or with `r`. `R : Sheaf J CommRingCat.{r}`
  supplies exactly the commutative ring sheaf. The smallness instances give
  sheafification and the abelian module category. `Modules R` transparently
  uses the recorded `CategoryTheory.ringedSiteModules` / `SheafOfModules`.
* `[HasDerivedCategory.{w} (Modules R)]` chooses the morphism-size convention
  of the unbounded derived category, whose localization is `DerivedCategory.Q`.
  The module uses the already published `derivedTensor R`, literally the
  curried `siteDerivedTensorIndependentCoefficients J R`. It introduces
  no new tensor choice, arbitrary comparison, or assumption of a comparison.
* Flat sheaves are quantified as `L : Modules R` with
  `IsFlatOnSite (J := J) (R := R) L`, exactly the recorded exactness of ordinary
  right tensor. Flatness is not a sectionwise exactness assumption.
* `degreeZero R` is `HomologicalComplex.single (Modules R) (.up ℤ) 0`.
  The witness `hs` asserts both `IsKFlatIndependentCoefficients` of this
  complex and `∀ n : ℤ, IsFlatOnSite ... (L[0].X n)`, including all zero terms.
* `totalRight R L` is the published signed direct-sum total tensor with
  `degreeZero R L` on the right. `termwiseRight R L` applies the existing
  `tensorRight L` to every object and differential. `degreeComparison` is
  the upstream `CochainComplex.mapBifunctorSingle₂Iso`, whose formula uses
  projection to / inclusion of the surviving `(n,0)` summand. Its signed
  interchange is one on that summand. Thus it is the specified degreewise
  identification, including its differential and its orientation.
* The derived-object family `a` is a natural isomorphism
  `(DerivedCategory.Q ⋙ derivedRight R L) ≅
  (totalRight R L ⋙ DerivedCategory.Q)`. It precedes the cohomology families,
  retaining the derived-object comparison required by the October 21 convention.
  Its first normalization equation identifies `a` on every flat-term K-flat
  `P` with the inverse of the published `representativeIso R P L[0]`.
  Its next equation states naturality in every module map `g:L→L'` between
  flat sheaves; naturality in all cochain maps is part of the natural iso.
* The `c L hL K i` family is exactly
  `H^i(totalRight R L K) ≅ K.homology i ⊗ L`, for every integer `i` and every
  unbounded `K`. The existential cycle isomorphism `z` is uniquely fixed by
  `z.hom ≫ (K.iCycles i ▷ L) = termwise.iCycles i`. The following quotient
  equation uses `termwise.homologyπ`, homology of `degreeComparison.inv`,
  and `c.hom`. This forces the map on the quotient of cycles by boundaries,
  rather than choosing an arbitrary isomorphism. Boundaries are the image
  killed by this canonical cycle quotient in the abelian sheaf category.
* The next conjunct is simultaneous naturality of `c` for arbitrary
  cochain maps `f:K→K'` and arbitrary module maps `g:L→L'` between flat
  sheaves: `H(totalMap f g) ≫ c' = c ≫ (H(f) ⊗ₘ g)`.
* For each flat `L` and integer `i`, `gamma L hL i` is the natural iso
  `derivedRight R L ⋙ DerivedCategory.homologyFunctor ... i ≅
   DerivedCategory.homologyFunctor ... i ⋙ tensorRight L`.
  This includes naturality in ALL derived morphisms. The next conjunct gives
  its square for every module map `g:L→L'`, with no condition on `g`.
* The next conjunct identifies restriction of `gamma` along `Q` with
  cohomology of `a` followed by `c`; the `homologyFunctorFactors` isos keep
  every source and target at its actual chosen localization, rather than
  pretending that the cohomology comparison is definitional equality.
* Finally `P,K,p,_hp,hP,hPf,i` quantify over EVERY flat-term K-flat resolution
  `p:P→K`, with only `QuasiIso p`, K-flatness and termwise flatness.
  The model arrow is exactly `representativeIso.hom ≫ derivedMap (Q.map p) (𝟙 L)`.
  The equation says its cohomology followed by `gamma` equals `c_P` followed
  by `H(p) ▷ L`, with the explicit localization cohomology factors at both ends.
  In particular the same `gamma` satisfies the equation for all resolutions,
  expressing resolution independence without asking for maps between resolutions.
* There is no boundedness, constructibility, finite generation, or Tor-amplitude
  binder anywhere. Complexes range over `CochainComplex ... ℤ` and derived
  objects over the full `DerivedCategory`.

Dependency declarations read and used:

* `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, `cochainModulesPreadditive`
  and the existing countable-colimit tensor instances. This is exactly the
  recorded ordinary sheaf tensor, not a private copy.
* `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, `Functor.map₂CochainComplex`;
  `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₂Iso`.
* `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.siteDerivedTensorIndependentCoefficients`, selected with
  its resolving comparison by the existing
  `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` interface:
  `SheafOfModules.KFlatFixedTensor.Modules`, `totalTensor`, `derivedTensor`,
  `representativeIso`, and its `derivedTensor_eq_published` equality.
  The owning, already landed definition node
  `def-sf-ringed-kflat-tensor-representative-data` is added to `stmt_deps`
  under brief §5's authorization to cite landed declarations. Its existing:true
  record owns exactly these tensor definitions and representative data;
  the triangulated theorem's conclusion is not used. No dependency node changed.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` (exact sheafified tensor).
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (all acyclic test complexes).
* Proof imports, without `public` where only used by the proof plan:
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
  (`SheafOfModules.tensorClosed`),
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`),
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
  (`CategoryTheory.ShortComplex.mapHomologyIso`, cycle maps and
  `Functor.preservesHomologyOfExact`), and
  `Mathlib.CategoryTheory.Localization.Predicate`
  (`Localization.lift`, `liftNatIso`, `natTrans_ext`).
  `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization` is a plain proof
  import: its `site_one_sided_tensor_normalization` is the proof's one-sided
  tool. Each statement-dependency module is imported publicly and directly,
  including the recorded module `KFlatFixedTensorTriangulated` of the existing
  representative-data definition node.
  The exact-functor and localization nodes are Mathlib leaves with no Lean
  record, so their recorded `mathlib_match` declarations are used directly.

Edge cases checked mathematically before writing: zero `L` (all tensors zero),
unit `L=R` (ordinary unit comparison), zero or acyclic `K`, `K` unbounded in
both directions, arbitrary negative or zero `i`, identity and zero `g`, and a
noninvertible map between flat sheaves (e.g. multiplication by 2 on the
constant integers). None is excluded. On the one-point site, nonflat
`L=ℤ/2` is correctly excluded: tensoring the exact complex presenting
`ℤ/2` otherwise produces the usual extra Tor class. Empty sites and zero
ring sheaves remain allowed. Smallness uses `EssentiallySmall.{r}` rather
than an equality of universes. There is no statement dispute or missing notion.

Searches (the prescribed `msearch.py Q45 <item>` wrapper recorded its service
results in sandbox `searches.jsonl`):

* LeanFinder: “For a ringed site tensor with a flat sheaf in degree zero
  commutes with unbounded cohomology naturally in both factors”: eight hits,
  chiefly `Module.Flat.rTensor_shortComplex_exact` and related module results;
  no match for the ringed-site derived comparison with normalization.
* Loogle: `"homologyFunctorIso"`: eight hits, including the short-complex
  homology comparison and derived single-functor comparison. Reused the
  exact-functor infrastructure, but none states the full node.
* Mathlib grep via msearch: `single.*[Tt]ensor|[Tt]ensor.*single`, restricted
  to `Algebra/Homology`: three tensor-unit hits in `Monoidal.lean`; no match.
* LeanSearch: “Cohomology of unbounded derived tensor with a flat module
  sheaf on a ringed site is tensor of cohomology, naturally in both variables”:
  eight module-flatness / exactness hits, no ringed-site theorem.
* Direct `rg` of Mathlib `Algebra/Homology`, the project's `lean/Sheaf`,
  and `lean/WeilConjectures` for single/tensor and tensor/cohomology patterns
  found `mapBifunctorSingle₂Iso`, which is reused as `degreeComparison`.
  The scheme-specific finite-Tor-amplitude uses do not state this node.
* Direct `rg` for the item id and new theorem name in `lean/Sheaf` and
  `lean/WeilConjectures`, and the upstream declaration index, found no
  existing declaration of this statement.

Validation: prescribed `scompile.py` checked this file separately as a sandbox
and as `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology` against the
published server library, with no errors or warnings. The initial elaboration
required explicit source/target pairs for the derived bifunctor map and
parentheses around natural-iso types; both were repaired. The final theorem
binds its site, ring and derived universe explicitly in its displayed signature.

## Returned-delivery repair

H2 (immutable head 8227750904f5): replaced the added theorem statement dependency
`lem-weil-pbc-kflat-fixed-tensor-triangulated` by the landed definition node
`def-sf-ringed-kflat-tensor-representative-data`. Read that node's complete
statement, existing:true record and the live definitions in
`KFlatFixedTensorTriangulated`: `Modules`, `totalTensor`, `derivedTensor`
and `representativeIso` are exactly the data used here; no triangulatedness
conclusion is used. All seven original statement dependencies are retained.
Comparison with the current shared base shows only `lean` and `stmt_deps`
changed. No statement, proof plan, dependency node or declaration body changed.

H9 advisory: the seven original statement-dependency modules and the recorded
representative-data module now have direct public imports. The one-sided
normalization module is imported only for the proof plan. The theorem signature,
seven abbreviations, docstrings, and sole `sorry` proof are unchanged.

Self-check after repair: reread the node and theorem together. The explicit site
smallness, independent universes, commutative ring sheaf, exact flatness, degree-zero
K-flatness with flat terms, both-variable naturality of `a`, the cycle inclusion
and quotient normalization of `c`, simultaneous naturality of `c` and `gamma`,
the localization-factor compatibility, and every-resolution normalization retain
the clause-by-clause correspondence above. No boundedness restriction is added.
The saved packet's initial dry run passed at 1f4a6b7f9b6; that mechanical pass
did not discharge the returned citation defect, which is repaired here.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
