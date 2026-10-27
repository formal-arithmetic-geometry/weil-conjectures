## Worker report

The module `Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams` states
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplax.section_resolving_oplax_constraint_diagrams`.
There is exactly one `sorry`, its proof. The other thirty-minus-one declarations are
transparent aliases, concrete comparison composites, or explicit proposition definitions
belonging to this diagram statement. No new independent notion or dependency repair is needed.
The node statement and its accepted split remain unchanged.

Source read: Stacks `sites-cohomology.tex`, `lemma-pullback-K-flat` (0G7E),
`lemma-pullback-tensor-product` (07A4), including the resolution and total-tensor
construction in the proofs. The precise six-vertex equations are the agent refinement
in this node's twelve proof steps, rather than a purported verbatim Stacks assertion.
I read those steps and the accepted stage-1 review. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/_section.md`
is the Verdier-exchange unit; this helper is not the unit's statement.

Hypotheses and clauses, matched individually:

- A commutative condensed ring is the explicit sheaf `Λ` on `coherentTopology Profinite`
  with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled input of the recorded
  coefficient-ring framework and admits arbitrary condensed rings.
- A scheme is `Scheme.{u}`; `modules Λ T`, `ring Λ T`, `internalModules Λ T`,
  `equivalence Λ T` and `derivedEquivalence Λ T` are the fixed existing constructions.
  In particular the site is `T.ProEt`, with object universe `u+1`, morphism universe
  `u`, and module/coefficient universe `u+1`. No equality of those universes is imposed.
  `[∀ T, HasDerivedCategory.{u+1} (modules Λ T)]` is the existing size convention.
- The internal and section localizations are the existing `DerivedCategory.Q` and
  `Qh` (the former is their composite with the homotopy quotient). The termwise
  section equivalence and its fixed localization factors are reused.
- Resolving means exactly `KFlatSectionComparison.sectionResolving`, namely
  `TensorFlatRepresentative`, the existing independent-coefficient K-flat predicate
  conjoined with `IsFlatOnSite` in every degree. No boundedness restriction occurs.
- `⊗` on cochain complexes is the existing signed direct-sum total over all integer
  degrees, exported by `SectionTotalOplaxComparisonData`. Its associator `α_` is
  unsigned reassociation, not a permutation. `obj` and `map` merely expose the fixed
  conjugate section derived tensor `tensor Λ T` and its action on morphisms.
- `f : X ⟶ Y`, `totalSectionPull Λ f`, `derivedPullback Λ f` are the stipulated
  ordinary and derived pullbacks. `resolution` is exactly the inverse of the existing
  `mapDerivedCategoryFactors` epsilon isomorphism, not another resolution choice.
- `representative` is the inverse of the prescribed `qTensor` on resolving pairs,
  using `tensor_representatives.exists.choose_spec` for invertibility. This is the
  fixed section realization of the ringed model comparison, identified with its
  independent native tensor by the recorded `section_kflat_tensor_comparison`.
  It does not select an arbitrary isomorphism.
- `sectionTotalIso` and `sectionTotalUnit` are the fixed ordinary b and u. The input
  `μ` is a natural transformation of the exact bifunctors in the statement; `v` has
  the stated regular-unit source and target. There is no assumed oplax structure.
- `hμ : PairNormalization` is literally the displayed equation, with Lean's
  left-to-right composition: mu, epsilon tensor epsilon, then r_X inverse equals
  LF(r_Y inverse), epsilon of total, then q(b). It is required on every resolving
  pair and only those pairs. `hv` is epsilon of U followed by q(u).
- The first conclusion existentially supplies the closure evidence `hPQ`, `hQH`,
  `hFP`, `hFQ`, `hFH`, `hFPQ`, `hFQH` and the two target pair totals. It explicitly
  asserts both nested source totals and their pullbacks are resolving. Closure is
  a conclusion, never an extra assumption on the theorem.
- `nestedLeft`, `nestedRight` are the nested r composites ell and varrho;
  `pair` is d = J followed by LF(r). `vertex0` through `vertex5` are exactly
  C0 through C5 of proof Step 4. `AssociativityDiagram` asserts each is invertible,
  all six edge squares, both whole-path squares with common outside comparisons,
  and equality of the two derived paths. A square `C_i ≫ D = q(edge) ≫ C_j`
  with these invertible C's is exactly `C_i ≫ D ≫ C_j⁻¹ = q(edge)`.
  Thus the incoming comparison is the inverse of the same fixed outgoing one.
- The cochain paths inside those whole-path squares are explicitly
  `F.map α ≫ b(P,Q⊗H) ≫ (FP ◁ b(Q,H))` and
  `b(P⊗Q,H) ≫ (b(P,Q) ▷ FH) ≫ α(FP,FQ,FH)`, respectively. The commutativity
  clause is included, rather than leaving it to informal interpretation.
- The unit conclusion supplies resolving evidence for U, V and FU, and for FP.
  `regularUnit` is exactly kappa followed by the localized ordinary unit comparison.
  `leftUnit` and `rightUnit` are the fixed transported derived unitors expressed
  using that regular-unit identification.
- `leftUnitDiagram` and `rightUnitDiagram` each assert the four fixed vertex maps
  invertible, their three edge squares, the direct unitor branch, the whole cochain
  branch and the derived commutativity equation. Their cochain maps are exactly
  `b ≫ (u ▷ FP) ≫ λ` and `b ≫ (FP ◁ u) ≫ ρ`, with direct branches `F.map λ`
  and `F.map ρ`. The specified v is used at the middle edge.
- `Conjugation` is the final conditional hypothesis written verbatim as composites
  of the fixed gamma (`derivedPullComparison`), theta (`tensorComparison`) and e
  (`regularUnit`). It quantifies over an internal natural transformation `μi` and
  unit `vi`, with no internal coherence assumption.
- `InternalAssociativity` gives every internal-to-section edge square and both
  complete path squares under their explicitly nested gamma/theta vertex maps.
  `InternalLeftUnit` and `InternalRightUnit` give the corresponding four vertex
  comparisons, all three edges, direct branch and complete branch, using gamma,
  theta, and e. This is an identification of specified diagrams, not merely their
  abstract commutativity. Quantifying over all internal derived objects also
  includes all internal resolving representatives and their section images.

Dependency declarations read and used (the owning modules are imported directly or
publicly through the stated dependency interfaces):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, whose
  unbundled sheaf/ring-object encoding is used for Λ.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj` and commutativity preservation.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence` and reconstructed section ring.
- `Sheaf.Paper.SectionModuleOperationsData`: `ring`, `modules`, `internalModules`,
  `equivalence`, `pullback` and its canonical operation comparison.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `Qh`.
- `Mathlib.Algebra.Homology.BifunctorShift`: the existing signed `mapBifunctor`;
  the cochain monoidal structure is that same signed total.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its Tensor
  import: the internal relative derived tensor on module objects.
- `Sheaf.Paper.SectionDerivedRealization`: `qTensor`, `tensor_representatives`,
  `derivedPullComparison`; its tensor-data import provides `tensor`, `tensorUnit`,
  `derivedPullback`, `derivedEquivalence`, `sectionLocalizationComparison`.
- `Sheaf.Paper.SectionDerivedPushpullNormalization`:
  `sectionDerivedPushpullNormalization`, the fixed gamma resolution normalization.
- `Sheaf.Paper.SectionKFlatTensorComparison`: `sectionResolving`,
  `section_kflat_tensor_comparison`, the fixed representative/unit normalization.
- `Sheaf.Paper.SectionOplaxTotalComparison`: `section_oplax_total_comparison` and
  its data import's `sectionTotalIso`, `sectionTotalUnit`, `totalUnitComparison`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients`; `tensorDescentPair` and
  `TensorFlatRepresentative` in the publicly imported `SiteDerivedTensorRestriction`
  identify the native model used by `SectionKFlatTensorComparison`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- Proof-only imports also retain `KFlatTotalTensorModel.kFlat_total_tensor_model`,
  `SheafOfModules.isKFlat_ringedToposPullback`, and
  `CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation`
  from the current recorded module `DerivedPullbackRepresentativeComputation`.

Edge cases checked before and during writing: zero complexes and the zero ring do
not change any comparison types; the identity scheme morphism leaves the prescribed
factor maps rather than assuming they are definitionally identities; the unit is
regular in degree zero, not an arbitrary chosen object. Every complex is indexed by
all of ℤ, including arbitrarily unbounded complexes and infinite degreewise sums.
There are no finiteness or nonemptiness restrictions. No factor identifies the site
object and morphism universes. The two associators only rebracket homogeneous triples,
so no Koszul permutation sign is introduced.

Searches actually run:

- `msearch.py ... leanfinder "Derived oplax monoidal coherence diagrams identified on K-flat resolving complexes via localization tensor and pullback comparisons"`:
  eight hits, including Tor and `Localization.Monoidal.tensorBifunctorIso`; none
  gives the prescribed section pullback six-vertex computation.
- `msearch.py ... loogle "Functor.OplaxMonoidal, Functor.mapDerivedCategoryFactors"`:
  zero hits, unknown identifier `Functor.OplaxMonoidal` in that service.
- `msearch.py ... grep "oplax.*(coherence|associat)|resolving.*diagram" CategoryTheory`:
  nineteen hits, generic oplax axioms and multifunctor diagrams, not this statement.
- `msearch.py ... leansearch "Derived pullback oplax associativity and unit diagrams computed on K-flat total tensor representatives"`:
  eight hits, mostly categorical pullback associativity, plus generic oplax composition;
  none states the required prescribed-map result.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for resolving/oplax constraint
  diagrams and the exact node id: no matching theorem. Read the generic upstream
  left-derived monoidal interface and existing ordinary section comparison; they
  supply maps, not this derived diagram identification. The related scalar-extension
  oplax axioms do not identify these gamma/theta/epsilon/r vertices.

Compilation: `scompile.py Q23 lem-pd-section-resolving-oplax-constraint-diagrams ...`
passed sandbox mode (58.8 s) and library mode (55.4 s), no errors or warnings.
`set_option linter.all false`, as in the imported normalization module, avoids
expensive whole-file linting near the fixed limit. The actual source still has
explicit binders (`autoImplicit false`), source docstrings on all declarations,
no lines above 100 columns, and a single theorem with a `sorry` proof. Comparison
opacity during elaboration prevents unfolding the large fixed constructions.

No STATEMENT-DISPUTED finding and no statement correction.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
