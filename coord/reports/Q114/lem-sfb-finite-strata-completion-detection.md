## Worker report

The module `Sheaf.Paper.FiniteStrataCompletionDetection` states
`AlgebraicGeometry.ProEtale.FiniteStrataCompletion.finite_strata_completion_detection`.
Its only postponed proof is this theorem. All five helpers have actual definitions.
The accepted stage-1 statement and proof are unchanged. The previous worker's refusal
was a stage-1 unchanged-item check; the current brief's stage-handoff paragraph authorizes
this stage-2 binding. No repair note exists for this item.

Hypotheses and clauses, matched to Lean:

* The prime is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`.
  `DerivedNakayama.integerRing l E` uses the actual valuation ring, its spectral
  norm topology and the recorded chosen uniformizer. No discrete replacement of A
  is made. `AdicCompletion.Modules l E T` is the ordinary internal-module category
  over its pullback to the small pro-etale site, not a completed category.
* Explicit universe `u` gives schemes in `Scheme.{u}`, sites with object universe
  `u+1` and morphism universe `u`, and abelian coefficient groups in `u+1`.
  This is the recorded size convention, without equating site universes.
* `W` has `[CompactSpace W] [QuasiSeparatedSpace W]`, exactly qcqs.
  `S : Scheme.FiniteLocallyClosedStratification W` records a finite disjoint covering
  partition, actual schemes, their immersions and their images. `_hc` requires each
  image `S.stratum a` to be constructible. There is no reducedness assumption.
* `𝒰 a : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a)` is the specified
  pro-etale cover on each stratum. The full precoverage includes its fpqc finite
  quasi-compact refinement condition. Cover members need not be qcqs, and the cover
  index need not be finite or nonempty.
* `pull l E` is the exact levelwise functor `(CondensedRing.upperStar Λ f).mapDerivedCategory`.
  The recorded derived-pullback module publicly supplies
  `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`, identifying it with the
  total left derived pullback. The original-cover expression is iterated, first by
  `S.immersion a` and then by `(𝒰 a).f i`, exactly `K_{a i}`.
* The first equivalence uses the recorded `IsDerivedComplete` predicate on both
  sides. Its definition tests the actual strict augmentation on a K-flat representative.
  `AdicCompletion.completionMap`, `isDerivedComplete_iff` and
  `CompletionTriangle.completion_triangle_comparison` identify this with invertibility
  of precisely the specified unit to the strict derived reduction limit. No arbitrary
  morphism or uncharacterized isomorphism between completion objects is substituted.
  Positive exponent n is indexed by n-1 in this published API.
* The second equivalence is `∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor _ q).obj K)
  ↔ ...`, for every integer separately. `K` is an arbitrary unbounded derived object.
* The existential `tree : Scheme.SchemeRefinementTree W ... W (𝟙 W)` is a genuinely
  finite inductive binary tree rooted at W. Each constructor records qcqs vertices,
  immersion branch morphisms, quasi-compact open and closed child edges, and disjoint
  complementary covering images. The allowed-split predicate is `True` because this
  item imposes no extra selected-immersion condition on those splits. It is a parameter
  of an existing construction, not an additional vacuous theorem hypothesis.
  The constructors imply that the nonempty leaf images partition W.
* The first `AllLeaves` clause supplies `a` and an actual morphism
  `t : L ⟶ S.domain a` with `t ≫ S.immersion a = branch` for each nonempty leaf.
  `leafCover` is `(𝒰 a).pullback₂ t`, the actual family
  `U_{a i} ×_{S_a} L → L`, retaining its cover certificate. There is no arbitrary
  replacement cover. `leafCoverTest` tests all such factors, which are unique when
  they exist because stratum immersions are monomorphisms and distinct strata are disjoint.
* `leafScalarModels` quantifies each original-cover scalar model, with P an ordinary
  scalar module encoded as `Mod Ab (scalarRingObj Λ)` and `Mod.IsFinitelyPresented`.
  `finiteConstantScalarExtension Λ T` is exactly `B_T ⊗_{A_T} P_T`.
  Its conclusion reuses that same P on the leaf-cover member. For every scalar
  finite presentation of P, the two cokernel models use the identical matrix `A`,
  source size m and target size n, through the recorded `scalarMatrix` construction.
  Matrices are not merely existentially replaced by other presentations. These local
  implications apply separately to every original-cover member, and hence simultaneously
  to any full family of the given scalar models; no global scalar-model hypothesis
  is needed for the completion or cohomology equivalences.
* The subsequent two equivalences test completion and degree-q zero objects by
  `tree.AllLeaves (leafCoverTest ...)`, using the actual branch-cover morphisms to W.
* `completionCone l E W P` is `Q.obj (mappingCone (AdicCompletion.augmentation ... P))`.
  The final clause, for every K-flat P, detects its zero object by those same leaf-cover
  restrictions. This is the cone of the actual unit, rather than a cone of a chosen map.
  Every K has such a representative, and the recorded augmented comparison transports
  this cone to the unit's cone at K.
* `IsEmpty L → ∀ M, IsZero M` explicitly gives the zero module category on empty
  leaves. An empty leaf's restrictions are therefore zero and its completion tests
  automatic; no nonemptiness premise or test is imposed on them. No original stratum
  is assumed globally open, and no Noetherianity, boundedness or ell-invertibility
  assumption occurs anywhere in the theorem.

Dependency declarations used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the publicly imported valuation-ring,
  norm-topology and chosen-uniformizer constructions.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, and its public upstream exact levelwise
  comparison `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`.
* `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  `AdicCompletion.Modules`, `AdicCompletion.augmentation`,
  `AdicCompletion.completionMap`, `AdicCompletion.isDerivedComplete_iff`,
  `IsDerivedComplete`.
* `Sheaf.Paper.CompletionTriangleComparison`:
  `CompletionTriangle.completion_triangle_comparison` (the actual augmented comparison).
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `Scheme.FiniteLocallyClosedStratification`, including its scheme realizations.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  the recorded finite constant local-model framework, publicly retained by the
  scalar-extension module. The stronger finite-presentation interface below is used
  for the statement's given scalar modules and matrices.
* `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `scalarRingObj`, `finiteConstantScalarExtension`, `scalarMatrix`, and the proof's
  `finiteConstantLocalModelOnCover_iff_scalarMatrix`.
* `Sheaf.SixFunctors.SchemeRefinementTree`:
  `Scheme.SchemeRefinementTree` and `SchemeRefinementTree.AllLeaves`.
  The last two existing nodes are added to `stmt_deps`, as authorized for landed notions.
  No new node or dependency repair is needed.

All already recorded proof-dependency modules are imported privately, with the
Mathlib leaves imported from their recorded files. The module docstring gives all
eight accepted proof steps, including product preservation and the unit's zero second
coordinate. No proof dependency was removed or replaced.

Edge cases checked before writing: empty W, the empty partition, empty individual
strata, empty covers on empty strata, empty leaves and the root-only tree; zero P,
zero-rank source or target matrices; arbitrary unbounded K and all positive or negative
cohomological degrees; ell not invertible on W; constructible partitions with no globally
open original stratum. Finite induction is on the supplied refinement tree, not on
Noetherian dimension or an assumed ordering of the original strata.

Searches for existing declarations:

* `msearch.py leanfinder`, query "Derived completeness and cohomology vanishing detected
  on pro etale covers of a finite constructible stratification of a qcqs scheme":
  eight hits on scheme sites and affine transition limits, none stating this result.
* `msearch.py loogle`, query `IsDerivedComplete, Stratification`: zero hits,
  unknown identifier `IsDerivedComplete` in the search service.
* `msearch.py grep`, query `completion.*strat|strat.*completion|IsDerivedComplete`:
  zero Mathlib hits. The retained earlier searches likewise found no Mathlib match.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `completion.*strat|strat.*completion|FiniteStrataCompletion`: no exact statement.
  The older `StratumCompletionUnitRestriction` and `AdicStratumCompletionUnit`
  interfaces use different coefficient/completion data or additional Noetherian
  hypotheses; they do not state this arbitrary-qcqs continuous-coefficient result.
* `rg` for `RefinementTree|BinaryTree` found the existing
  `Scheme.SchemeRefinementTree`; its full constructors and `AllLeaves` were read
  and reused. Searches of the existing scalar-model node and its module found the
  exact ordinary scalar extension and scalar matrix constructions, reused here.

Validation: `scompile.py Q114 lem-sfb-finite-strata-completion-detection` compiled
both the sandbox module and the delivered library path cleanly (15.6 s / 11.0 s).
The initial parser error was repaired by opening the existing monoidal namespace;
there are no remaining errors or warnings. No live repository files were edited.

## Second reading by Q114

Final self-check only; the dispatch forbids starting another agent and assigns the
independent reading to the maintainer. Re-read the unchanged node against the module.
Both original-cover equivalences are present; tree leaves have actual scheme morphisms,
actual base-changed covers, the same scalar P and matrices, and degreewise tests.
The strict augmentation and its cone are reused by name. Empty and zero-rank cases
are included. The code has explicit universes and `autoImplicit false`, no local
notation or private declaration, and only the one theorem has `sorry`.
