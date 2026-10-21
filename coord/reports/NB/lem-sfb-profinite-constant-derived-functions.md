## Worker report

The module `Sheaf.Paper.ProfiniteConstantDerivedFunctions` states the item in the ordinary
unbounded derived categories of the recorded internal modules. Main declaration:
`AlgebraicGeometry.ProEtale.ProfiniteFunctions.delta`. Every theorem is postponed with
`sorry`; all maps and model data are constructed. Helper declarations implement the free
parameter, evaluation, adjunction mates, continuous model and compatibility maps introduced
by this same node. They are all listed in `lean.declarations`, and have source and blueprint
docstrings. No statement, proof, dependency record or target has been corrected.

Hypothesis and clause audit (names below are in `AlgebraicGeometry.ProEtale.ProfiniteFunctions`):

* The distinct primes are `(p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)`.
  The characteristic-p field is `(k : Type u) [Field k] [CharP k p]`.
* The normed finite extension is `[NormedField E] [NormedAlgebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The choice F is `[NormedField F]
  [NormedAlgebra E F]` with `Nonempty (E ≃ₐ[E] F) ∨ IsAlgClosure E F`:
  the first disjunct is the E case up to E-algebra identification, the second the
  normed algebraic closure. There is no completeness instance on F.
* The affine k-scheme is `[IsAffine X]` and the structural morphism
  `s : X ⟶ Scheme.Spec.obj (op (CommRingCat.of k))`. The map is not required to be
  finite type or smooth. All coefficient, parameter and scheme types are in the
  common compatible universe `u`; section groups are canonically lifted to `u+1`.
* `continuousRing F` is the underlying ring object of the recorded
  `continuousMapRingSheafOfUniverse F`, with the canonical existing sheaf tensor.
  It is not a locally constant or a completed replacement. `Modules R X` uses
  `condensedRingObj R.X X`. `PointModules R` is the existing condensed internal module
  category, and `functions R P` is `(ihom (freeParameter R P)).rightDerivedFunctor`.
  Thus derivation is in the second argument on the full unbounded category, using
  the existing K-injective total right derivation. The definition of lisse is
  imported from the recorded dependency; lisseness is not an added hypothesis.
* `testScheme X P` and `projection X P` are the left object and structural map of
  `(profiniteToProEtOf X).obj P`, the recorded inverse-limit test scheme.
* `ScalarModel E F M` is literally `F ⊗[E] M`. Its topology is `moduleTopology F`,
  which in finite dimension is the finite product norm topology in any basis.
  The binder `[FiniteDimensional E M]` is retained. `constantModel` is the module
  sheafification of the explicitly constructed presheaf `Q ↦ ULift C(Q,F ⊗[E] M)`
  with pointwise action. `continuousPresheaf_isSheaf` and
  `continuousModuleUnit_isIso` state that this does not change its sections;
  `modelSection` uses the inverse of that actual unit. No arbitrary module is chosen.
* `freeParameter` uses `InternalBar.free`, with its existing free-forgetful
  adjunction, on the universe-lifted representable of P. `identityGenerator` and
  `parameterSection` are the adjunction unit at the identity and its restriction
  along the graph of the universal parameter. `parameterGenerator` is the uniquely
  specified regular-module map given by scalar multiplication by that section.
* The displayed derived isomorphism is `delta`. Its source is exactly
  `Rρ_* (p_{X[P]}^* M_F[0])`, its target exactly
  `p_X^* RHom(C_F[P],M_F[0])`. `constantModelD` is `singleFunctor ... 0`.
  `comparisonApp` is defined BEFORE its invertibility theorem: evaluate at the
  universal parameter and transpose under `projectionAdjunction`. `delta` is its
  inverse. `delta_normalization` states this evaluation-adjoint identity as a
  derived equality; in degree zero, evaluating the same free generator is the
  exponential law, not an arbitrary existence isomorphism.
* `comparison_naturality` is an equality for every derived condensed coefficient
  morphism; it includes M-linearity and all linear maps of finite-dimensional M.
  `comparison_baseChange` states the actual mate square for every pro-etale map f,
  without requiring the new base affine. `pushSquareApp` is constructed from the
  derived counit and the recorded composition isomorphisms.
* Scheme-linear maps are handled independently of point-linear maps:
  `schemeFunctions`, `derivedSliceComparison` and `sliceDelta` are normalized by
  the relative free generator and evaluation, not by conjugating with delta.
  `delta_factorization` identifies delta with this slice comparison followed by
  the inverse `pointHomIso`. `sliceDelta_family_naturality` quantifies over every
  derived X-linear u and every actual relative parameter map h; it specializes
  to the degree-zero maps between the supplied finite free constant models.
  `relativeFreeMap`, `schemeParameterMap` and `pushParameterApp` are the independently
  specified parameter maps. Taking h induced by a continuous P'→P includes ordinary
  parameter naturality. Setting h to the identity includes arbitrary X-linear
  naturality; this does not require that the linear map descend to the point.
* `familyParameterMap X Q P P' α`, where `α : Q ⨯ P' ⟶ P`, constructs the actual
  simultaneous map `X[Q][P'] → X[Q][P]` using the canonical product comparison for
  `profiniteToScheme`. `delta_wholeFamily` is an equality in the derived category
  on `X[Q]`, for arbitrary linear u on that whole scheme. No testing on individual
  Q-points replaces this equality. The categorical profinite product is the
  canonical compact topological product, and its morphisms are continuous maps.
* `coefficientInclusion E Ω` is the recorded postcomposition map for `algebraMap`.
  `scalarModelInclusion` is the actual tensor map `E ⊗ M → Ω ⊗ M`, identified with
  m↦1⊗m. `scalarConstantMap_existsUnique` characterizes the map on every continuous
  section; its construction is allowed because this formula determines it uniquely.
  `scalarConstantMapD` puts it in degree zero. `restrictHomD` is derived from the
  UNIQUE free-generator/evaluation formula `restrictHom_existsUnique`.
  `restrictPushD` uses the recorded coefficient pushforward square and derived units.
  `comparison_scalarRestriction` states their commutative square for arbitrary N;
  `comparison_scalarModel` states naturality for this exact specified module map.
  Pasting gives the E-to-Omega compatibility, and inverting delta gives the stated
  direction. Neither scalar-comparison map is asserted invertible. In particular
  no exact scalar extension or coefficient flatness is assumed.

Dependency declarations read and used:

* `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingSheafOfUniverse`,
  its underlying abelian sheaf and canonical monoid/commutative structures.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint`, `upperStarFromPointComp`, `profiniteToProEtOf`.
* Mathlib `CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, regular module and action.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and the published total derived adjunction.
* Mathlib `AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its small-site topology.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
* `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and `continuousMapRingSheafMapOfUniverse`.
* The free notion already exists as `Profinite.CondensedAction.InternalBar.free` and
  `freeAdjunction` in `Sheaf.CategoryTheory.CondensedInternalBarResolution`; reused verbatim.
* `InternalAbelianSheafModule.sheafModuleReflector`, `ordinaryAction` and
  `sectionModuleFunctor` reuse the exact internal/sectionwise transport construction.
* Existing `Functor.rightDerivedFunctor`, `rightDerivedFunctorNatTrans`, composition
  comparisons, `rightDerivedDesc` and `mapDerivedCategory` supply all derivation maps.
* `CondensedRing.comapLowerStarIso`, `coefficientMap` and `Functor.mapModComapIso`
  supply the original scalar comparisons. The known flatness-requiring derived
  pushforward isomorphism is not used; the general derived comparison is constructed.

All stated proof-dependency modules are imported privately; the already-public
`ProfinitePointPullback` is used in the statement's composition interface. The proof-only
node `lem-sfb-wcontractible-component-derived-hom` has no Lean record yet and therefore
has no module to import. It is named in the full eight-step natural-language proof in
`comparison_isIso`; none of its data is needed to write this node's statement.

Edge cases checked: P empty (both sides are the zero module), P a point (identity
comparison), M zero, X empty, arbitrary disconnected P, arbitrary finite dimension,
non-complete Omega, and Q empty or a point. The graph construction uses no chosen point
of P or Q. All-continuous sections with infinitely many values remain in the model.
The comparison and compatibility maps are constructed for arbitrary R and derived N;
the invertibility claim on the point comparison has exactly the item's arithmetic,
affineness and finite-dimensional hypotheses.

Searches: `msearch.py` LeanFinder for "Derived direct image of continuous constant module
along profinite parameter projection is derived internal Hom from free condensed module"
returned eight light-condensed ordinary Hom/solidification results, no exact statement.
Loogle `"Condensed", "ihom"` returned five ordinary light-condensed Hom results, no match.
Mathlib grep `(profinite|Profinite).*(rightDerived|derived|internalHom)` returned zero.
LeanSearch "Pullback from condensed modules commutes with derived internal Hom from free
profinite modules over continuous normed field coefficients" returned eight ordinary
sheaf pullback and LightCondensed.ihomPoints hits, no derived comparison. The exact query
and results are recorded by the wrapper in this item's logs.
`rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and derived-function,
free-profinite, point-pullback and coefficient-map names found the existing tools above,
not this theorem. Existing source signatures and docstrings were opened before use.
The source blueprint paragraph (3) of `sk-thm-sf-ctf-stability.proof.md` and the node's
complete reviewed eight-step argument were read. The old example CompactObject module
is now withdrawn and was not copied as a mathematical definition.

No STATEMENT-DISPUTED flag and no node correction.

## Second reading by NB

This dispatcher starts a single worker and explicitly forbids sub-agents. An independent
maintainer review follows delivery; no independent second-worker review is claimed here.
I reread the node and the full file clause by clause before delivery. This pass added
`delta_factorization` to connect arbitrary scheme-linear maps to the actual delta,
`familyParameterMap` and `delta_wholeFamily` to encode simultaneous Q-parameter maps,
and the continuous-model unit isomorphism to rule out altered function sections.
It also added the actual coefficient inclusion and scalar model map rather than leaving
the scalar square quantified only over unspecified maps. Exact base-change and derived
mate directions were checked against the upstream adjunction signatures. The audit above
records the correspondence for every hypothesis and clause. No independent notion or
DAG dependency repair was required.

Source verification: [HRS, Example 3.1 and Proposition 4.3(1)](https://arxiv.org/html/2305.18131)
was read directly: the all-continuous coefficient sheaf is their Example 3.1; their
Proposition 4.3(1) supplies the inner-Hom comparison on a w-contractible affine basis.
Compilation through scompile.py succeeded against current server sources in 47.9 seconds,
within the unchanged 60-second limit, with no errors or non-sorry warnings.

Elaboration caching: `condensedSheafMonoidal` and `schemeSheafMonoidal` are named
specializations of the published canonical instances (`inferInstance` as their entire
bodies). They introduce no alternative tensor; naming these avoids repeated synthesis
of the large presheaf enriched-Hom diagrams in the compatibility declarations. Temporary
profiling options were removed.
