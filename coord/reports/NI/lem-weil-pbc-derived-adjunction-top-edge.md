## Worker report

Item: `lem-weil-pbc-derived-adjunction-top-edge`.
Module: `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge`.
Main declaration: `AlgebraicGeometry.derivedAdjunction_topEdge`.

The statement specifies the canonical edge by its sheafification equation, and states
that its composite with cohomology of the derived adjunct is the ordinary adjunct of
the normalized top-cohomology map. Its only postponed theorem is the main declaration,
with proof `sorry`. All nine helper definitions have real data. There are no new DAG
nodes, dependency-record repairs, statement corrections, or disputed statements.

Hypotheses and clauses, matched against the node:

- A scheme morphism g:T→S is `{T S : Scheme.{u}} (g : T ⟶ S)`.
- The shared module derived categories are `schemeDerivedCategory S` and
  `schemeDerivedCategory T`, with the same family of
  `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))` binders as
  the recorded top-cohomology comparison and pinned adjunction. This fixes the
  localization sizes and does not assume a geometric property of any scheme.
- The integer q is `(q : ℤ)`; negative degrees are included.
- C is `(C : schemeDerivedCategory S)`, with `(hC : C.IsLE q)` for the vanishing
  H^i(C)=0 for i>q. This is the recorded standard t-structure, not termwise vanishing
  of a specified complex and not a lower cohomological bound.
- K is `(K : schemeDerivedCategory T)`. The node's D+ hypothesis is
  `(_hK : ∃ n : ℤ, K.IsGE n)`; the bound is arbitrary and need not be q.
- Derived pullback is `derivedPullback g`; direct image is
  `schemeDerivedDirectImage g`. Their chosen adjunction is
  `pinnedDerivedAdjunction`, supplied with the published
  `Scheme.Modules.canonicalTensorPullbackAdditive` proofs. This is the adjunction
  fixed by `canonicalSingleAdjunctionTranspose`, with the composition-pinned counit.
  No additional adjunction is quantified over or chosen by an unconstrained existence.
- κ is the dependency's `derivedPullbackTopCohomology g q C hC`.
  `topEdgePullbackInverse` takes its inverse using precisely the IsIso conclusion of
  `derivedPullback_topCohomology`; no extra invertibility hypothesis appears.
- Ordinary pullback is `Scheme.Modules.tensorPullback g`, through the target of κ.
  Ordinary direct image is `Scheme.Modules.pushforward g`. The ordinary transpose
  uses `Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)`, whose
  unit is pinned to the section formula in the recorded dependency.
- Θ for every derived object on every scheme is the ringed-space helper
  `RingedSpace.topEdgeLocalClass X q K`. It is exactly the abelian sheafification
  unit followed by `localHypercohomologySheafificationAt q K`. That existing
  isomorphism has its explicit K-injective normalization. All its components are
  presheaf natural transformations, so restrictions are included.
- λ is `RingedSpace.topEdgeLocalLeray`. The direct-image theorem records the inverse
  direction of λ; this helper uses its inverse. Its domain is transported from
  the theorem's `sectionDerivedDirectImage` to the shared
  `derivedModuleDirectImage` by `topEdgeDirectImageComparison`. Both functors are
  compared using their actual derived units on the same K-injective representative,
  via `rightDerivedFunctorOfQuasiIsoResolutionsObjIso` and
  `rightDerivedFunctorObjQIso`. This is a construction, not an assumed comparison.
- Θ on g-inverse-image opens is `topEdgeInverseLocalClass`. The inverse-open
  hypercohomology presheaf is computed on that same representative using
  `topEdgeInverseModel`. Exact precomposition by `(Opens.map g.hom.base).op`
  commutes with homology. `topEdgeLocalModel.inv` then returns to the existing local
  hypercohomology presheaf of K, where `topEdgeLocalClass` applies. The resulting
  target is the underlying abelian presheaf of the module direct image of H^q(K),
  retaining its actual g-sharp scalar restriction.
- The edge e has type H^q(Rg_*K)→g_*H^q(K) in module sheaves. It is quantified by
  `∃! e`, with the first conjunct its universal sheafification equation at every
  `V : (Opens S)ᵒᵖ`. The equation reads Θ_RgK followed by sections of e equals λ
  followed by Θ on the inverse-image open. Quantifying all opposite opens includes
  all opens, including the empty open. Writing the equation after forgetting to
  abelian groups loses no linearity: e itself is a module-sheaf morphism. Uniqueness
  expresses the sheafification universal property implicit in the node's definition
  of e, rather than an additional mathematical restriction.
- Every derived arrow is `∀ d : (derivedPullback g).obj C ⟶ K`. Its α is written
  directly as `(pinnedDerivedAdjunction g).homEquiv C K d`. This is equivalent to
  binding α together with the equation identifying it as d's unique adjunct.
- The second conjunct states exactly
  `ordinary.homEquiv (κ⁻¹ ≫ H^q(d)) = H^q(derived.homEquiv d) ≫ e`.
  Lean composition order is left to right, so these are the two composites in the
  node, with no reversed arrows or strengthened conclusions.

Helpers `topEdgeResolution` and `topEdgeResolutionIso` merely choose a complex
representative of a derived object, apply the published functorial K-injective
resolution, and identify it with that derived object by the actual quasi-isomorphism.
They neither choose mathematical data from a non-unique mere-existence theorem nor
introduce another definition of derived direct image, local sections, or cohomology.
The only choice from a postponed theorem in a helper is the presheaf isomorphism of
`unboundedDirectImage_sectionPresheaf`: its hom is specified to equal
`localHypercohomologyComparison`, which determines the isomorphism uniquely.

Statement dependencies read and used (module, declaration):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` on the shared SheafOfModules carrier.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, its canonical transported construction and spec.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`:
  `AlgebraicGeometry.Scheme.Modules.canonicalSingleAdjunctionTranspose`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology`:
  `AlgebraicGeometry.derivedPullbackTopCohomology`, `derivedPullback_topCohomology`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction`.
- `WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology`:
  `AlgebraicGeometry.RingedSpace.sheafification_cohomology` (the local-class theorem),
  with the fixed normalized comparison supplied by the next dependency.
- `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf`:
  `AlgebraicGeometry.RingedSpace.localHypercohomologyPresheaf`,
  `localHypercohomologySheafificationAt`, `localHypercohomologyComparison`,
  `unboundedDirectImage_sectionPresheaf`, and their resolution interfaces.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`. The equation is
  written on underlying abelian presheaves; the existing
  `sheafificationCompToSheaf` identifies this with module sheafification.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, `DerivedCategory.IsGE`.

The proof docstring follows all eight DAG proof steps, including the cocycle
normalization, the two Hom factorizations with the correct variance, the role of
shifted full faithfulness, the single transpose with the pinned shifts, and the final
naturality calculation. Recorded proof modules are imported, including
`CanonicalSingleDirectImageComparison`, `TruncationsAndHomotopyColimits`,
`PinnedDerivedAdjunctionShifts`, `DerivedAdjoint`, and the Mathlib truncation and
fully-faithful interfaces. Counit shifts, triangle Hom exactness, orthogonality and
the abstract derived category are available through their public dependency imports.

Edge cases checked before and after writing:

- g=id: both derived-unit model comparisons identify the same resolution, and the
  local formula reduces to the identity edge, consistent with the identity adjunct.
- q=0 and q<0: all constructions use integer cochain homology, with no Nat conversion.
- C=0, K=0, or H^q(C)=0: the displayed composites are the unique maps from/to the
  relevant zero objects; no nonzero or positive-rank condition was introduced.
- Empty opens and empty schemes: the natural-transformation formulation includes
  them and assumes no points, nonempty covers, affine covers or sections exist.
- K with cohomology below q is included: D+ is an existential lower bound, not IsGE q.
- C can be unbounded below, and g can be non-flat. No coherence, quasi-coherence,
  finite-rank, properness or flatness assumption appears.
- Independent localization universe w is retained; no equality with u is imposed.

Searches actually run:

- `msearch.py ... leanfinder` with "Derived adjunction induces ordinary pullback
  pushforward adjunction on top cohomology via cohomology direct image edge": eight
  ordinary sheaf/module adjunction hits, no matching normalized top-cohomology theorem.
- `msearch.py ... loogle` with `"Adjunction", "homology"`: zero hits.
- `msearch.py ... leansearch` with "Top cohomology of derived adjoint morphisms are
  ordinary adjoints via the direct image local cohomology edge": eight hits, chiefly
  `Adjunction.derived`, `derived'`, their unit/counit results and ordinary adjunctions;
  none states the edge equation in this node.
- `msearch.py ... grep 'homologyComparison|mapHomology|homologyMap' Algebra/Homology`:
  25 hits on generic homology maps and preservation, no statement of this item.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the item id and candidate
  names `derivedAdjunction_topEdge`, `derivedAdjunctionTop`: no existing declaration.
- Additional `rg` on both project trees for local-class, top-edge, and
  adjunction/homology combinations found other étale comparison/edge statements and
  the dependency modules, but no equality with this module-sheaf local-class edge.
- Source searches located `rightDerivedFunctorObjQIso`,
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`, and
  `mapHomologicalComplexHomologyIso`; the definitions use those existing constructions.

Sources read: Stacks `cohomology.tex`, labels
`lemma-sheafification-cohomology`, `lemma-Leray-unbounded`, and
`lemma-unbounded-describe-higher-direct-images`, with the complete DAG statement and
eight proof steps. The supplied example `CompactObject.lean` has been withdrawn;
its node now records the identical upstream definition. Current dependency modules
provide the header and public-module conventions used here.

Validation: `scompile.py NI lem-weil-pbc-derived-adjunction-top-edge <file>` passed
both the sandbox check (52.4 s) and the library-name check (26.1 s), with no errors or
unexpected warnings. Earlier elaboration errors (missing public import, namespace,
and a field-projection line break) were repaired. An intermediate old-file compile
timed out; the corrected final file passed the unchanged 60-second limit.

## Second reading by NI

This is the author's second pass, not a claim of independent review: the dispatcher
brief reserves independent review to the maintainer and prohibits spawning agents.
I reopened the node and final module together. The clause mapping above was checked
against the final theorem signature. In particular, the first conjunct fixes e by
Θλ rather than asserting an arbitrary map, the target and source of κ⁻¹ are correct,
the ordinary adjunction uses tensor pullback, and the derived adjunction is the pinned
one. I checked that the resolution comparisons use actual units in both models, that
λ has the node's direction, and that all local maps land on inverse-image opens.
All helper declarations have source/blueprint docstrings and real definitions. The
only `sorry` is the main theorem, whose docstring includes every proof step. No
mathematical mismatch or node correction was found in this second pass.
