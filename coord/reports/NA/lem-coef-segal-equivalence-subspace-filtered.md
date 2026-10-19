## Worker report

The module `Sheaf.CategoryTheory.SegalEquivalenceSubspaceFiltered` states
`SSet.SegalEquivalenceFiltered.segal_equivalence_subspace_filtered`, with one
postponed proof, belonging to this item. All helper definitions have explicit data.
The node's natural statement, proof and proof dependencies are unchanged. Five
already-landed statement dependencies are added to expose the actual interfaces used;
there are no new nodes or dependency repairs.

The statement uses the canonical walking-isomorphism model of the requested subspace,
not a selected equivalence or an arbitrary map. The existing node
`lem-coef-segal-inverse-evaluation` states precisely
`Map_PDelta(dE,W) ≃ W_inv`, naturally by forward-edge evaluation, without completeness.
Its concrete theorem provides the path-pullback model and factorization through
`SegalInverse.invertibleArrows`, normalized by equality after its actual inclusion.
The recorded `lem-coef-segal-equivalence-classifier` identifies this for Reedy Segal
representatives, including forward-edge evaluation, both endpoints, collapse and
naturality. Thus the corepresented functor at the actual objectwise image of `dE`
is a canonical model of the node's functor `X ↦ X_eq`, including all homotopy types.
This use of the source's equivalent canonical model requires no statement correction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Nested universes and small spaces: `Spaces.infinityCategory.{u}` is the existing
  coherent nerve of all `u`-small Kan complexes, in universe `u+1`. `Presheaves` is
  only an abbreviation specializing the existing `CategoryTheory.presheafSSet`
  to `SimplexCategory` and that target. It does not construct another presheaf notion.
  The corepresented functor of this presheaf category uses the standard ambient lift
  to `u+2`, with values in `Spaces.infinityCategory.{u+1}`. The smallness test on
  `I : SSet.{u+2}` remains `IsSmall.{u,u+2}`, not smallness in the larger universe.
  Kan values remain `u`-small; use of a larger mapping-space model does not change
  the universal property, since universe inclusion of spaces preserves small colimits.
- Small spaces considered up to weak equivalence: `q` is objectwise passage to the
  recorded infinity category of spaces; `_hq : IsLocalization ... q` specifies the
  weak-homotopy-equivalence localization, rather than any unconstrained map. It is
  model-presentation data, available by the space localization/comparison nodes.
- A Segal object with consecutive-edge homotopy comparisons: `IsSegalObject q z`
  says exactly that `z` is equivalent, in the full coherent presheaf category, to
  `diagram q W` with the existing `HomotopySegal.IsHomotopySegalSpace W`. That
  predicate is levelwise Kan plus all canonical degree `n+2` comparisons to the
  path-model homotopy edge products. Equivalence-saturation allows arbitrary coherent
  simplicial spaces; no choice of a representative is made. In particular this
  imposes neither Reedy fibrancy on the supplied object nor completeness.
- `X_eq` is the union of entire invertible components, with both inverse equations:
  the existing `SegalInverse.invertibleArrows` and classifier give exactly that
  subspace. `walkingIsoObject q` is the actual objectwise image of the existing
  `SSet.SegalSpace.walkingIsomorphism`; `equivalenceSpaces q` is exactly
  `Spaces.corepresented Presheaves (walkingIsoObject q)`. Its values are the above
  canonical model of `X_eq`, not merely the set of equivalence components.
- Every map induces the specified map of subspaces: `equivalenceSpaces` is a single
  actual simplicial map on the whole coherent presheaf category. Its postcomposition
  and all higher coherence data are those of the recorded `Spaces.corepresented`.
  Forward-edge evaluation in the classifier identifies its action with restriction
  of the actual degree-one maps to the invertible components.
- Arbitrary small filtered quasicategory: `(I : SSet.{u+2}) [Quasicategory I]`,
  `_hsmall` and `_hfiltered : IsKappaFiltered Cardinal.aleph0.{u} I`.
  The filteredness predicate includes the empty test diagram, so `I` is nonempty
  for exactly the reason in the node; no additional nonemptiness binder occurs.
- Coherent diagram of Segal objects: `F : I ⟶ uliftFunctor.obj Presheaves` with
  `_hstage : ∀ i, IsSegalObject q (F.app _ i).down`. `I` is not replaced by an
  ordinary category, and its higher simplices are retained in `F`.
- The induced simplicial colimit object is Segal: `c` is a vertex of the existing
  coherent `coconeCategory F`, and `_hapex : IsSegalObject q c.1.1.down` says its
  actual apex is Segal. Its second coordinate is the entire coherent transformation
  into the constant diagram; hence the colimit operators and all compatibilities
  are those of this same simplicial-space cocone.
- Pointwise space colimit in every degree: `_hpointwise` quantifies every natural
  number `n`, including zero and one, and requires that applying the actual
  `degreeEvaluation n` to `c` gives a colimiting coherent cocone. It uses
  `Spaces.mappedCocone`, fixing both the apex and full transformation.
- The canonical comparison is an equivalence: the conclusion is precisely that
  the cocone obtained by applying `equivalenceSpaces q` to this same `c` is
  colimiting. This is the universal-property form of
  `colim_i (X_i)_eq → X_eq` being an equivalence: for any colimit presentation of
  the source diagram, its induced comparison to this cocone's apex is an
  equivalence, and conversely that comparison being an equivalence makes the
  cocone colimiting. This fixes the canonical comparison via its original cocone
  legs; it asserts more than the mere existence of unrelated equivalent objects.
  Forward-edge restriction from `dE` is natural and lands in `X_1`; the very same
  cocone and restriction therefore give the canonical comparison over `X_1`.
- The final exclusions are respected: no completeness, discreteness, nonemptiness
  of any value, monomorphism, injectivity, full-faithfulness or ordinary-index
  assumption is present. There is no added quasicategory hypothesis on the fixed
  presheaf category: its needed instance is obtained from the existing theorem
  `Spaces.infinityCategory_quasicategory` and Mathlib's internal-Hom instance
  inside the definition, not assumed from the caller.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `diagramVertex`, `evaluation`,
  `coconeCategory`, `IsColimiting`, `IsWeakHomotopyEquivalence`; their full
  definitions and docstrings were read, including the initial-object definition.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `IsSmall`, `IsKappaFiltered`.
  The latter counts nondegenerate simplices for its finite tests, including empty K.
- `Sheaf.CategoryTheory.CompleteSegalQuasicategoryComparison`:
  `complete_segal_quasicategory_comparison`, read including the full signature.
  Its complete-object comparison supplies conventions, not a completeness hypothesis
  on our stages or colimit.
- `Sheaf.CategoryTheory.HomotopySegalSpace`:
  `IsHomotopySegalSpace`, using its actual path-model comparisons.
- `Sheaf.CategoryTheory.SegalInverseEvaluation`: `segal_inverse_evaluation`,
  `invertibleArrows`, `IsInvertibleClass`, `edgeClass`, `derivedEvaluation`.
- `Sheaf.AlgebraicTopology.SegalEquivalenceClassifier`:
  `walkingIsomorphism`, `walkingArrow`, `segal_equivalence_classifier`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `infinityCategory`,
  `infinityCategory_quasicategory`, `corepresented`, `mappedCocone`.
- `Sheaf.CategoryTheory.GrothendieckPresheafCoherentStraightening`:
  `CategoryTheory.presheafSSet` (the existing entire functor object).
- `Sheaf.CategoryTheory.FiniteReedyLocalization`, exposed by the comparison import:
  `largeNerve`, `diagram`, `EquivalentObjects`, `IsLocalization`; read their full
  definitions, including `diagram` as curried objectwise evaluation.
- Proof-only import `Sheaf.CategoryTheory.SpacesKappaLimitFilteredColimit`:
  `spaces_kappa_limit_filtered_colimit` and its complete canonical-cone statement.
- Mathlib `AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct`:
  the instance `Quasicategory ((ihom A).obj X)` for arbitrary A and quasicategory X.

Edge cases checked before formalizing: all stages empty gives an empty degree-one
space and empty invertible subspace, not a point; a constant terminal Segal object
has terminal invertible-edge space; a discrete nerve of a non-groupoid is Segal but
need not be complete, and only its invertible arrows are selected; arrows may become
invertible at a later stage; a group may map to the trivial group, so no injectivity
is assumed. A genuinely empty indexing quasicategory fails the recorded filteredness
predicate at K empty, exactly as in the natural statement. Every degree, including
0, is in `_hpointwise`; no source or fiber point is required. Smallness remains in
u even when the ambient index model lives in u+2.

Searches made:

- `msearch.py leanfinder`, query "Equivalence edge subspaces of Segal spaces commute
  with filtered colimits": eight hits on strict Segal simplicial sets, strict Segal
  cores and ordinary category nerves; none is this coherent space-colimit statement.
- `msearch.py loogle`, query `"Segal", "colimit"`: zero hits.
- `msearch.py grep`, query `SegalSpace|equivalenceSubspace`: zero Mathlib hits.
- `msearch.py leansearch`, query "Equivalence edge subspaces of Segal objects commute
  with filtered colimits": eight hits concerning ordinary filtered colimits and
  finite limits, not equivalence subspaces in coherent Segal diagrams.
- `rg` in the upstream `WeilConjectures` sources and `lean/Sheaf/CategoryTheory` for
  `SegalSpace|equivalenceSubspace|equivalenceEdges|equivalence.*[Ff]iltered|IsSegal|eqSubspace`:
  upstream supplies no matching statement; project hits identified the existing
  Segal, homotopy-Segal, inverse-evaluation, Rezk and classifier interfaces reused here.
- `grep -rn` for this exact node id in upstream sources: no hits.
- `rg` for `segal_equivalence_subspace_filtered|SegalEquivalenceFiltered|equivalence.*subspace.*filtered`
  in the upstream source, side-project Lean and upstream declaration-name inventory:
  no existing declaration or namespace collision.

Source read: https://arxiv.org/html/math/9811037, especially Sections 5.3--5.8 and
Theorem 6.2, together with the project's recorded classifier and inverse-evaluation
source statements. The filtered-colimit proof remains the node's agent argument;
it is not misattributed as a theorem quoted from Rezk. The declaration docstring
carries its five steps, including the finite witness construction and the
monomorphism/whole-component argument. No STATEMENT-DISPUTED or node fault remains.

Validation: every delivered file is compiled separately through `scompile.py`; the
only postponed theorem is the item itself. No global build, direct Git mutation,
source-checkout write, or shared-library write was performed.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
