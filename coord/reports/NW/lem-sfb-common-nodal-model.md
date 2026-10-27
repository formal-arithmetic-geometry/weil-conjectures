## Worker report

The new module `Sheaf.AlgebraicGeometry.CommonMarkedNodalModel` states
`AlgebraicGeometry.exists_common_marked_nodal_model`. Its only theorem proof is `sorry`.
There are no new definitions, new DAG nodes, dependency repairs or statement corrections.
The original node statement, proof and dependencies remain unchanged.

The marked nodal family terminology is rendered by its constituent hypotheses, using the
same `HasNodalGeometricFibres`, `IsReduced` and `Scheme.IsPureDimension` conditions as
`exists_nodal_log_canonical_reconstruction`. No relative dualizing data or positivity
hypothesis is needed. `Over` bundles a scheme with its specified structure morphism; its
morphisms are exactly morphisms commuting with those structure maps.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| DVR R | `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| K its fraction field | `[Field K] [Algebra R K] [IsFractionRing R K]` |
| S = Spec R and two S-schemes | `X₁ X₂ : Over (Spec (.of R))` |
| Projective, in the blueprint convention | `[IsHProjective X₁.hom] [IsHProjective X₂.hom]` |
| Flat | `[Flat X₁.hom] [Flat X₂.hom]` |
| Finitely presented | `[LocallyOfFinitePresentation Xᵢ.hom]`; H-projectivity gives properness and hence quasi-compactness and quasi-separatedness, so this is full finite presentation |
| Nonempty connected geometric fibres | `hnodal₁`, `hnodal₂`, through `ConnectedSpace` in the existing `HasNodalGeometricFibres` |
| Reduced, pure one-dimensional geometric fibres | `hgeometric₁`, `hgeometric₂`, quantifying over every algebraically closed `Ω : Type u` and every map `Spec Ω → Spec R` |
| Only ordinary double points | `hnodal₁`, `hnodal₂`: the existing predicate requires the completed local ring at each nonsmooth point to be `Ω[[x,y]]/(xy)` |
| n pairwise disjoint sections | `n : ℕ`, `a₁`, `a₂` indexed by `Fin n`, section equations `ha₁`, `ha₂`, and pairwise disjoint image sets `hdisjoint₁`, `hdisjoint₂` |
| Sections in relative smooth locus | `hsmooth₁`, `hsmooth₂` quantify over each section index and each base point |
| Permutation of markings | `σ : Equiv.Perm (Fin n)` |
| K-isomorphism u | `uK` is an isomorphism of objects over `Spec K`, obtained by the canonical `Over.pullback` along `Spec.map (algebraMap R K)` |
| u carries a₁j,K to a₂σ(j),K | `hmark` uses the existing canonical `sectionBaseChange`, and `uK.hom.left` |
| Common marked nodal family | Existential `Y : Over (Spec R)` with `IsHProjective`, `Flat`, `LocallyOfFinitePresentation`, existing `HasNodalGeometricFibres`, and reduced pure one-dimensional geometric fibres |
| Disjoint smooth sections b | Existential `b`, its section equations, pairwise disjoint images, and the smooth-locus condition |
| Proper S-morphisms pᵢ | `p₁ : Y ⟶ X₁`, `p₂ : Y ⟶ X₂` in `Over`, and `IsProper p₁.left`, `IsProper p₂.left` |
| Finite sets Zᵢ of closed special-fibre points | Existential `Zᵢ : Set Xᵢ.left`, `Zᵢ.Finite`, closed singletons, and `Xᵢ.hom z = IsLocalRing.closedPoint R` |
| Isomorphism off Zᵢ | An open `Vᵢ` with underlying set `Zᵢᶜ` and `IsIso (pullback.snd pᵢ.left Vᵢ.ι)`, exactly the restriction of pᵢ over Vᵢ |
| p₂,K = u composed with p₁,K | The equation between the underlying maps of `(Over.pullback ...).map p₂` and `(Over.pullback ...).map p₁ ≫ uK.hom` |
| p₁ bⱼ = a₁ⱼ | `∀ j, b j ≫ p₁.left = a₁ j` |
| p₂ bⱼ = a₂σ(j) | `∀ j, b j ≫ p₂.left = a₂ (σ j)` |
| Both generic maps are isomorphisms | Final two `IsIso` conjuncts on the canonical base-changed maps |
| No extra assumptions and n=0 allowed | No generic smoothness, stability, positivity, completeness, excellence or base extension hypothesis; no `Nonempty (Fin n)` hypothesis |

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`; `Mathlib.RingTheory.Localization.FractionRing`
  gives the standard fraction-field interface `IsFractionRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, the recorded finite projective-space convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction`:
  `AlgebraicGeometry.exists_nodal_log_canonical_reconstruction`, read for its family hypotheses.
  Its public interfaces include the existing `HasNodalGeometricFibres` from
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres` and `Scheme.IsPureDimension` from
  `Sheaf.AlgebraicGeometry.PureDimension`. The theorem here does not invoke its reconstruction
  conclusion: it uses exactly that node's marked-family terminology without positivity.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and its public dependency
  `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `AlgebraicGeometry.sectionBaseChange`,
  the already constructed canonical induced section; no replacement construction.
- Proof-only imports cover the recorded projective-properness theorem,
  `Mathlib.AlgebraicGeometry.ValuativeCriterion` (`IsProper.eq_valuativeCriterion`),
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`
  (`ext_of_isSchemeTheoreticallyDominant_of_isSeparated`), and
  `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel`
  (`exists_etale_nodal_local_model`). `IsProper.of_comp` and
  `IsClosedImmersion.of_comp` are available through the imported Mathlib modules.
  The other proof dependencies have no recorded Lean declaration yet; no module is invented
  for a proof-only prerequisite. The docstring preserves all ten proof steps and their uses.

Sources read: `literature/stacks-project/resolve.tex`, lemma-birational-regular-surfaces
(Tag 0C5S), and `literature/stacks-project/models.tex`, lemma-blowup-at-worst-nodal
(Tag 0CDE). As the node itself says, the combined conductor-and-marking result is an
agent extension of those constructions, not a verbatim assertion of either tag. The source
limitation is preserved explicitly in the module and declaration docstrings.

Edge cases checked before drafting:

- `n=0`: `Fin 0` is empty, all section conditions are vacuous, and its permutation exists.
- Empty intermediate normalization or empty conductor is allowed by the proof; the statement
  does not ask those intermediate schemes to be connected. The families themselves must
  have nonempty connected geometric fibres, as required.
- Singular generic fibres and nonsplit nodes are allowed by the nodal completed-local-ring
  predicate; no smoothness, normality or integrality of the total spaces is assumed.
- Empty exceptional sets are allowed. `Vᵢ` is then the entire scheme; the condition says pᵢ
  is an isomorphism everywhere.
- A closed point of the special fibre is also closed in the total space since the special
  fibre is closed; conversely the displayed closed singleton over the closed base point
  is exactly such a closed special-fibre point.
- No residue-characteristic restriction, completeness, excellence or field extension of R
  appears. Universe `u` is explicit throughout and `autoImplicit` and
  `relaxedAutoImplicit` are disabled. There is no independent small test-field universe.
- `Set.range` disjointness expresses disjoint section images. Sections of these separated
  morphisms are closed immersions, so this agrees with disjoint marked sections as schemes.

Searches for an existing statement (all through the required msearch wrapper):

- `leanfinder` query `Two marked nodal curve models over a discrete valuation ring with isomorphic generic fibres admit a common nodal model` (subdirectory ``): 8 hits. Candidates: AlgebraicGeometry.ValuativeCriterion.eq, AlgebraicGeometry.ValuativeCriterion.Existence.eq, WeierstrassCurve.exists_isMinimal, WeierstrassCurve.IsGoodReduction, WeierstrassCurve.IsMinimal, AlgebraicGeometry.ValuativeCriterion.existence, WeierstrassCurve.instIsMinimalMinimal, WeierstrassCurve.minimal.
- `loogle` query `AlgebraicGeometry.MultipointedCurve, AlgebraicGeometry.Scheme.Birational` (subdirectory ``): 0 hits. loogle: unknown identifier 'AlgebraicGeometry.MultipointedCurve'. Candidates: none.
- `grep` query `common.*[Nn]odal|[Nn]odal.*[Mm]odel|semistable` (subdirectory `AlgebraicGeometry`): 0 hits. Candidates: none.
- `leansearch` query `A common marked nodal model of two projective semistable curves over a discrete valuation ring` (subdirectory ``): 8 hits. Candidates: WeierstrassCurve.Projective, WeierstrassCurve.integralModel.congr_simp, WeierstrassCurve.integralModel, WeierstrassCurve.isGoodReduction_iff, WeierstrassCurve.exists_isMinimal, WeierstrassCurve.IsGoodReduction.congr_simp, WeierstrassCurve.minimal, WeierstrassCurve.reduction.

The results provide valuative criteria and Weierstrass models, not common nodal marked
models. Direct `rg` searches for `common_marked_nodal|common.*nodal.*model|commonNodal` in
`dag/lean_names_upstream.json`, Mathlib AlgebraicGeometry, the entire `lean/WeilConjectures`
and `lean/Sheaf` source trees found no match. The required item-id search in
`lean/WeilConjectures` found no match. Broader searches for marked/nodal families found
and reused the reconstruction and nodal-geometric-fibre interfaces above. The canonical
section base change was found in the upstream source, and its full signature and data
construction were read.

No STATEMENT-DISPUTED flag or node fault is asserted.

Validation: `scompile.py NW lem-sfb-common-nodal-model` compiled the sandbox and library
module successfully (10.8 s and 10.2 s respectively), with no error or unexpected warning.
`deliver2.py NW lem-sfb-common-nodal-model --no-push` returned OK: server preflight
and per-file compilation passed. A local record check also confirmed that only the node
field `lean` changed, its signature is verbatim, and the single named theorem contains
the sole `sorry`.

## Second reading by NW

This is the worker's self-check; the independent maintainer review is external to this
single-worker delivery, as specified in the dispatch brief. No second agent was started.
The item statement and the final Lean signature were compared clause by clause in the
correspondence table above. In particular finite presentation is not weakened to local
finite presentation (H-projectivity supplies qcqs), connectedness includes nonemptiness,
reducedness and pure dimension are stated separately, the generic isomorphism is over K,
and the two exceptional loci are finite sets of closed points over the closed point of R.
The maps on the complements are the full scheme pullbacks, not just bijections of points.
The last two generic-isomorphism clauses and the permuted marking equation are both present.
No mathematical statement mismatch or required node correction was found.
