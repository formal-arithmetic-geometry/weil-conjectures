## Worker report

This repairs the immutable returned head `2809b69b7e40`. The saved packet passed the
initial prescribed dry run (`df88de833a`), but its required mathematical self-check
confirmed the returned defects. The revised module is
`Sheaf.Paper.VectorBundleThomClass`, namespace
`WeilConjectures.PurityFiniteSetting`. No definition or statement of a dependency
is copied, and the item's mathematical statement, dependency lists and proof are
unchanged. I compared all non-`lean` fields with the current shared node: they agree.

Hypotheses and clauses, read against the node and its main-20261015 blueprint source:

| Node text | Lean rendering |
| --- | --- |
| Fixed finite coefficients A=O_E/(varpi_E^n), n at least one | `P : PurityFiniteSetting.{u}` retains the field, coefficient extension and `level_pos`; the coefficient object is the existing `P.Coefficient`. The finiteness instance unfolds that same quotient and uses `Padic.finite_coefficientExtensionRing`. |
| B separated and finite type over k | Explicit variables `B`, `hB : B ⟶ Spec (.of P.field.k)`, with `[IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB]`. These are inherited binders of every bundle declaration, not auto-bound variables. |
| An arbitrary vector bundle pi:E→B, rank r at least zero, with its specified zero section | `V : PurityVectorBundle P B hB r`, `r : ℕ`, and the existing `V.E`, `V.p`, `V.𝓔`, `V.phi`, `V.over_commutes`, `V.locallyFree`, `V.zeroSection`. The chosen total space need not be literally the canonical relative spectrum. |
| E=Spec Sym(M), F=M dual | `M` is `V.𝓔`; `vectorBundleVectors V := Scheme.Modules.dual V.𝓔`. `vectorBundleTautologicalModule V` is literally `(Scheme.Modules.tensorPullback V.p).obj (vectorBundleVectors V)`. |
| The generator map defines the tautological section | `vectorBundleGenerator` is the existing symmetric-algebra inclusion followed by `VectorBundleZeroSection.algebraIso`, transported by `V.phi.hom.c` and `V.over_commutes`. `VectorBundleTautologicalSectionSpec` prescribes `sum x_i e_i^dual` in every actual affine frame, using `regularSectionDualFrame` and the section-normalized tensor pullback. `vectorBundleTautologicalSection_existsUnique` states existence and uniqueness for that prescription; `vectorBundleTautologicalSection` chooses only this uniquely determined section. |
| Its zero scheme is z(B) and it is regular | The named postponed theorems `vectorBundleTautologicalSection_regular` and `vectorBundleTautologicalZero_existsUnique`. The latter is an isomorphism from B to the actual `regularSectionZeroScheme`, commuting with the two maps into E. Its inverse equation is `vectorBundleTautologicalZero_inv`. Regularity is a conclusion, never an input to the Thom class. |
| thom(E)=c_r(pi*F,s_taut), source z_*A_B, target A_E(r)[2r] | `vectorBundleThomClass V : P.FunctorialCupH true V.zeroSection (2 * (r : ℤ)) r`. Its body applies `(localized_top_chern P).choose` at `T=V.E`, with exactly the tautological module and section, and uses `functorialCupChangeSupport` along the canonical zero-scheme isomorphism. Expanding `FunctorialCupH` gives the degree-zero **underived** closed direct image of `P.constant B` as source. No new uniqueness theorem for localized Chern families remains. |
| The specified twists and derived tensor | The target is the existing `P.functorialCupTwist true V.E r`, the comparison inverse image of `Scheme.finiteEtaleTateSheaf`; `functorialCup` uses the published derived tensor and signed tensor-shift comparison. No private tensor or Tate object is introduced. |
| tau_E from inverse composition identification followed by Rpi_!(thom) | `vectorBundleThomClosedIso` uses the canonical proper comparison `rightDerivedLowerShriekIsoOfIsProper`, exact closed direct image, and the exact single-functor comparison. `vectorBundleThomSourceIso` then applies `originCompositionAmbient`, the existing `V.zeroSection_spec.1`, and `originCompactSupportId`. `vectorBundleThomTau` is precisely its inverse followed by the compact-support functor's map of `vectorBundleThomClass`. Its source is A_B, and its target is Rpi_!(A_E(r)[2r]). It makes no assertion that tau is invertible. |
| The compositor's bounded-below etale-origin domain | `vectorBundleThom_unitOrigin` supplies the witness for the degree-zero constant complex, and `vectorBundleThomOriginUnit` bundles that object in the existing full subcategory. This is derived from the constant etale complex, not an additional hypothesis on V or A_B. |
| For positive rank the projective completion and localization fiber give Rpi_!A_E ≅ A_B(-r)[-2r] | `vectorBundleThom_fiber V (_hr : 1 ≤ r)` states exactly existence of that object isomorphism, with the existing compact-support functor and signed finite Tate sheaf. Its full proof docstring constructs P_B(M plus O), H=P_B(M), and the complement; pushes the localization triangle; uses the two projective-bundle decompositions; and accounts for the possibly nonzero final column `[1 v]` by `(s,c) ↦ (s-vc,c)`. It does not identify tau with an arbitrary generator. |
| Under a local direct-sum decomposition, the class is the cup product of pulled line classes | `vectorBundleThomClass_directSum` states the binary form on an actual module decomposition `e : V.𝓔 ≅ V₁.𝓔 ⨯ V₂.𝓔`. `vectorBundleThomProjection₁/₂` come from the inclusions of generators by the uniquely normalized `vectorBundleLinearMap`; no arbitrary projections are assumed. `vectorBundleThomPullback` uses the literal Cartesian square of each pulled-back zero support. `vectorBundleThomSumSupport` identifies their scheme-theoretic intersection with z(B). The displayed `HEq` compares the transported total Thom class with `P.functorialCup` of those pulled classes; it only accommodates the equal degree expressions `2(r+s)` and `2r+2s`. Iteration with one-dimensional factors and the published associativity gives the node's finite ordered local line product. The same theorem applies on every open carrying the decomposition, since such opens of B are Noetherian and quasi-compact. |
| Rank zero, identities and empty product, with no rank-minus-one projective bundle | `vectorBundleThom_rankZero_geometry` states that pi is an isomorphism with inverse z. `vectorBundleThomClass_rankZero` is the identity after the actual coefficient restriction and zero-shift comparison. `vectorBundleThomTau_rankZero` is the identity after the same coefficient comparison and `vectorBundleThomSourceIso`. The positive-rank fiber theorem alone uses projective completion. |

Dependency interfaces read and used (including the helper declarations of their
recorded modules):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `constant`, `constantEtale`.
- `Sheaf.Paper.PurityVectorBundleZeroSection`:
  `AlgebraicGeometry.PurityVectorBundle`, its `zeroSection`, `zeroSection_spec`;
  the imported owning module `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`
  supplies `algebraIso` and the symmetric-algebra generator.
- `Sheaf.Paper.LocalizedTopChern`: `localized_top_chern`,
  `LocalizedTopChernClasses`, `LocalizedTopChernLaws`. The result is existential,
  not unique. The existing regular-section module supplies `regularSectionDualFrame`,
  `IsRegularSection`, `regularSectionZeroScheme`, `regularSectionZeroProjection` and
  `regularSectionZeroIdeal_spec`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its finite-twist imports:
  the same finite signed Tate sheaves exposed by `functorialCupTwist`. The recorded
  `sfQbarTwistingFunctor` is the common-stage part of this coefficient node; this
  finite-coefficient construction uses the module's existing finite part.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: the existing
  derived tensor, used through supported cup, without a second tensor construction.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`,
  the recorded compactification formula; the fixed-scalar presentation of that
  construction is `ProEtale.rightDerivedLowerShriek`.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompositionAmbient`
  (the ambient component underlying recorded `originComposition`) and
  `originCompactSupportId`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry`:
  `exists_projectiveBundleTautologicalGeometry` and the actual relative-Proj
  realizations; `Sheaf.Paper.ProjectiveBundleFormula`: `projectiveBundleFormula`,
  in the postponed positive-rank fiber proof.
- `Sheaf.Paper.SfOpenClosedTriangleAllStages`: `sfOpenClosedTriangle_finite`, the
  finite part of the node whose main record lists `sfOpenClosedTriangle_qbar_weil`.
- `Sheaf.Paper.SupportedCup`: `ProEtale.supportedCup`; its twist-multiplied version
  in `Sheaf.Paper.SupportedCupFunctoriality` is `functorialCup`, used with its
  existing `functorialCupPullback` and `functorialCupSupportMap`.
- The proof imports retain `ProEtaleRingedOpenClosed`, `FiniteDirectImageComposition`
  and the derived direct-image triangulated interface for the closed exactness,
  pushed localization triangle, and proper-image composition in the node's proof.
  The proper comparison is the existing
  `WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample` declaration
  `ProEtale.rightDerivedLowerShriekIsoOfIsProper`.

Edge checks: r=0 is explicitly covered, with an empty coordinate sum and identity
normalizations. Empty B and empty trivializing opens are not excluded; their section
modules and augmentation quotients still have the stated prescriptions. The polynomial
regularity argument works over rings with zero divisors, so no smoothness, regularity
or reducedness of B has been added. Neither r>0 nor regularity is a hypothesis of the
Thom definition. A nontrivial M and a chosen total space transported by phi are retained:
no trivialization or equality E=the canonical model is assumed. In a change of frame
`e'=eG`, generator coordinates transform by G transpose and the dual by G inverse
transpose, so the tautological sum is invariant. The two direct-sum factors can have
rank zero; swapping factors introduces no cohomological sign because their degrees are even.

Searches: the retained packet's `searches.jsonl` records the original LeanFinder,
Loogle and LeanSearch attempts and their unrelated topological-bundle results.
For this repair I reran `msearch.py ... leanfinder` with
"algebraic vector bundle tautological section of the pullback dual of the symmetric
algebra generator module, supported Thom class and compact support": eight hits,
all topological trivialization/Hom-bundle declarations. `msearch.py ... loogle
'"vectorBundleThom"'` returned zero hits. `rg` for
`vectorBundleThom|[Tt]autological[Ss]ection|[Tt]hom[Cc]lass` in Mathlib AlgebraicGeometry,
upstream WeilConjectures, and current shared `lean/Sheaf` returned no hits; searching
upstream for this node id also returned none. The module reuses the existing algebraic
bundle, dual, regular-section, localized-Chern, tensor, cup, compact-support and compositor
notions instead of defining replacements.

## Repair of the return

H3: replaced arbitrary `(T,a,F,r,s,hs)` by the recorded `PurityVectorBundle`;
constructed its dual, tensor pullback, generator-normalized tautological section,
regularity and zero-scheme identification; the source is now the actual zero-section
pushforward. Added tau, the rank-zero identities, the positive-rank fiber calculation,
and the supported direct-sum/cup clause. All eleven statement dependencies now have
their stated role in the construction or its postponed proof.

H3/H6: removed `existsUniqueLocalizedTopChernClasses` completely. The definition
uses exactly `(localized_top_chern P).choose`, as requested. The remaining unique
choices concern the explicit generator characterization or a unique isomorphism
over E, never uniqueness of Chern families.

H11: replaced the former second reading with the declaration-by-declaration reading
below. It no longer claims that an arbitrary input section renders the tautological one.

H1: removed the inaccurate dependency-copy section. There is no LocalizedTopChern
copy or dependency node in this delivery; the current recorded module imports and compiles.

## Second reading by Q12

I reread the corrected file with the entire unchanged node and the current blueprint
definition open, under the dispatcher's instruction not to start another agent.
The independent immutable-head review remains the maintainer's. The clause table above
records this second reading, including the previously missing clauses.

In particular, I checked the *body* of `vectorBundleThomClass`: its section is
`vectorBundleTautologicalSection V`, its module is the tensor pullback of M dual,
its regularity proof is a theorem, and its source is transported from the actual
regular-section zero scheme to `V.zeroSection`, rather than left on arbitrary T.
I checked the *body* of `vectorBundleThomTau`: the source comparison runs from
Rpi_!z_*A_B to A_B, so its **inverse** precedes the compact-support image of thom.
Its composition input is the retained origin object of A_B, with the existing
zero-section equality and the compositor's identity normalization.

I expanded the rank-zero target: finiteEtaleTateSheaf at zero is the existing
constant sheaf, so the statements normalize only the zero shift and the actual
closed coefficient restriction. The fiber theorem is restricted to positive rank
and uses the negative signed twist and shift, not the positive Thom target. The
cup law pulls back along generator-determined projections, compares the correct
intersection support, and uses HEq only for the two arithmetically equal degree
presentations. Every omitted geometric proof is now a named theorem with this
node's blueprint id and a full coordinate/composition proof docstring. All data
definitions have actual bodies; no theorem asserts uniqueness of the localized
Chern family, and no extra geometric hypothesis was introduced.
