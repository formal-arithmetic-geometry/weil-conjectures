## Worker report

The module `Sheaf.SixFunctors.CompactSupportProperImageTower` states
`WeilConjectures.CompactSupportProperImageTower.compactSupportProperImageTower`.
Its only postponed proof is this named theorem. The helper declarations have real data
or are structures specifying the canonical presentation; no object, arrow or definition
is assigned sorry. The node is unchanged outside `lean`.

The statement supplies the canonical presentations in its conclusion, then gives the
consecutive transition equation and an isomorphism of inverse systems whose components
are exactly beta. Presentation witnesses are not extra hypotheses. In particular,
`DirectData` fixes the ordinary coefficient comparison by identity on underlying sections,
and fixes its derived comparison by `CompactSupportDerivedSquareNormalization` on every
K-injective complex and every K-injective resolution of its restriction. `OpenData` fixes
the ordinary open comparison on every direct-sum extension generator. Its derived map
`openRestriction` is the localization of that ordinary comparison. These normalizations
exclude twisting either comparison by arbitrary coefficient-level automorphisms.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Field K_0 | `(K₀ : Type t) [Field K₀]` |
| X,Y finite-type K_0-schemes | `X Y : Scheme.{t}`, their `Over (Spec (.of K₀))` instances, and `LocallyOfFiniteType` plus `QuasiCompact` of both structure morphisms |
| Separated finite-type K_0-morphism f | `(f : X ⟶ Y) [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| Same compactification c=(j,p) | `(c : Compactification f)`, with `c.i`, `c.g`, `c.Z`; the structure supplies open immersion, properness and `c.i ≫ c.g = f` |
| j quasi-compact | `[QuasiCompact c.i]` |
| Prime ell, invertible in K_0 | `(l : ℕ) [Fact l.Prime]` and `(_hl : IsUnit (l : K₀))` |
| Finite E/Q_l and its valuation ring, uniformizer, positive quotient levels | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the existing coefficient sheaves use `Padic.coefficientExtensionRing l E (n+1)`, built from the recorded integer ring and chosen uniformizer |
| Small pro-etale site and R_W=lim P_n | The existing `scalarReductionSource l E W`, completed coefficient sheaf, and its actual limit projections; no discrete constant integer coefficient object is substituted |
| Res_n restriction along the projection | `coefficientFiniteDerivedRestriction l E W n`, which is the recorded `scalarReductionDerivedRestriction` |
| K derived complete, without boundedness/constructibility/Tor assumptions | `K : (IntegralOpenReduction.complete l E X).FullSubcategory`; `complete` is `IntegralOnSlice.IsComplete ... none`, the existing quotient-tower Roos completeness condition |
| L=j_!K using completed ringed extension | `(IntegralOpenReduction.shriek l E c.i o).obj K.obj`, the recorded exact localized ringed-slice extension |
| K_n and L_n derived finite reductions | `coefficientFiniteDerivedExtension l E X n` and its c.Z counterpart; these are the recorded `scalarReductionDerivedExtension` |
| Canonical alpha_n | `alpha`: inverse of the actual reduction evaluation, evaluation of `r.r`, canonical J evaluation, and actual reduction evaluation on X |
| N_n=Res_n Rp_{*,n} L_n | `properLevel` |
| M_n=Res_n Rp_{*,n} j_! K_n | `supportLevel`, using the same `compactSupportLevelDirectImage` as N and the recorded `compactSupportCanonicalJLevel` |
| S_n quotient restriction | `normalizedDVRRes l E W (Nat.le_succ n)` along the actual coefficient-system quotient |
| Quotient reduction d_n and k_n | `reductionMap`, the transpose of the smaller-level actual reduction unit under the larger-level normalized derived scalar adjunction; this is id tensor quotient on K-flat representatives |
| C_n ordinary finite-coefficient direct-image/restriction comparison | `d.comparison n`; section and K-injective normalizations are fields of `DirectData` |
| N transition Res_(n+1)(C_n Rp_*(d_n)) | `properTransition`, followed by `compactSupportSystemRestrictionComp` to identify successive restriction with Res_n |
| M transition applies finite compact support to k_n, then its specified coefficient comparison | `supportTransition`: apply J_(n+1) to `reductionMap`, apply the localized generator-normalized open comparison, apply Rp_(n+1), then the SAME `d.comparison n`; finally use the SAME completed restriction composition |
| beta_n=Res_n Rp_{*,n}(alpha_n), an iso | `beta` is the two actual functors' `mapIso` applied to `alpha` |
| beta commutes with every consecutive transition | The `∀ n : ℕ` equality in the conclusion is `properTransition ... n ≫ (beta ... n).hom = (beta ... (n+1)).hom ≫ supportTransition ... n`; Lean writes composition left to right |
| Isomorphism of inverse systems, not merely unrelated levelwise isomorphisms | `properTower` and `supportTower` use Mathlib `Functor.ofOpSequence`; the conclusion supplies `b : properTower ... ≅ supportTower ...` with `b.hom.app (op n) = (beta ... n).hom` |
| Every n>=1, with all further transition composites | Lean index zero is exponent one. All natural-number indices occur, and the natural isomorphism is natural for every morphism of ℕᵒᵖ |

Dependency declarations read and used:

- `WeilConjectures.Compactification.RefinementCategory`: `AlgebraicGeometry.Compactification.Refinement`
  and `category`; compactifications themselves are the upstream `Compactification` in `Defs`.
  The morphism-property dependency is the recorded convention node, so its collected Mathlib
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, and `IsProper` are used.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `CoefficientExtension`:
  `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionRing` and quotient maps.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` / `CompletedIntegralCoefficients`:
  `integralConstantToCompletionOfUniverses`, `integralCoefficientSheaf`,
  `completedIntegralCoefficientSheafUnrestricted`,
  `completedIntegralCommRingSheafUnrestricted` and its projections. The constant map module
  is imported as the dependency's recorded independent-universe interface.
- Mathlib `Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` (the restriction dependency's Mathlib match).
- `Sheaf.Paper.DerivedCompleteOnSlices`: `WeilConjectures.IntegralOnSlice.IsComplete`,
  reached through `IntegralOpenReduction.complete`; its global branch is the recorded
  `IsDerivedCompleteUnrestricted`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`:
  `proEtaleRingedExtensionByZero` and `proEtale_ringed_open_closed` give the ringed open
  notion; the actual exact localized open model used is the normalized one in the
  recorded open-reduction module.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension`, `scalarReductionDerivedRestriction`,
  `derivedScalarExtensionRestrictionAdjunction`. The coefficient-sequence module's
  `coefficientFiniteDerivedExtension`, `coefficientFiniteDerivedRestriction` and
  `coefficientFiniteAdjunction` reuse these definitions.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`:
  `Operations`, `TensorComparison`, `Comparison`, `shriek`, `finiteExtension`,
  `finiteExtensionSection`, `J`, `extensionEvaluation`, `complete` and the statement
  `integralOpenReductionComparison`. The `alpha` formula evaluates the actual `Comparison.r`;
  its `strictModel` is the retained canonical quotient compatibility, not a new assumption.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`:
  `intrinsicCompactSupportRestriction` is the open comparison followed by the normalized
  proper comparison. The helper `supportTransition` spells out exactly that same
  composite on the independent-universe slice coordinates, retaining all generator
  and K-injective normalizations rather than assuming an arbitrary comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingDerivedPullback` and the imported arbitrary-ringed operations
  specify the ordinary, uncompleted derived operations. Their sectionwise direct-image
  presentation here is the existing `compactSupportLevelDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`:
  `fixedScalarRestrictionDirectImage`, `fixedScalarRestrictionDirectImage_kInjective`;
  these give the normalization represented in the helper `DirectData` in the equivalent
  intrinsic small-site coordinates, without assuming restricted K-injectives are K-injective.
- Mathlib `CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, including the full signatures/docstrings.
- Existing transitive presentation helpers in
  `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram`:
  `compactSupportLevelDirectImage`, `CompactSupportDerivedSquareNormalization`,
  `compactSupportCanonicalJLevel`, `compactSupportCanonicalJEvaluation`, and
  `compactSupportSystemRestrictionComp`. These give the existing actual operations,
  not a second definition of the compact-support functor.

Sources checked: the current blueprint ancestor
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/def-weil-integral-rational-qbar-compact-support.md`;
Bhatt--Scholze PDF p.56, Definition 6.7.6 and Lemma 6.7.7 (using pdftotext);
`literature/stacks-project/sites-modules.tex`, `lemma-j-shriek-and-tensor` (Tag 0E8I).
The statement's four proof steps are carried in the theorem docstring. In particular,
proper direct image is derived separately after exact open extension; it is not the
right derived functor of the underived composite (compare Bhatt--Scholze Remark 6.7.8).

Edge cases checked before writing and again against the final signature:

- `n=0` means P_1, not the zero coefficient ring P_0. The quotient is P_2 -> P_1.
- The zero derived complex is permitted; its quotient maps and beta components are zero-object isomorphisms.
- Empty X or an empty open immersion is permitted. Open normalization quantifies over
  the actual extension summands and imposes no nonempty-open or nonzero-section assumption.
- An identity open immersion is permitted; its comparisons reduce to the same canonical
  tensor and scalar-restriction identifications.
- Arbitrarily unbounded derived-complete K is permitted. There is no constructibility,
  finite Tor dimension, boundedness, nonzero K, or nonempty scheme binder.
- Site object universe t+1 and morphism universe t are retained; coefficient size is
  max u (t+1). No equality t=u is imposed. All universes and object variables are explicit.
- Longer quotient transitions are the composites in Mathlib's inverse sequence; the
  resulting b is a natural isomorphism for every such morphism, including identities.

Searches actually run (2026-10-21):

1. `msearch.py ... leanfinder "The proper derived image reduction tower of completed extension by zero is canonically isomorphic to the compact support reduction tower"`:
   8 hits, including `HasCompactSupport.extend_zero`, homological-complex extension lemmas,
   and `IsAdicComplete.StrictMono.factorPow_comp_extend`; none is this statement.
2. `msearch.py ... loogle '"ofOpSequence", "Iso"'`: 0 hits.
3. `msearch.py ... grep '([Cc]ompactSupport|[Ee]xtensionByZero).*([Tt]ower|[Rr]eduction)'`:
   0 Mathlib hits.
4. `msearch.py ... leansearch "The canonical maps Res_n Rp_* alpha_n give an isomorphism of inverse systems for completed extension by zero and compact support"`:
   8 hits, chiefly ordinary `AdicCompletion` factorization/naturality; none identifies these derived towers.
5. `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
   `properImageTower|proper_image_tower|compactSupport.*[Tt]ower|compact.support.proper.image.tower`:
   upstream `Etale.AdicSystem.compactSupportTower` and `exists_compactSupportTower` concern
   normalized perfect compactly supported GLOBAL SECTIONS on the etale site with bounded
   constructible finite-Tor input, not this arbitrary complete pro-etale object over Y.
   Read both declarations. Project `CompactSupportReductionTower` gives a strict tower
   existence theorem, not the comparison between the two towers here.
6. `rg -n 'lem-sf-compact-support-proper-image-tower' lean/WeilConjectures`: no match.
7. Further `rg` for reduction maps found `compactSupportReductionMap` (equal site/coefficient
   universe), `sfDerivedReductionTransition` (already restricted to completed coefficients),
   and unrelated condensed coefficient maps. The delivered `reductionMap` is the missing
   finite-linear adjunct with independent sizes; it is built directly from the recorded
   normalized adjunction and restriction composition, with no replacement reduction functor.

No new DAG node, dependency-node rewrite, statement correction, or disputed statement.

## Second reading by NB

A second pass opened the node, each dependency record and the completed module, comparing
the hypotheses and every conclusion clause in the table above. The finite-level alpha
is obtained by evaluating `r.r`, not by choosing a levelwise isomorphism. Both transitions
use exactly the same `d.comparison n`. The support transition uses the canonical ordinary
open summand map localized termwise; it is not defined by conjugating the proper transition
with beta, which would make the target claim tautological. Beta is precisely two mapIso
applications, and b's component equation fixes its actual arrows.

The initial open section normalization was replaced with a typed comparison of functions
on extension generators. This avoids an expensive kernel conversion between two scalar
module presentations while preserving the specified generator equation. Independent
site/coefficient universes are retained throughout. Compile errors from competing older
sheafification instances were repaired by using the existing independent-size instances;
no universe restriction or mathematical hypothesis was added. The temporary heartbeat
diagnostic option was removed. No mathematical mismatch or statement fault remains.
