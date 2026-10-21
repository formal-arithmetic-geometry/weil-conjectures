## Worker report

The delivery states `lem-sf-locally-closed-closure-comparison-square` in
`Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare`. No node statement,
statement dependency, proof or proof dependency was changed. The module contains real
composite constructions and five named theorems with `sorry`; it proves no new theorem.
The module never imports the downstream `FiniteDualityLocallyClosedComparison` module.

The source read was the current blueprint main-20261015,
`sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`,
the second paragraph's sentence “The locally closed Rs^! commutes with ν^* by the open
and closed comparisons above.” The node is the explicit left-adjoint coherence step
of that argument. I read its six proof steps and the statements and records of all
sixteen statement dependencies. Their relevant declaration signatures and docstrings
were read in the local live-project source, including the complete canonical mate,
etale normalized extension theorem, and pro-etale extension-coherence interfaces.

Hypothesis and clause correspondence:

| Node | Lean rendering |
| --- | --- |
| finite discrete commutative A | `(A : Type (u + 1)) [CommRing A] [Finite A]`; fixed-scalar module sheaves encode the discrete constant coefficients |
| ordinary derived module categories, L in D+ | the existing `DerivedCategory.Plus (Sheaf ... (ModuleCat.{u + 1} A))`; equalities of natural transformations quantify over every L and give naturality |
| C_W is the exact termwise comparison | recorded `siteComparisonDerivedPullbackPlus W A` |
| open comparison o_j | `closureSquareOpenComparison A j`, the termwise descent of the recorded `openImmersionLowerShriekComparisonUpperStarIso`, with the canonical descent composition maps |
| closed comparison delta_h | the actual `fixedComparisonDirectImageMatePlus A h`, converted to an isomorphism using its recorded invertibility theorem; no isomorphism is chosen |
| canonical pullback comparison a_h | recorded `fixedComparisonPullbackPlus A h`, the inverse of the published sheaf pullback comparison, descended termwise |
| T Noetherian | `[IsNoetherian T]`, precisely locally Noetherian plus compact underlying space |
| immersion s and a closed/open factorization | `(s : S ⟶ T) [IsImmersion s]`, `(c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]`, `(h : c ≫ v = s)` |
| scheme-theoretic closure Sbar, u and i | the existing `s.image`, `s.toImage`, `s.imageι`, with the actual equality `s.toImage_imageι`; no arbitrary closure or arbitrary factor map |
| closure open factor has the necessary immersion property | `closureSquareImageOpen` derives it from the Noetherian topology induced on S by s and Mathlib's quasi-compact-source instance, then Mathlib's image factor theorem; no extra quasi-compact hypothesis |
| F_e and F_p | `closureSquareEtaleFactor` and `closureSquareProEtaleFactor`: derived closed direct image followed by termwise open extension |
| E_e and E_p | `closureSquareEtaleClosure` and `closureSquareProEtaleClosure`: termwise open extension followed by derived closed direct image |
| q_e and q_p are identity-normalized closure identifications | `qe`, `qp` and `he`, `hp : closureSquare...Normalized ...`; these predicates use the actual open units, closed counits and pullback compositors |
| Delta_L = v_p!(delta_c,L) o_v | `closureSquareDelta`: whisker o_v by Rc_e,* and then whisker the specified delta_c by v_p,! |
| B_L = i_p,*(o_u) delta_i | `closureSquareB`: whisker the specified delta_i by u_e,! and then whisker o_u by Ri_p,* |
| Delta and B natural isomorphisms | both constructions have natural-isomorphism types; bounded-below closed direct images and exact open extensions make every input admissible |
| q_p Delta = B C_T(q_e) | first conjunct of `locallyClosed_closure_comparison_square`, with Lean composition read left to right |
| restriction identifications agree through the compositor for s | second and third conjuncts of the main theorem; each uses the same `fixedComparisonPullbackPlus A s` and the explicit `closureSquare...PullComp` in its restriction map |
| a second factorization | `c'`, `v'`, immersion instances and `h' : c' ≫ v' = s` in `locallyClosed_closure_comparison_change`; its q maps have the same canonical closure target |
| t = inverse q' after q | real definition `closureSquareChange q q' := q ≪≫ q'.symm` |
| t_p Delta = Delta' C_T(t_e) | first conjunct of `locallyClosed_closure_comparison_change` |
| t restricts to the identity | second and third conjuncts of that theorem, using precisely the two factorization restriction maps |
| identity and cocycle on derived categories | `locallyClosed_closure_comparison_etale_laws` and `locallyClosed_closure_comparison_proetale_laws` |
| identity and cocycle termwise | `locallyClosed_closure_comparison_termwise_laws`, for the actual closed/open composites of module-sheaf functors on each site |

The q parameters are given identifications, as in the node's “let q”. Their restriction
normalization is an equivalent characterization of the termwise normalized maps supplied
by the two recorded extension-comparison dependencies. On the derived categories this
characterization still determines q uniquely: conjugate two normalized maps to an
endomorphism of F, apply the restriction Hom bijection, and cancel. Therefore quantifying
over normalized derived coordinates does not replace a specified q by arbitrary
isomorphism data. Closed direct images are exact here, so using Rclosed in F and E is
canonically the termwise version stated in the node. The restriction maps use derived
closed counits, which agree with the termwise counits by the normalization proof dependency.
No extra exactness hypothesis is required in the delivered signatures.

All helpers are the explicit composites F, E, Delta, B, r_F, r_E and t introduced in this
node, or their normalization predicates and canonical descent compositors. None is an
independent missing notion requiring another DAG node. The definition of the closure is
Mathlib's kernel-ideal subscheme; in particular it does not substitute the reduced
closure or only the topological closure.

Dependency declarations used (namespace `AlgebraicGeometry.ProEtale` unless indicated):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules` and its
  canonical fixed-scalar realization interface, reexported through the intrinsic
  coefficient modules. These justify the fixed-scalar coordinates already used by
  both recorded comparison maps. No coefficient presentation is redefined.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, its canonical adjunction.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek` and its upper-star adjunction.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` and its realization equivalence;
  the same open extension in the fixed-ring coordinates is the public upstream
  `openImmersionLowerShriek`, used by the recorded open comparison.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparison_pullback_coherent`; no second comparison is constructed.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, `isIso_fixedComparisonDirectImageMatePlus`,
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus_counit`.
- Mathlib `AlgebraicGeometry.IsOpenImmersion`, `IsClosedImmersion`, `IsImmersion`,
  `IsLocallyNoetherian`, `IsNoetherian`, `CompactSpace`, `Scheme.Hom.image`, `toImage`,
  `imageι`, and `toImage_imageι` are the recorded geometric notions.
- `Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison`:
  `AlgebraicGeometry.etale_locallyClosed_extension_comparison` and its canonical
  restriction normalizations.
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`:
  `AlgebraicGeometry.Scheme.locallyClosedExtensionCoherence` and the `homBijection`
  field of its `DerivedCoherence` witness.
- The existing etale/pro-etale `derivedUpperStarLowerStarAdjunctionPlus`,
  `Etale.upperStarCompDerivedPlus`, `upperStarComp`, `upperStarCongr`, and generic
  `Functor.mapDerivedCategoryPlusNatIso`, `mapDerivedCategoryPlusCompIso`,
  `mapDerivedCategoryPlusIdIso` implement the displayed restriction formulas.

Proof-only imports include finite direct-image exactness and exact-functor descent.
The proof dependency `lem-sf-derived-immersion-comparison-normalization` currently has
neither a Lean record nor a Mathlib match, so it has no import to add under the rule
for already-stated proof dependencies. Its mathematical normalization is explicitly
named in the proof docstring; the theorem is not needed to type this statement.
The Mathlib-only Noetherian proof dependencies are available through the public
Noetherian imports. No downstream theorem is imported to introduce its own map.

Edge cases checked before writing: S empty (all image and restriction constructions
remain defined); s open, s closed, and s an identity (the same canonical image formula
and unit/counit expressions apply); zero coefficient ring (no `Nontrivial A`);
unbounded-below L is intentionally excluded exactly by the node's D+ condition;
no nonempty support, reducedness, properness of s, field, finite-type-over-field,
separatedness or independent equality of site universes is assumed. Arbitrarily large
finite coefficient types are covered by the standard fixed-module universe u+1.
The generic inverse-cancellation laws even hold for any closure identifications,
so their two statements do not need redundant normalization premises.

Actual searches:

1. msearch.py `leanfinder`, query “Etale proetale comparison commutes with locally closed
   extension closure factorization normalized change of factorization”: eight results,
   beginning `Algebra.Etale.comp`, `AlgebraicGeometry.IsEtale.instHasOfPostcompPropertyScheme`,
   and standard-etale presentation lemmas; no match.
2. msearch.py `loogle`, query `"comparisonUpperStar"`: successful search, zero hits.
3. msearch.py `grep`, query `locallyClosed.*[Cc]omparison|[Cc]omparison.*locallyClosed`:
   successful Mathlib search, zero hits.
4. msearch.py `leansearch`, query “The canonical comparison of etale and proetale locally
   closed extension by zero commutes with scheme theoretic closure factorization”:
   eight results, including `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
   `PrimeSpectrum.closure_image_comap_zeroLocus`, and etale morphism properties; no match.
5. rg over both `lean/WeilConjectures` and `lean/Sheaf`, same locallyClosed/comparison
   regex and the item id: the existing etale closure theorem and the downstream
   `FiniteDualityLocallyClosedComparison` module were found. The latter defines its own
   Delta and q_e for its exceptional-adjoint statement but only mentions this square in
   its proof plan; neither its theorem nor `locallyClosed_comparison_factorization`
   states this node's closure square and restriction equations. Importing the downstream
   theorem would reverse the proof dependency. No duplicate construction is used.
6. Literal `grep -rn` of the item id in `lean/WeilConjectures`: no hits.

No statement correction, dependency repair, disputed statement or new node was needed.
The server wrapper scompile.py compiled the sandbox and library module names cleanly
at the default 60-second limit, with no errors or warnings. All variables and universes
are bound explicitly (`set_option autoImplicit false`). Every line is at most 100
characters; every helper and theorem has its source/blueprint docstring. Definitions
have explicit data, with no sorry; each of the five postponed named theorems is recorded
in lean.declarations and has the applicable natural-language proof.

## Second reading by Q41

I reread the node and the final module against the table above. This is the worker's
self-check; no independent agent was started, as the brief forbids delegation. The
maintainer supplies the independent review. The two composites use the right order:
Delta is o_v then v_!(delta_c), while B is delta_i then i_*(o_u). The shared closure is
literally s.image, and both restriction equations use a_s rather than separate arbitrary
identifications. The change square has q followed by inverse q' on each site, giving
Delta then t_p on the left and C_T(t_e) then Delta' on the right. The final read added
the termwise identity/cocycle theorem so the node's pre-descent laws are explicitly
stated as well as the derived laws. No mathematical mismatch was found in this read.
