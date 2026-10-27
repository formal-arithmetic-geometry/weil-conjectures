## Worker report

Stage 2, Q152, lem-pur-witnessed-open-chart-transport. Q155's reviewed PASS was a stage-1 split, not a stage-2 statement delivery: its report explicitly says there are no Lean files, and the live item has no lean record. The earlier worker's stage-1 live-wins disposition therefore does not apply. This is the repair of L's independent return at immutable head 16525712b940. The repair preserves the complete current natural-language statement, its eight-step proof, and both Lean theorem signatures.

The item module is Sheaf.Paper.PurityWitnessedOpenChartTransport, namespace AlgebraicGeometry.ProEtale.PurityWitnessedChart. Its two postponed theorems are open_restriction and witnessed_open_chart_transport. Every other declaration is an abbreviation, a genuine canonical construction, or the record of the theorem's conclusions. There are no unfilled definition data. The proofs of the two theorems are sorry; their docstrings give the full proof plans. The public statement ingredients homChain and kappa use the existing constructions recorded by definition nodes: the new def-sf-etale-chart-hom-chain and the landed def-per-site-comparison-pullback-data. Those definition nodes replace the two theorem nodes added by the returned packet to stmt_deps; the theorem nodes remain in proof_deps. There is no statement correction.

Hypotheses and clauses, read against the node:

- Finite purity coefficients: S : WeilConjectures.PurityFiniteSetting carries the finite-field datum, ell different from its characteristic, the fixed coefficient closure, a finite intermediate extension E, and the positive level. S.Coefficient is the published ULift of O_E/(varpi_E^n) in the module-value universe. coefficientFinite obtains the recorded finiteness theorem, with S.level_pos, and the ordinary ULift instance. It adds no coefficient assumption. The schemes remain Scheme.{u}, with site objects in u+1 and site morphisms in u.
- C_Z and the ambient derived categories: compare A Z is the exact comparisonUpperStar.mapDerivedCategory; recover A Z is comparisonLowerStar.rightDerivedFunctor. Et A Z abbreviates the recorded Etale.DerivedCategoryModule; Pr A Z is the ordinary fixed-module pro-etale derived category. The category C(Z) is FixedEtaleOriginDerivedCategory Z A, the authorized dependency coordinate repair below. Its first component is a D+ object, and its second is the existing FixedEtaleOriginWitness, retaining complex and iso. InducedCategory makes every underlying pro-etale arrow a morphism.
- F_v^c, H_v^c, G_v^c and compactifications: right A c is the right adjoint of the exact recorded ordinary etale rightDerivedLowerShriekOfCompactification; adj A c is its actual adjunction, using the recorded left-adjoint existence theorem as a local instance, without an extra hypothesis. exceptional A c abbreviates the recorded sfFiniteExceptionalAt A c, literally recover, H, compare. Compactification is the published factorization structure. chosenAdj conjugates adj through the canonical compactification comparison to the chosen Rv_! used by the existing normalized chart Hom chain; it does not choose a new comparison. The introductory pro-etale Rv_!^c notation imposes no additional result in this node and is not redefined.
- Every open immersion between finite-type k-schemes: open_restriction binds W,Z : Over (Spec S.field.k), their locally-finite-type and quasi-compact structure maps, and j : W ⟶ Z with IsOpenImmersion j.left. There is no separatedness assumption on either structure map.
- Exactness on both constant-A sites is the first two pairs of PreservesFiniteLimits and PreservesFiniteColimits. The two Nonempty natural-isomorphism clauses identify leftDerivedFunctor with the respective exact termwise pullback. The two IsGE clauses quantify over every integer n, preserving the same cohomological lower bound.
- The actual lift is openLift A j. Its object is the exact pro-etale pullback of N.1, with antecedent Etale.upperStar.mapDerivedCategoryPlus.obj N.2.complex. Its iso is kappa.app N_e followed by prPull.mapIso N.2.iso. kappa is the localization of the canonical sheaf comparison with the exact functor composition identifications, not an unspecified isomorphism. map takes an arbitrary induced-category arrow to its underlying pro-etale pullback. The identity and composition proofs here only discharge the definitional functor laws.
- Identity and successive restriction: open_restriction asserts natural isomorphisms from openLift id to identity and from openLift(hj) to openLift(j) followed by openLift(h). Their underlying components must be the canonical prId/prComp. The next equality in each case relates the actual retained witness isomorphisms by the canonical etId/etComp comparison, so it includes witness coherence, not merely an isomorphism between forgotten objects. For successive restrictions U is again finite type over k and h is any open immersion; naturality uses all underlying arrows.
- Chart geometry: witnessed_open_chart_transport binds X,V as finite-type k-schemes, IsAffine V.left, f as a k-morphism (Over morphism) with precisely separated finite-type hypotheses, U affine and j an open immersion, d : Nat including zero, i a closed immersion into AffineSpace (ULift (Fin d)) V.left, and w exactly j >> f = i >> pi. pi is the published canonical AffineSpace structure map. The three binders cf,ci,cp are arbitrary supplied compactifications. U's k-structure is the composite through j; its finite type follows from the Noetherian open argument, not a new assumption.
- Noetherianity and map geometry: ChartTransportData.noetherian states it for U,X,T,V; j_qc proves the missing quasi-compactness of the open immersion, and p_sep,p_ft,p_qc give separated finite type for pi. The existing IsOpenImmersion and IsClosedImmersion instances give separatedness/local finite type for j and i and properness/quasi-compactness for i. Composition instances then give the same properties for the displayed composites, and Nagata supplies their compactifications. The proof never assumes X separated over k.
- D+ claims: plusF, plusP and plusIP quantify over every bounded-below etale N_e, asserting H_f N_e, H_pi N_e and H_i H_pi N_e bounded below. plusQ asserts the same for j_e^* H_f N_e. No uniform input-independent bound, bounded constructibility, finite Tor amplitude or exceptional-image admissibility hypothesis appears.
- Ordinary etale natural isomorphism: ChartTransportData.a is a natural isomorphism between Plus.ι >> H_f >> j_e^* and Plus.ι >> H_pi >> H_i, in the actual derived category. Both targets are D+ by plusQ/plusIP, so this is also an isomorphism in its full D+ subcategory. normalization says, for every bounded-below H and N_e and every t : H -> Q, homChain(t) = t >> a_N. unique says every isomorphism with that property equals a_N. This records the unique normalized representing isomorphism, not only per-degree cohomology or bare existence.
- Exact displayed Hom chain: homChain specializes the existing Etale.ChartAdjointComparison.homChain to its f=f, s=j, v=id_V, i=i and p=pi, using chosenAdj at each supplied compactification. The final ordinary identity-inverse-image normalization removes v^*. The imported definition explicitly uses the j_! / j^* adjunction, F_f / H_f, normalized compact-support compositor, open identity adjunction, F_pi / H_pi, canonical closed normalization to i_*, and F_i / H_i. Thus it is precisely the displayed chain with i_{e*}, and not an arbitrary Hom equivalence.
- First comparison unit: witnessUnit A N is eta_{N_e} followed by recover.map beta, in categorical composition order. witnessExceptional A c N is compare.map(right.map witnessUnit). unit_iso, f_iso and p_iso assert invertibility, giving exactly G_f N ~= C_X H_f N_e and G_pi N ~= C_T H_pi N_e.
- Second comparison unit: targetWitness is compare_U.map(H_i.map(eta at H_pi N_e followed by recover_T.map s_pi)). second_unit_iso explicitly asserts its invertibility at that bounded-below etale object. sourceWitness is kappa at H_f N_e followed by j^* s_f. These are exactly q_N,t_N in the DAG proof.
- Witnessed lifts and naturality: source and target are actual functors C(V) -> C(U); source_underlying and target_underlying are equalities of whole functors with j^*G_f and G_pi followed by G_i after forgetting. Thus they constrain the map action for every underlying pro-etale arrow. source_complex/target_complex identify their actual antecedents with Q/B, and source_iso/target_iso identify their witness isomorphism maps with the exact q_N/t_N. HEq only crosses those previously specified object equalities; it supplies no freedom to change the maps.
- Final chart transport: chart : source ~= target is a derived natural isomorphism in the induced category, with every underlying arrow allowed. chart_normalization says q_N followed by its underlying map is C_U(a_N) followed by t_N. Because the recorded witness isomorphisms are invertible, this is precisely t_N C_U(a_N) q_N^{-1}. Its source retains Q and target retains B.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting, Ring, Coefficient and coefficientCommRing; Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison: Scheme.proEtaleSiteComparison and proEtaleSiteComparisonModules. The actual fixed-module functors and derived unit are the public comparisonUpperStar, comparisonLowerStar, derivedComparisonAdjunction from the upstream comparison modules.
- Sheaf.Paper.EtaleOriginDerivedCategory: EtaleOriginDerivedCategory and its forgetful functors; Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness. The former has ring-sheaf endpoints; the latter has exactly the fixed-scalar endpoints needed here.
- WeilConjectures.Compactification.RefinementCategory: Compactification.Refinement and category; Compactification.Defs: Compactification, precomp, copy, hasCompactification. No compactification data are reconstructed by choice.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: rightDerivedLowerShriekOfCompactification. LowerShriekLeftAdjoint supplies isLeftAdjoint_rightDerivedLowerShriekOfCompactification. LowerShriekIndependenceUnbounded supplies rightDerivedLowerShriekIso. adj and chosenAdj use precisely these interfaces.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients records the full higher-coefficient System and publicly retains the finite declaration in Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt: sfFiniteExceptionalAt, used here at finite level. No alternative exceptional functor is defined.
- Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport: sfIntrinsicCompactSupport is the recorded intrinsic Rf_!^c convention. It is read but not needed in the final chart formula, which uses the finite exceptional composite and ordinary etale compact-support adjunctions.
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage: Scheme.proEtaleSheafInverseImage and its module interface; the upstream ProEtale.upperStar is the same fixed-module sheafified Kan-extension inverse image. WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: Etale.upperStar, lowerStar and upperStarLowerStarAdjunction. The open-immersion module supplies openImmersionLowerShriek and the derived ordinary open adjunction used by homChain.
- Mathlib.AlgebraicGeometry.AffineSpace: AffineSpace and its canonical over projection. The coordinate type ULift (Fin d) is in the schemes' universe and includes d=0.
- WeilConjectures.AlgebraicGeometry.DerivedCategories: Etale.DerivedCategoryModule; Mathlib: DerivedCategory.Plus, standard t-structure, InducedCategory, inducedFunctor, Iso.homCongr. All witnesses and comparisons concern derived isomorphisms.
- Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison: openNormalization, closedNormalization, leftComparisonPlus, leftComparison, closedNormalizationAmbient, homChain and exists_homEquiv. The helper and theorem were read in full; only H is restricted to D+ there, so our plusQ/plusIP assertions precede the Yoneda evaluation in the proof plan.
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence: supportSiteComparisonCoefficientPullbackIso, the two canonical identity/composition interfaces, and supportSiteComparison_pullback_coherent. Their actual sheaf normalization is localized by kappa, prId/prComp and etId/etComp.
- Proof imports retain NagataCompactification, etaleInverseImageModulesExact, finiteCoefficientModulePullback_exact, etaleCoefficientSystemAdjoint, comparisonPullbackExact and isIso_compactSupportComparisonUnit, as well as the exceptional coefficient module. The docstrings identify exactly which step each will prove.

Edge cases checked mathematically before writing and while reading the signatures: n=1 uses level_pos and no division; d=0 uses Fin 0 and the identity affine-space projection; zero input and zero morphisms remain available in the full induced category; empty schemes and the empty affine chart impose no nonemptiness, dimension maximum or selected point; identities and two successive opens are explicitly quantified; witnesses need not be constructible; arbitrary cohomological lower bounds are retained; X may be nonseparated over k. The coefficient universe is u+1 for Scheme.{u}; no site universe equality was added.

Searches for existing notions/statements:

1. msearch.py leanfinder: "Open restriction of exceptional inverse image with retained etale origin witness and normalized affine chart Hom chain". Eight hits, read: normalizationDiagram, toNormalization_app_preimage, iota_toNormalization, fromNormalization_preimage, normalizationDiagramMap, iota_fromNormalization, Scheme.Etale and normalizationOpenCover. These concern scheme normalization and sites, not this statement.
2. msearch.py loogle: "CategoryTheory.Adjunction.rightAdjointUniq". Twelve hits: generic right-adjoint uniqueness and its reflexive, component, counit, unit and transitivity laws. These support uniqueness in general but do not state the witnessed chart comparison.
3. msearch.py grep: "witnessed.*[Cc]hart|[Cc]hart.*[Aa]djoint|[Ee]taleOriginDerivedCategory". No Mathlib hits.
4. msearch.py leansearch: "derived category bounded below etale origin open restriction exceptional inverse image normalized affine chart". Eight hits, read: affineOpensRestrict_symm_apply_coe, fromNormalization_preimage, HasDerivedCategory.standard, SheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict, Scheme.Modules.restrictFunctorIsoPullback, morphismRestrict, LocallyRingedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict, and Scheme.restrictFunctorGamma_inv_app. No exact match.
5. rg on the upstream WeilConjectures and project Sheaf sources for witnessed/Witnessed, etaleOrigin/EtaleOrigin, chartAdjoint/ChartAdjoint and openChart/OpenChart; exact blueprint-id search on both trees has no declaration match. Read the upstream finite exceptional definitions, UpperShriekComposition and the existing chart-Hom theorem. The upstream statements forget retained witnesses, or give composition for exceptional functors, and do not jointly supply the open lift, normalized chart Hom chain and two explicit units of this node.
6. Project reuse check: TrfWitnessedOpenPullback states only the retained pullback and open-extension comparison and assumes separated trace-formula schemes; it does not state this ordinary etale chart isomorphism or its transport on arbitrary D+ witnesses. It cannot replace this item. The new fixed-coordinate category is an interface repair of the existing notion, not an independent new node; its category is the existing InducedCategory on the existing FixedEtaleOriginWitness.

No STATEMENT-DISPUTED flag or source correction is needed.

## Dependency modules

`def-sf-etale-origin-subcategory`: Sheaf.Paper.FixedEtaleOriginDerivedCategory publicly imports the original module and the existing fixed-coordinate witness. The recorded original category is induced from FiniteCoefficientDerivedCategoryPlus, whose objects are modules over the continuous-function coefficient sheaf. The ordinary chart theorem and the recorded finite exceptional composite have the fixed-scalar Sheaf (ModuleCat A) endpoints. The repair defines the same sigma of a D+ underlying object and its complete retained witness in that presentation, with the same induced arrow category and canonical forgetful functor. It changes only this dependency's lean record, retaining all six Q19 declarations and adding the two fixed-scalar declarations (eight in total). The original EtaleOriginDerivedCategory, etaleOriginForgetfulPlus, etaleOriginForgetfulPlusFullyFaithful, etaleOriginForgetfulPlus_essImage, etaleOriginForgetful and restrictToEtaleOrigin are publicly imported without alteration. Both new definitions have real data, and no arbitrary map, equivalence or Nonempty choice is introduced. The item's two main statements consume the repaired interface directly.


## New nodes

`def-sf-etale-chart-hom-chain` records the six already-published definitions in
`Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison`, with `existing: true`:
`openNormalization`, `closedNormalization`, `leftComparisonPlus`, `leftComparison`,
`closedNormalizationAmbient`, and `homChain`. It introduces no duplicate Lean module.
Its statement follows the actual definitions: finite commutative coefficients, open s/v,
closed i, separated finite-type f/p, quasi-compact s/v, compactifications and the equation
sf=ipv; three specified ambient right adjoints and their adjunctions; a D+ test object H
and arbitrary ambient K. The six construction clauses specify both normalizations,
the canonical compositor, its ambient value, ambient closed normalization, and the
seven-equivalence forward chain. No existence/naturality theorem or representing-object
conclusion is asserted. The source is the chart adjunction of blueprint
thm-pur-general-admissibility Step 1 and its ordinary etale expansion.

Searches for this node: `msearch.py leansearch` with query "canonical ordinary etale chart
Hom adjunction chain compact support open closed normalization" returned eight scheme
normalization declarations; `leanfinder` with query "Hom equivalence for etale exceptional
adjoints along a factored open closed chart" returned eight manifold-chart declarations;
`grep` with query `homChain|leftComparisonPlus|closedNormalizationAmbient` returned no
Mathlib hits. The new node stores the actual result names. `rg` in WeilConjectures finds
only unrelated private Koszul lemmas; `rg` in Sheaf finds these six definitions in their
published module and unrelated private boundary-chain lemmas. DAG searches find them
recorded only on the chart theorem, and `blueprint_refs.py search "Hom chain"` returns
zero blueprint nodes. Thus the definition node reuses the existing construction and
records its proper ownership, without creating a second definition.

The already-landed `def-per-site-comparison-pullback-data` is reused directly, not
redelivered. Its existing record includes supportSiteComparisonCoefficientPullbackIso,
supportSiteProEtaleComparisonId/Comp and supportSiteEtaleComparisonComp in exactly the
module already publicly imported by the item. Its statement explicitly specifies the
adjunction-mate construction and the identity/composition identifications, with no
coherence assertion. A second new node for those definitions would duplicate that node.

## Returned points repaired

L1: removed lem-sf-etale-chart-adjoint-comparison and lem-weil-pbc-comparison-pullback
from the returned packet's added statement dependencies. Neither was on the live
item's original stmt_deps. Added def-sf-etale-chart-hom-chain and the existing
def-per-site-comparison-pullback-data. The two theorem nodes remain unchanged proof
dependencies, since their conclusions supply naturality/coherence in the proof.
The item uses the exact same canonical definitions and Hom-chain normalization.

L2 / H13: the category dependency's lean.declarations now contains the six old plus
two new public declarations. I read the live F9 node
lem-sf-refinement-comparison-witness-comp and its full statement: its O remains
EtaleOriginDerivedCategory X Lambda with precisely its finite/discrete hypotheses.
The repaired module publicly imports that unchanged original category and all five
old companion interfaces. Its primary fixed-scalar declaration and the two new
signatures remain as in the previously compiled packet. No citer is edited, and
no old interface is dropped.

Repair self-check: re-read both item theorem signatures and ChartTransportData against
the complete node. Open exactness/lower bounds and the identity/composite witness
clauses are unchanged; chart hypotheses and Q/B bounds are unchanged; normalization
and uniqueness of a, both comparison units, all underlying-arrow functor equations,
and q_N/t_N normalization remain unchanged. The original empty-chart, d=0, n=1,
nonseparated-X and arbitrary bounded-below witness checks still apply. The new
Hom-chain node likewise permits empty schemes, zero H/K/ring, identity opens and
unbounded K, as do the six published definitions it records. This repair changes
dependency ownership and preserves the old category interface; it changes no
mathematical assertion.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
