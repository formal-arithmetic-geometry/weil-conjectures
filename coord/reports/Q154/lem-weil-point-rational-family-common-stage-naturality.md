## Worker report

This delivery states `WeilConjectures.PointRationalFamily.rational_family_common_stage_naturality`
in `Sheaf.Paper.PointRationalFamilyCommonStageNaturality`. Its sole theorem has `sorry` as its
whole proof. The helper definitions name the recorded pullback, comparison composites, finite-stage
actions, scalar transport and component prescriptions, under the fresh namespace
`WeilConjectures.PointRationalFamily`. All have real data. The mathematical statement and
proof are unchanged. The two landed dependencies requested by return R2 are now recorded.
No new nodes or dependency modules are needed; return R1 explicitly permits helpers in
the item's own module under a fresh namespace.

Source read: the local Deligne Weil II PDF, printed pp. 150–151, (1.1.3) and (1.1.7), extracted
with pdftotext. The former specifies rational Hom tensors and the coefficient 2-limit; the
latter provides point-transport context. Also read the current main-20261015 blueprint
`sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-weil-global-geometric-frobenius.md`.
The normalized same-stage argument is correctly described as agent-written, not a theorem
ascribed to Deligne. Its four proof steps are reproduced in the theorem docstring.

Hypotheses and notions, clause by clause:

- Global p,a,q,k₀,k: `D : FiniteFieldDatum.{u}`; prime ell: `l : ℕ`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`; algebraic closure: `Ω : Type u`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`. A common containing universe is used as in the recorded
  point-fibre interface; finite coefficient fields use its canonical Shrink models.
- The point is literally `Spec (.of D.k)`; its automorphism is the morphism `g` with
  `[IsIso g]`. The wrappers defined here supply the residue-field invertibility proof from
  ell ≠ p, rather than adding an invertibility hypothesis.
- Integral and raw rational categories are the recorded `sfIntegralConstructibleCategory`
  and `sfRationalConstructibleCategory`; the latter has the integral objects and raw Hom
  localization, with no Karoubi completion. Their sheaf categories use the small ProEt site.
- `rationalPullback`, `commonPullback`, and `pullbackObject` are wrappers around
  `rationalDerivedPullback`, `commonStageDerivedPullback` and its literal object formula.
- `pointRationalFibre`, `pointStageFibre`, and `pointQbarFibre` are the specified sections
  functors. `pointStageFibre` includes only the recorded Shrink-to-subfield scalar transport.
- `RationalFamily` is a natural transformation F_E ⇒ P_E ⋙ F_E at EVERY finite stage;
  its naturality covers every rational morphism, not just integral tensor generators.
- `rationalB` is exactly `F_L.mapIso(alpha.symm) ≪≫ phi.app(P_E K)`; `alpha` is
  `rationalPullbackScalarComparison` and `phi` is `pointRationalFibreScalarIso`, each fixed
  by the rationalization specification in the dependency declarations. No comparisons
  are free variables and no different pullback or fibre is introduced.
- `ht : RationalCompatible ... t` is the given scalar equation, written with Lean's
  left-to-right composition: t_L ≫ b = phi ≫ T(t_E).
- `hunit` says b_E,E followed by the ordinary tensor unit equals H_E applied to the source
  scalar unit. Its HEq compares only the canonical endpoint identifications.
- `htower` says H_N(a_C) ≫ b_E,N = b_L,N ≫ T_N/L(b_E,L) ≫ a_D, on the actual small
  coefficient-field models. The final direct coefficient map is the composite inclusion,
  canonically equal to the direct inclusion by coefficientInclusion_laws. The comparison
  on point complexes is `pointFibreFdTensorTower`, itself the restricted fieldScalarTower.
- `hactions` first identifies both actual common-stage functor maps with `fibreClass` and
  `pullbackClass`. Their representatives are exactly `fibreArrow` = phi inverse ≫ F(f) ≫ phi
  and `pullbackArrow` = b inverse ≫ H(f) ≫ b, using `stageB` with the specified source
  transition identifications. Its last two clauses state their scalar transport formulas
  for every N ≥ L, with `StageSystem.tr` on the source and `pointTransport` on the target.
- Literal source and target are `generalAlgebraicallyClosedConstructibleCategory` and
  `DerivedCategory.PointFdQbar`, not arbitrary categories. The existing target uses its
  canonical realization whose Hom-colimit characterization is
  `pointFdQbarCocone_isFilteredTwoColimit`; no faithfulness hypothesis is added.
- `componentAt` is T_L/E(t_E,K), including the existing coefficient identification and the
  prescribed units. `stageComponent` is the t_E,K representative before this extension.

Conclusions, clause by clause:

- The first outer conjunct quantifies over every A,B,L,hA,hB and actual representative f.
  `rationalFamilyNaturalityLeft = rationalFamilyNaturalityRight` means
  A_L(f) ≫ t_B^L = t_A^L ≫ B_L(f). This is precisely the symmetric form of the displayed
  B_L(f)t_A^L = t_B^L A_L(f), in the full subcategory of D(L), before taking classes.
- Its nested N,h clause identifies the pointTransport of EACH side with the corresponding
  side for `StageSystem.tr h f`. The universally quantified same-stage clause at N also
  supplies their equality there. Thus this records the transported equality itself.
- The second outer conjunct assumes equality of the two source mkHom classes. It returns
  a common finite N and inclusions from both original fields, equality of their source
  transports, and identical left and right sides at N. HEq permits only the propositionally
  equal bounds on the same finite-stage endpoints; it is not equality only in the colimit.
- The final existential returns a natural transformation between the actual pointQbarFibre
  and commonPullback ⋙ pointQbarFibre. `CommonNormalized` fixes every component to the stage
  inclusion of stageComponent, namely [E,t_E,K] with the prescribed tensor units.
- No IsIso hypothesis on t, no injectivity assumption on any coefficient transition,
  and no integral transformation, normalization, or lift occurs in the signature.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: recorded coefficient rings and
  `Padic.finite_coefficientExtensionRing` (background coefficient convention).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and topology.
  The scheme-morphism-properties dependency is explicitly a convention, with no own symbol.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its full subcategory.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalScalarExtension` and raw scalar localization.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalPullbackScalarComparison`, `commonStagePullbackComparison`,
  `commonStagePullbackObject`, `commonStageDerivedPullback` and their specifications.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalFibreScalarIso`, `pointStageFibre`, `pointStageFibreScalarIso`,
  `pointQbarFibreObj`, `pointQbarFibre`, `pointFibreFdTensorTower`.
- `Sheaf.Paper.PointFdQbarCategory`: `PointFdQbar`, `pointFdQbarStage`,
  `pointFdQbarStageComp` and the Hom-colimit theorem.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarPullbackCompleted`,
  the prescribed ordinary and completed comparisons and their unit/tower statements.
- `Sheaf.Paper.PointSectionsScalarExtension`: `pointSectionsScalarExtension`,
  `pointRationalSectionsScalarExtensionIso`, including its six coherence clauses.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Stage`, `stageSystem`,
  `generalAlgebraicallyClosedConstructibleCategory`, `transport`, `representatives`.
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfRationalScalarUnit`, `sfRationalScalarComp`.
  These only name the source unit and associator already specified in the statement.
- Helpers owned by this item in `Sheaf.Paper.PointRationalFamilyCommonStageNaturality`:
  RationalFamily, RationalCompatible, rationalPullback, rationalB, commonPullback,
  pullbackObject, stageB, stageComponent, componentAt, fibreArrow, pullbackArrow,
  fibreClass, pullbackClass, pointTransport, CommonNormalized (also pullbackComparison
  and pointClass). These are the real canonical composites, not arbitrary comparison data.
- `Sheaf.Paper.PointFibreDerivedTensorBasic`:
  `WeilConjectures.finiteFieldSpecCoefficientPrimeInvertible` supplies the unique
  residue-field invertibility proof forced by ell ≠ p.

Repair of the independent return at immutable head 330b19f779fc:

- R1: removed the public import of `Sheaf.Paper.PointTransformationCoefficientDescent`.
  The 17 helper definitions are now in this item's module under the fresh namespace
  `WeilConjectures.PointRationalFamily`; both displayed-side definitions and the theorem
  also use that namespace. The return expressly allows this owning-module arrangement,
  as in the landed sibling `PointCompositeComparisonTower`. Every helper is listed in
  `lean.declarations` and has this item's blueprint/source docstring. Their bodies are
  precisely composites of the recorded dependency constructions; no helper calls the
  downstream coefficient-descent theorem. The downstream module can therefore import this item for its stage-3 proof without
  closing the former cycle. No live module was edited.
- R2: added `lem-weil-scalar-extension-composition` to `stmt_deps` for
  `sfRationalScalarUnit` and `sfRationalScalarComp` in `hunit` and `htower`, and added
  `def-sf-point-fibre-tensor-system` for `finiteFieldSpecCoefficientPrimeInvertible` in
  the pullback/comparison wrappers. Both nodes already have landed Lean records. This is
  permitted by `coord/brief-stage2.md` §5 and `coord/STATE.md`, “STMT_DEPS MAY GAIN LANDED
  NODES”; no statement correction or definition-node duplication is needed. The former
  supplies the canonical source tensor associators, and the latter supplies the proof
  that ell ≠ p makes ell invertible at every residue field of s. Their source declarations
  and docstrings were reopened for this repair.

Edge cases checked on paper and against the definitions: t=0; noninvertible t; zero or
torsion-derived objects; E=L; N=L; both representatives already over the same field;
g=id; unequal original fields with common compositum. Only comparison isomorphisms are
cancelled. Equality is always pushed forward, never reflected. The stage poset includes
repeated fields. The fixed s is nonempty by its field datum; there is no extraneous empty
scheme hypothesis. No counterexample, ambiguity or node correction was found.

Searches: msearch.py leanfinder, query “Scalar compatible rational point natural
transformations descend to common stage coefficient categories with naturality over each
representative field”, returned 8 unrelated sheaf scalar/naturality lemmas. Loogle
`CategoryTheory.NatTrans.naturality` returned 9 elementary category lemmas. Mathlib grep
`commonStage.*[Nn]at|[Nn]at[Tt]rans.*[Cc]olim` in CategoryTheory returned 15 unrelated
colimit/abelian hits. LeanSearch query “Compatible natural transformations descend to a
common stage category with naturality before the colimit” returned 8 ordinary colimit-map
lemmas. Project rg for RationalFamily/common-stage naturality found the downstream helper
module, whose helper bodies were read for the returned repair, but its theorem requires
an integral family
and does not state this arbitrary rational-family implication. rg for the item id in
WeilConjectures and for all three new names in Mathlib, WeilConjectures, Sheaf and the upstream
name index found no exact statement or name collision. Search outputs are in searches.jsonl.

Validation: the saved packet was dry-run first, as dispatched. The repaired owning-module
version is compiled with scompile.py and then checked by the prescribed deliver2.py dry
run; only the node theorem has a sorry proof. Validation results are recorded below.

## Second reading by Q154

This is the author's second reading, not an independent review; the dispatched brief forbids
starting other agents and reserves independent review for the maintainer. I reopened the
node and the final file. The input is the universally supplied rational NatTrans family,
not an existentially rationalized integral family. The specified b has the correct inverse
alpha direction, hunit and htower compare the prescribed source and point associators,
and hactions gives both representative formulas and every transport formula. The original
L is universally bound before f; no passage to a larger field is hidden in its naturality
equality. The second conjunct retains the common N and identical sides, rather than only
equality in the target category. CommonNormalized fixes all descended components. The two
new definitions contain only the required composites; the sole sorry is the node theorem.
The fresh-namespace helper bodies were compared with the accepted formulas: rationalB
still uses alpha inverse, stageB includes the specified stage comparisons, pointTransport
uses the same tensor tower, and CommonNormalized fixes the same finite-stage class. Their
new ownership removes the downstream theorem-module import. The two added dependencies
are the exact landed sources of the unit/tower and invertibility declarations. No binder,
conclusion or mathematical proof step changed; only helper ownership, the theorem's
namespace and the two requested dependency records changed. No downstream theorem is
invoked, and all helper definitions have actual data.

Repaired-file validation (2026-10-22): scompile.py exited 0, compiling the module
separately at both the sandbox module name (37.3 s) and its delivered library name
(32.1 s), with no errors or unexpected warnings. All 20 declarations are recorded;
the theorem signature is verbatim; exactly one sorry remains. A recursive local
project-import check found no path to PointTransformationCoefficientDescent. The node
delta is only lean plus the two requested landed stmt_deps.
