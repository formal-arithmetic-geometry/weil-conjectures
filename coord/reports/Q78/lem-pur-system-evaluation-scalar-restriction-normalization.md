## Worker report

The module `Sheaf.CategoryTheory.SystemEvaluationScalarRestrictionNormalization` states
`SheafOfModules.systemEvaluationScalarRestrictionNormalization`. Its proof is the only
`sorry`. The accompanying definitions construct actual restriction functors, localization
identifications, the singleton Hom comparison, and the ordinary/derived mate words. No
source or node statement was corrected. No new DAG node or dependency repair is needed.

The main objects and hypotheses are rendered as follows.

| Node data | Lean rendering |
| --- | --- |
| Sites small relative to the module universe | `C : Type u`, `Category.{v} C`, `D : Type u'`, `Category.{v'} D`, topologies `J`, `K`, and `EssentiallySmall.{w} C/D`. Object and morphism universes are independent; coefficients and sheaves of sets are w-valued. The sheafification and locally-bijective instances are the existing module-category size infrastructure. |
| Geometric morphism, without a site-functor presentation | `uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))`. |
| AY and AX = inverse image of AY | Commutative ring sheaves `AY`, `AX` and `IA : AlgebraicInverseImage uTop.inverse AY AX`. Its ringUnderlying, operations, modules and moduleUnderlying identify the actual inverse-image ring/module structures. |
| BY, BX with pulled-back transitions | `BY/BX : ℕᵒᵖ ⥤ Sheaf ... CommRingCat.{w}`, algebraic lifts `IB n`, and `htransition`, the equality of the pulled-back coefficient-transition square. |
| Compatible constant-AY algebra and its pullback | Natural transformations `aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY`, `aX` on X, and `halgebra`, the equality of their inverse-image ring squares. Naturality of aY/aX includes all transition compatibility. |
| Exact system and level inverse images | The recorded `SystemGeometricInverseImageData` representatives `FB`, `FA`. Their fields fix the underlying geometric inverse image, evaluations and actual transitions. `FA` uses constant sequences and the constant family `fun _ ↦ IA`. |
| Normalized singleton adjunctions and c_n | `SY/TY`, `SX/TX` are the dependency's scalar/tensor assignments; `systemSingleDerivedExtension` supplies the actual singleton and its adjunction. `hFB/hFA : SystemSingletonGeometricComparisons ...` carry all the representative, multiplication and lower-singleton normalizations. `systemNormalizationSingleton` selects the comparison from this full specification. The representative equation on a resolving class determines it up to equality. |
| Ordinary module-induced geometric adjunctions | Ordinary additive direct images `HB`, `HA`, `Hn n`, `H0`, with adjunctions `adjB`, `adjA`, `adjn n`, `adj0` to these exact module inverse images. A right adjoint to the specified ordinary inverse image is its induced module direct image, uniquely as an adjoint pair. No separate arbitrary derived adjunction is supplied. |
| Ordinary unbounded derived categories and the named direct images | `DerivedCategory (StrictRingSystem ...)`, `DerivedCategory (systemLevel ... n)`, `HB.rightDerivedFunctor`, `HA.rightDerivedFunctor`, `(Hn n).rightDerivedFunctor`, and `H0.rightDerivedFunctor`. `mapDerivedCategoryRightDerivedAdjunction` derives the ordinary module adjunctions. The K-injective-resolution instance parameters are the standard existence infrastructure for these Grothendieck module categories, not preservation by evaluation. |
| U_T and r_T,n | `systemNormalizationRestriction aT` transports the recorded sequence-site `singletonSequenceRestriction aT` across `strictSystemSequenceEquivalence`; `singletonLevelRestriction aT n` is precisely the dependency's actual restriction of scalars. Explicit instances transport their existing additivity and exactness. |
| Ordinary restriction/evaluation identifications | `systemNormalizationRestrictionEvaluation aT n`, composed from `singletonRestrictionEvaluation` and the equivalence unit; its localization is `systemNormalizationDerivedRestrictionEvaluation`. |

The conclusions and their canonical normalizations are rendered clause by clause.

1. `systemNormalizationEvaluation ... hFB n` defines beta_B by the actual
   `conjugateIsoEquiv` of `c_n.symm` under the two composite singleton/geometric
   adjunctions. The theorem's quantified Hom equation spells out the three Hom
   transposes in the node for every V, Z and test map f. This fixes the comparison,
   rather than asserting unrelated isomorphism of its evaluated objects.
2. The existential `d : SystemNormalizationSquares ...` CONSTRUCTS the canonical
   ordinary scalar/inverse-image and transition-restriction squares. Its level and
   restriction underlying-sheaf equations fix their maps as identity on inverse images.
   Its scalarEvaluation equation fixes the whole-system scalar square using the actual
   evaluation/restriction identifications and that normalized level square. These
   ordinary squares are conclusions, not additional assumptions about the geometry.
3. The natural isomorphisms `delta`, `kappa n`, `chi h` are characterized by equality
   with the explicitly defined derived mate words. `UnitNormalized` additionally states
   the comparison-unit equation from the two factorizations in
   `diagramRingRestrictionPushforward` and 0D6E. It is written on the homotopy
   presentation `Qh` of the same localization, with the canonical exact-functor
   factorization isomorphisms included. On cochain complexes it is the recorded
   diagram-comparison equation. Right-derived uniqueness pins delta and kappa to the
   named comparisons in the node. For chi, the equation is for `chi.inv`, matching
   the inverse direction of the coefficient-restriction/direct-image comparison.
4. The constant comparison `systemNormalizationEvaluation ... FA ... hFA n` equals
   the derived mate of `FA.evaluation n` and has its resolution-unit normalization.
   Constant-ring strict systems are the ringed-sequence-site realization of ordinary
   module towers. These equations identify this beta_A with the unique constant-tower
   comparison in `exists_unique_towerDerivedEvaluation_normalized`, including its
   module-induced adjunction, rather than leaving beta_A unpinned.
5. The scalar-square conjunct is, in Lean composition order,
   `rY.map beta_B ≫ kappa = restrictionEvaluationY.inv ≫ eAY.map delta ≫ beta_A ≫
   PA.map restrictionEvaluationX.hom`. The two explicit evaluation/restriction
   isomorphisms are precisely the node's ordinary identifications. Both paths end at
   `PA (rX (eBX Z))`, with the stated common source.
6. The counit conjunct states `eBX.map counitB = FB.derivedEvaluation.hom ≫
   g_n.map beta_B ≫ counit_n`. The initial exact inverse-image/evaluation identification
   makes explicit the node's `e_n^X G_B = u_n^* e_n^Y` identification.
7. The last conjunct is the actual restriction-form transition equation for every
   `h : n ≤ m` and every derived Z:
   `tY ≫ RY.map beta_n = beta_m ≫ Pm.map tX ≫ chi`.
   Here tX and tY are the existing `systemDerivedTransition`, obtained by localizing
   the strict transitions, and both R functors are the existing `systemRestriction`.
8. Beta, delta, kappa and chi are natural isomorphisms of the actual derived functors.
   Quantification over all Z gives the required natural identities. All categories
   are unbounded. No flatness, boundedness, cartesian-system or K-injective-preserving
   evaluation hypothesis appears.

The extra mate and resolution-unit equations specify the comparisons named in the
node; they are included to prevent treating delta, kappa, beta_A or chi as arbitrary
maps. The only classical selection is of c from the dependency's fully normalized
representative theorem, which determines c up to equality. No object is selected from
a merely nonempty collection of uncharacterized data.

Dependency declarations read and used (with the recorded modules):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`; the site
  convention supplies Grothendieck topologies. The size-convention node is explicitly
  metatheoretic and has no declaration to import.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent existing `SheafOfModules` category underlying every `systemLevel`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: `SheafOfModules.restrictScalars`.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`: `strictSystemSequenceEquivalence`,
  `systemSequenceEvaluation`, and the actual coefficient-sequence ring.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: `systemLevelLeftExtensionTheory`
  and its reexported `StrictRingSystem`, `systemLevel`, `systemEvaluation`,
  `systemRestriction`, `SystemScalarAssignment`, `SystemTensorCoherence` interfaces.
- `Sheaf.CategoryTheory.SystemSingleDerivedExtension`: `systemSingleDerivedExtension`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`;
  the geometric/algebraic inverse-image interface used here is the recorded singleton
  geometric dependency's implementation for arbitrary geometric morphisms.
- `Sheaf.CategoryTheory.SystemSingletonGeometricPullback`:
  `SystemGeometricInverseImageData`, `SystemSingletonGeometricComparisons`,
  `systemSingletonGeometricPullback`, and `systemGeometricUnderlying`.
- `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`:
  `diagramRingRestrictionPushforward`, including its two-factorization unit equation.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `ringedToposDerivedPushforwardComposition`, including its K-injective normalization.
- `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`:
  `exists_unique_towerDerivedEvaluation_normalized` and its uniqueness/counit clauses.
- `Sheaf.CategoryTheory.SystemSingletonScalarExtension`:
  `singletonSequenceRestriction`, `singletonLevelRestriction`,
  `singletonRestrictionEvaluation`, and `singletonScalarDerivedIso`/`singletonScalarExtension`
  for the scalar-normalized singleton comparison used in the proof.
- `Sheaf.CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`, the
  ordinary-tower presentation of constant-ring sequence modules.
- Proof imports retain the recorded normalized coefficient adjunction, tensor/adjunction
  two-path comparison, independent-coefficient K-flat resolution, generalized tensor
  pullback, generalized derived pullback, and actual singleton-transition evaluation.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`, `mateEquiv`, and the
  pasting clauses recorded by the two Mathlib-leaf proof nodes.
- Existing upstream functorial localization and exact-left derived-adjunction APIs:
  `Functor.mapDerivedCategorySquareIso` and
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`. No substitute derived category,
  tensor product, module category, evaluation, singleton extension or scalar restriction
  category was introduced.

Edge cases checked before finalizing: n=0 represents the first positive level; h=n≤n
retains the actual identity restriction and its canonical comparison; u=id gives identity
geometric squares; B=constant A makes restriction the identity up to the displayed
canonical identifications; the zero complex and zero ring are included; no step divides
by a coefficient or assumes a nonzero ring. The nonflat map Z→Z/2 is allowed in aY and
in coefficient transitions, and arbitrary unbounded Z remains quantified. No empty
site or universe case is removed by an equality of site universes.

Searches (full wrapper output is retained in searches.jsonl):

- LeanFinder, `Canonical derived evaluation direct image comparison agrees after scalar
  restriction with constant ring tower evaluation`: eight hits, including
  `PresheafOfModules.restriction`, ordinary module scalar counits, and adic-completion
  transitions. None states the singleton-derived scalar normalization square.
- Loogle, `Adjunction.conjugateEquiv, Adjunction.rightAdjointUniq`: zero hits, unknown
  unqualified identifier. Source inspection located the actual Mathlib declarations
  `CategoryTheory.conjugateIsoEquiv` and `CategoryTheory.mateEquiv`; these are used.
- msearch grep, `evaluation.*[Ss]calar|[Ss]calar.*[Ee]valuation`, Mathlib CategoryTheory:
  zero hits. Broader source searches in project Sheaf and WeilConjectures found the
  existing singleton/scalar and semilinear-evaluation components, not this main square.
- LeanSearch, `singleton derived evaluation direct image compatible scalar restriction`:
  eight ordinary restriction/derivation hits, no derived singleton normalization result.
- `rg` of the item id and expected new declaration names in Sheaf, WeilConjectures and
  dag/lean_names_upstream.json: no existing declaration. The prescribed upstream
  `grep -rn` for the item id also returned none. `SemilinearDerivedSections` was read:
  its categorical evaluation_mate and geometric evaluation data do not pin this
  singleton comparison to the scalar-restriction/direct-image comparison.

Sources inspected: Stacks `sites-cohomology.tex`, lemma-derived-pushforward-composition
(Tag 0D6E), including its proof through pullback composition and adjunction; Zheng PDF,
printed pp. 21–23, Construction 4.1 and the paragraph before Lemma 4.10. The general
varying-ring scalar square is the node's explicitly identified agent auxiliary, not
claimed as the literal statement of 0D6E or Zheng's fixed-coefficient lemma.

Validation: prescribed scompile.py checked the complete module in sandbox and module
positions with no errors or warnings. The main theorem remains sorry as required for
stage 2. The initial elaboration timeout was repaired by giving the transported exact
restriction a named typed interface, caching its existing exactness instances, and
using an evaluation square to specify its underlying normalization. The limit stayed
60 seconds; no live source was edited. All new variable and universe binders are explicit.

## Second reading by Q78

A separate pass compared the node, dependency signatures and finished file, following
its three conclusions in order. The scalar square has kappa after rY(beta), with both
ordinary restriction/evaluation identifications explicitly inserted on the other path.
The counit has the correct inverse-image/evaluation identification and the same
module-induced derived adjunctions. The transition comparison has inverse mate direction
`Pn RY → RX Pm`, so chi itself is `Pm RX → RY Pn`, as required. No varying-ring
K-injective evaluation preservation was introduced. Both beta comparisons come from
c inverse; the constant one is additionally fixed by the derived-unit normalization.
The normalization squares are constructed as conclusions and have specified underlying
maps. Checked the zero, identity, diagonal-index, nonflat and unbounded cases again.
This pass found and repaired the constant-family resolution instance binder: it must
be supplied at each level, all definitionally the same module category. No statement
change resulted. The dispatcher's requested independent maintainer review is still the
independent review of this self-delivery; no second agent was started.
