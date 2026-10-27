## Worker report

The module `Sheaf.CategoryTheory.EvaluationBidualComparisonTransport` states
`CategoryTheory.MonoidalClosed.evaluationBidualComparisonTransport`, with its whole proof
`sorry`. Its only helper, `evaluationDualComparison`, constructs the actual isomorphism
`asIso β ≪≫ (ihom (F.obj K)).mapIso w`. The data and inverse are existing constructions;
no map is chosen from an unspecified existence assertion. Both declarations belong to this
node. No new nodes, dependency repairs, or statement correction are needed.

Source read: the node's complete nine-step proof and the final paragraph of
`literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-rf-shriek-preservation/lem-weil-finite-duality-site-comparison.md`.
This is the source snapshot explicitly recorded by the node (it has no blueprint_update).
The paragraph defines the Hom comparisons by evaluation, identifies their double-dual
transposes and transports duality along the constructible equivalence. The theorem's
docstring gives the nine formal steps in full.

Hypotheses and constructions, clause by clause:

- Locally small categories C and C': independent `C : Type u`, `C' : Type u'`,
  `[Category.{v} C]`, `[Category.{v'} C']`. The four universes are explicit and independent.
- Symmetric monoidal closed structures: `[MonoidalCategory C]`, `[MonoidalClosed C]`,
  `[SymmetricCategory C]` and the corresponding three structures on C'. Internal Homs
  are the existing `MonoidalClosed.internalHom`, with the adjunctions `ihom.adjunction`.
  Mathlib takes left tensor as its left adjoint. The node's right-tensor adjunction is
  obtained by symmetry, with no additional assumption and no change to the Hom objects.
- Strong symmetric monoidal functor: `F : C ⥤ C'` with `[F.Braided]`, which extends
  `F.Monoidal` and `F.LaxBraided`. Thus the tensor and unit comparisons are specified
  isomorphisms satisfying associativity, unitality and symmetry coherence.
- Chosen dualizing objects and comparison: `{W : C}`, `{W' : C'}`, `w : F.obj W ≅ W'`.
  Neither object is assumed invertible or dualizing on the entire ambient category.
- D and D' are `internalHom.flip.obj W` and `internalHom.flip.obj W'`. Their object
  values are `(ihom K).obj W`; their maps are `(pre f).app W`.
- Evaluation in the node's order DK tensor K is
  `(β_ ((ihom K).obj W) K).hom ≫ (ihom.ev K).app W`. The specified double-dual map is
  the existing `toIhomIhom W K`, defined as the left-tensor transpose of precisely
  this composite. Equivalently it is the right-tensor transpose of evaluation with
  the factors interchanged, as in the node and lem-weil-duality-pairing.
- Replete full subcategories: `B : ObjectProperty C`, `B' : ObjectProperty C'`,
  `[B.IsClosedUnderIsomorphisms]` and `[B'.IsClosedUnderIsomorphisms]`.
  Their full subcategories are `B.FullSubcategory` and `B'.FullSubcategory`.
- D preserves B: `hD : ∀ K : C, B K → B ((ihom K).obj W)`.
- F restricts to an equivalence: `hF` records that F maps B into B'; the instance
  `(B'.lift (B.ι ⋙ F) (fun K ↦ hF K.obj K.property)).IsEquivalence` states that this
  exact restriction is an equivalence. This imposes no ambient equivalence.
- Canonical beta: `(Functor.LaxMonoidal.ihomComparison F K).natTrans.app W` is the
  existing mate of the tensorator. `ihomComparison_app_eq_curry` and `ihomComparison_ev`
  characterize it by pulled-forward evaluation. It is not an arbitrary chosen map.
  `hβ : ∀ K, B K → IsIso ...` assumes its invertibility only for objects in B.
- c is `evaluationDualComparison F w K (hβ K hK)`, composing exactly beta and H'(1,w).
  The helper's `.inv` is its specified inverse, used contravariantly below.

Conclusions, clause by clause:

- `∃ hD' : ∀ P : C', B' P → B' ((ihom P).obj W')` says D' preserves B'. It provides
  the preservation proof needed to type the restricted target dual functor.
- The first conjunct supplies a natural isomorphism between the actual restricted
  functors `B.liftDual D hD ⋙ F_restricted` and `F_restricted.op ⋙ B'.liftDual D' hD'`.
  The equality of its component's underlying `.hom` with `evaluationDualComparison...hom`
  fixes every component to c_K. Thus naturality is for the specified comparison,
  rather than merely for some isomorphism between the same functors.
- The next conjunct, quantified over every `(K : C) (hK : B K)`, contains both equations.
  Its first equation is `(c_K.hom ⊗ₘ 𝟙 FK) ≫ ev' = μ F DK K ≫ F.map ev ≫ w.hom`.
  This restores exactly the monoidal identification suppressed in the node.
- Its second equation is `toIhomIhom W' FK = F.map (toIhomIhom W K) ≫ c_DK.hom ≫
  (pre c_K.inv).app W'`. The comparison at DK uses `hβ DK (hD K hK)`, so no comparison
  outside B is presumed. `pre c_K.inv` is exactly the contravariant D'(c_K inverse).
- The last conjunct retains BOTH conditional assumptions: `IsEquivalence` of the
  source restricted dual, and invertibility of every specified source `toIhomIhom`.
  It concludes `IsEquivalence` of the target restricted dual AND invertibility of
  every specified target `toIhomIhom` on B'. The source anti-equivalence assumption,
  though redundant given invertible biduality, has not been removed.

Dependency declarations and exact source signatures read:

- def-nagata-category: `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic`, extending `CategoryStruct` with category laws.
  This node is a Mathlib leaf; its `mathlib_match` supplies the declaration.
- def-sfb-monoidal-category: `CategoryTheory.MonoidalCategory` in
  `Mathlib.CategoryTheory.Monoidal.Category`, including the tensor bifunctor, unit,
  associator, unitors, pentagon and triangle. This is also a Mathlib leaf.
- lem-weil-duality-pairing: `Sheaf.Paper.DualityPairing`, publicly imported. Read
  `CategoryTheory.dualityDoubleFunctor`, `DualityPairingCompatibility`, both site
  `AmbientDualityPairing` definitions, and `AlgebraicGeometry.Etale.ambient_duality_pairing`.
  The geometric theorem concerns the specified ambient etale/pro-etale dualizing objects;
  this item uses its formal evaluation-transpose normalization. For general categories
  that construction already exists upstream as `MonoidalClosed.toIhomIhom` in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`; it is used directly,
  not copied or postulated. No geometric hypotheses are added to this formal lemma.
- Canonical beta, its defining curry equation and evaluation equation:
  `Functor.LaxMonoidal.ihomComparison`, `ihomComparison_app_eq_curry`, `ihomComparison_ev`
  in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`.
- Restriction of the contravariant functors: `ObjectProperty.liftDual` in
  `WeilConjectures.CategoryTheory.ObjectProperty.Duality`; its complete definition and
  `liftDualEquivalence` were read. The latter gives the final quasi-inverse construction
  in the proof plan, rather than an assumption about the ambient categories.

Edge cases checked before writing: empty full subcategories (restriction equivalence
forces the target full subcategory empty, all object clauses vacuous); full subcategories
consisting of a zero object when available (no nonzero or nonempty assumption); identity F
and identity w (the two equations reduce to their canonical normalizations); arbitrary
coefficient isomorphism w (retained in c and the evaluation equation); DK in B by hD
exactly where c_DK is needed; lack of ambient equivalence or ambient biduality (neither is
assumed); noninvertible ambient delta away from B; and independent object/morphism
universes on both sides. The result does not require additive or triangulated structure.

Searches actually run:

- msearch leanfinder, "A strong symmetric monoidal functor transports evaluation and the
  canonical double dual map relative to a fixed dualizing object along equivalences of
  replete full subcategories": eight hits, principally `hasRightDualOfEquivalence`,
  `exactPairingOfFaithful`, `rigidCategoryOfEquivalence`, `MonoidalClosed.ofEquiv`.
  These concern rigid duals or an ambient equivalence, not this whole statement.
- msearch loogle, `CategoryTheory.MonoidalClosed.toIhomIhom, CategoryTheory.Functor.Monoidal`:
  zero hits, unknown identifier `CategoryTheory.MonoidalClosed.toIhomIhom` (the service
  indexes Mathlib, whereas this name is upstream). Recorded as unavailable for that name;
  it is not evidence that the construction is absent.
- msearch grep, `ihomComparison|toIhomIhom|bidual|expComparison` in CategoryTheory/Monoidal:
  five hits for `expComparison`, `expComparison_ev` and `coev_expComparison` in
  Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean. That interface is cartesian-closed.
- msearch leansearch, "A symmetric monoidal functor preserves the canonical evaluation
  transpose double dual map relative to a dualizing object on full subcategories": eight
  hits, including `Functor.Monoidal`, `Functor.CoreMonoidal`, and rigid-functor-category
  declarations; none states the item.
- rg in upstream and Sheaf for bidual, double-dual, internal-Hom comparisons, and the
  node id found the existing generic comparison and double-dual constructions listed
  above. A second search for `map_toIhomIhom|toIhomIhom.*map|ihomComparison.*toIhomIhom|
  [Bb]idual.*[Tt]ransport|[Ee]valuation.*[Tt]ransport|[Cc]omparison.*[Bb]idual` found
  coefficient/site-specific statements, not the generic restricted-equivalence lemma.
  Read `EtaleTwistedBidualTransport` and `FiniteDualitySiteComparison`: the former
  cancels a shifted invertible factor in a geometric pullback, and the latter specializes
  the site comparison. Neither is an exact existing declaration for this item.
- The chosen declaration names and node id were searched in upstream, Sheaf and
  dag/lean_names_upstream.json; no existing declaration of this item was found.

The first server compile passed in both sandbox and library mode without warnings.
The final file is compiled again after the explicit restricted-natural-isomorphism and
public-import adjustment. The final dry run and delivery also compile this same file.
No STATEMENT-DISPUTED finding or node fault was found. The natural-language node and all
fields other than `lean` are unchanged.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
