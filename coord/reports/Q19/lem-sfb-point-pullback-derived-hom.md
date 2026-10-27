## Worker report

The module states the unchanged node on ordinary, uncompleted, unbounded derived
categories of internal modules. Its primary declaration is
`AlgebraicGeometry.ProEtale.PointDerivedHom.point_pullback_derived_hom`.
The evaluation-adjoint map is the preceding real definition `comparison`.
No theorem is proved: the three theorem proofs are `sorry`; each has this node's
source, blueprint marker and complete natural-language proof. The exactness and
monoidality instances specialize existing published structures and proofs.

Hypothesis and clause correspondence:

- Any scheme and its small pro-etale site: `X : Scheme.{u}` and `X.ProEt`, with
  `Scheme.ProEt.topology X`. Objects have universe `u+1`, morphisms universe `u`;
  abelian sheaves have coefficients `Ab.{u+1}`. No equality of object and morphism
  universe levels is imposed. Explicit universe parameters and the existing
  Grothendieck/derived-category instances render the size convention.
- Any commutative condensed ring: the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. This is exactly the unbundled form of
  `Profinite.CondensedRing`, not a continuous-function or discrete specialization.
- The condensed-point inverse image: `pull Λ X` is transparently the existing
  `(upperStarFromPoint X).mapMod Λ`. Its underlying sheaf functor is the actual
  left Kan extension/sheafification and scheme inverse image. `pointLimits`
  specializes the existing `profinite_point_pullback` exactness theorem;
  `pointColimits` and `pullLeftAdjoint` use the actual point adjunction.
- The coefficient B is the actual `(upperStarFromPoint X).obj Λ`, definitionally
  `condensedRingObj Λ X`, as in `coefficientRing` and its `coefficientRing_X` clause.
  The module action is the existing `mapMod` action, never an arbitrary structure.
- Internal module categories: `Mod (Sheaf J Ab.{u+1}) Λ` and its pulled-back
  specialization. These use Mathlib `Mod`; no private replacement is introduced.
- Ordinary uncompleted unbounded derived categories: `DerivedCategory` and
  `derivedPull Λ X = (pull Λ X).mapDerivedCategory`. There is no bounded or
  completed subcategory in any signature.
- Derived relative tensor and Hom: the native `Mod.derivedMonoidalCategory` and
  the recorded `DerivedCategory.monoidalClosed` give `⊗` and `ihom`.
  `CondensedRing.derivedHom` is precisely `MonoidalClosed.internalHom` for this
  structure. The K-injective ringed-site description is related to these native
  structures by the recorded module-object/ringed-site and sections-model proof
  dependencies, rather than replacing either with arbitrary tensor or Hom data.
- The canonical tensor comparison is `tensorComparison`, built by `exactTensor`
  from the existing `leftDerivedTensorComparison` and the canonical exact-functor
  identification `leftDerivedFunctorIsoMapDerivedCategory`. Its construction is
  the native K-flat one: transport `F(QK ⊗^L QL) -> LF(QK ⊗^L QL)`, apply the
  existing derived tensorator, and transport each factor to the exact termwise
  derived functor. It is not selected from mere existence. `pullFlat` states
  the ordinary flatness preservation needed for this existing interface, as a
  named postponed theorem with its source and natural-language proof.
- The evaluation transpose defining beta is the real definition
  `evaluationComparison`, specialized in `comparison`: apply the inverse normalized
  tensor comparison to `F(K) ⊗ F(ihom(K,L))`, then `F.map ((ihom.ev K).app L)`,
  then `MonoidalClosed.curry`. The native Mathlib closed adjunction has K on the
  left. The node puts the Hom factor on the left; the symmetric Koszul braidings
  identify the two transpose conventions. Naturality of the actual monoidal tensor
  comparison with these braidings gives precisely the Hom-first map in the node.
  Thus no alternative or arbitrary Hom isomorphism is chosen.
- Isomorphism for every K,L: `ExactPreservesHom` expands through `PreservesHom` to
  `∀ K L : DerivedCategory (...), IsIso (comparison Λ X K L)`, together with
  the following two naturality clauses.
- Contravariance in K: the second conjunct quantifies over every `a : K' ⟶ K`
  and gives the equation with `MonoidalClosed.pre a` and `pre (F.map a)`.
- Covariance in L: the third conjunct quantifies over every `b : L ⟶ L'`
  and gives the equation with `(ihom K).map b` and `(ihom (F.obj K)).map (F.map b)`.
- Every pro-etale test: the last conjunct quantifies over `W : X.ProEt`, including
  the empty test and the identity test. Restriction is
  `(CondensedRing.supportPullback Λ W.hom).mapDerivedCategory`, the existing
  inverse image with inverse-coefficient transport. Weakly-etale localization and
  coefficient-sections localization identify this with the localized ringed site.
- Canonical coefficient/composition identifications: `restrictionComparison` is
  chosen from a unique specification whose component, on underlying sheaves, is
  exactly `(upperStarFromPointComp f).hom.app M.X`. Its termwise localization is
  `derivedRestrictionComparison`, using the existing exact-functor composition
  and natural-isomorphism maps. This excludes arbitrary identifications.
- Canonical restriction of Hom: `restrictionHom` is the explicit evaluation
  transpose using the already recorded `supportDerivedTensorComparison`.
  For each W and the two pulled-back inputs, the last conjunct asserts that this
  comparison is invertible and gives equality of derived morphisms:
  restricted beta, followed by this Hom comparison and transport of its two
  arguments, equals the point-composition comparison followed by beta on W.
  This is an equality in the derived category, not only equality on cohomology.
- No boundedness, finite-generation, dualizability, discreteness or completeness
  hypothesis occurs anywhere. No such condition is hidden in the aliases.

Dependency declarations read and used:

- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale` / `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: metatheoretic convention, rendered by the explicit universes.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing` / `Profinite.CondensedRing`.
- `lem-weil-pbc-profinite-point-pullback`: `Sheaf.Paper.ProfinitePointPullback` / `AlgebraicGeometry.ProEtale.profinite_point_pullback`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` / `AlgebraicGeometry.ProEtale.coefficientRing`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod` / `CategoryTheory.Mod`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` / `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `sk-def-sfb-derived-tensor-hom`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` / `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` / `CategoryTheory.derivedInternalHomOfUniverses`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` / `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `def-pur-localized-ringed-site`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` / `SheafOfModules.overFunctor`.
- `def-sfb-condensed-pullback-tensor-comparison`: `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison` / `AlgebraicGeometry.ProEtale.CondensedRing.supportDerivedTensorComparison`.

All recorded statement dependencies are imported publicly. All recorded, stated
proof dependencies are imported, including the internal-section tensor comparison
on the condensed point and the coefficient-sections localization comparison.
The existing `def-sfb-condensed-pullback-tensor-comparison` is added to stmt_deps
because its canonical `supportDerivedTensorComparison` occurs in the signatures and definitions here. Its node is
already landed; no new definition node or dependency repair is needed.

The helpers belong to this node's canonical evaluation map and restriction clause.
Their data is made from actual existing constructions. The only choice is from
`restrictionComparison_existsUnique`, whose specification fixes the entire ordinary
natural isomorphism by its underlying sheaf map. `uniqueChoice` abstracts selection
from such a unique specification and never chooses arbitrary isomorphisms.


Edge cases checked: empty X and empty W (zero module categories); K=0 or L=0;
identity test W=X; arbitrary shifts and genuinely unbounded complexes; arbitrary
commutative condensed coefficient objects with no topological presentation.
Neither the signatures nor the canonical maps exclude any of these cases.
The statement uses the native left-tensor closed adjunction, so no additional
braiding instance is selected: the symmetric Koszul tensor identifies this with
the right-tensor convention of the source.

For elaboration, the full parallel naturality formulas are in the explicit predicate
`PreservesHom`, and the full restriction equation and restriction-isomorphism clause
are in `RestrictsHom`. They bind every K,L and every map with the variances described
above. The main theorem asserts these predicates for the actual point functors and
actual comparisons, including every `W : X.ProEt`. This abstraction avoids repeated
expansion of the concrete sheaf internal-Hom instances and changes no clause.
The generic `ExactPreservesHom` and `ExactRestrictsHom` specialize those same predicates
to the termwise derived functors of exact functors. `HomComparisonFamily`,
`DerivedCompositionFamily`, `PointCompositionFamily` and
`PointCompositionNormalization` give names to their exact full types and normalization
formula. These names avoid recomputing concrete sheaf structure data during
elaboration; none introduces an assumption or changes a map.


Searches made for an exact existing statement:

- msearch LeanFinder: “Pullback from condensed modules to a scheme pro etale site
  preserves unbounded derived internal Hom”. Eight hits concern ordinary module
  pullback adjunctions and underived light-condensed closedness; none is this theorem.
- msearch Loogle: `"Condensed", "ihom"`. Five hits are the underived
  `LightCondensed.ihomPoints` family, not this derived scheme-point comparison.
- msearch grep: `(pointUpperStar|upperStarFromPoint).*(ihom|internalHom|Hom)`.
  No Mathlib hit.
- msearch LeanSearch: “Condensed point inverse image preserves internal Hom on
  ordinary unbounded derived categories”. Eight hits concern generic inverse-image
  predicates, underived light condensed Hom points, or unrelated injective resolutions.
- Project rg by node id and names `pointDerivedHom`, `pointPullbackDerivedHom`:
  no existing declaration. Concept searches located the native module-object Hom,
  the actual point inverse image, and the specialized w-contractible component
  theorem, all reused rather than restated as an alternative notion.
- Read HRS Proposition 4.3(1), its proof using (4.2), and the factorization (4.1)
  in the local source PDF. The globalization and slice normalization are the
  live node's independently reviewed proof; its natural-language statement is
  unchanged in this delivery.

No statement fault or STATEMENT-DISPUTED finding. All changes are confined to the
worker sandbox.

Validation: scompile.py compiled the complete file cleanly with default limits,
first as the sandbox module (20.2 seconds) and then as
`Sheaf.Paper.PointPullbackDerivedHom` (17.1 seconds). No errors or warnings.
The final file contains no diagnostic commands or diagnostic heartbeat settings.
The successor morphism universe in the generic tensor helper matches the native
derived tensor API; the scheme site and coefficient universes are unchanged.

Delivery dry run: deliver2.py --no-push returned OK; commit 72963420359
passed the server preflight and per-file compilation.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
