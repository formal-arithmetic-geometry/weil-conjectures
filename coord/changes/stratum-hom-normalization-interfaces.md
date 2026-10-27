# AlgebraicGeometry.StratumHomComparisonMate canonical comparison data

## Reason

A new equality lemma needs the existing canonical maps without importing its consumer theorem.
Move the definition interface into StratumHomComparisonData and publicly import it from the
original module; the declaration names and mathematical formulas are preserved. Explicit result
types on the large derived adjunctions and maps, and the irreducible generic normalization
predicate, keep elaboration from unfolding derived constructions at every specialization.
The ordinary adjunction bodies are unchanged and now carry irreducible. HomIso and Normalized
factor through the displayed generic definitions; unfolding those gives their old formulas.
This is an interface extraction needed by the mathematical decomposition, not a split of a
completed proof to evade a compile limit. The discarded all-in-one proof attempt remains in the
sandbox scratchpad. The target signatures are unchanged; review of their meaning is reopened
because their canonical helper definitions moved and the normalization predicate was factored.

## Old

Original file: lean/Sheaf/AlgebraicGeometry/StratumHomComparisonMate.lean.

```lean
namespace AlgebraicGeometry.StratumHomComparisonMate

namespace Etale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.Etale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.Etale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v ≅
      ImmersionProjectionComparison.Etale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :=
  (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.Etale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.Etale.pull A c).obj
        ((ImmersionProjectionComparison.Etale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).op.prod (𝟭 (D A X)) ⋙
      Functor.uncurry.obj (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X) ≅
    (𝟭 (D A S)ᵒᵖ).prod (a.etaleRight v) ⋙
      Functor.uncurry.obj (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S) ⋙
      (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  ∀ (P : D A S) (B : D A X),
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        (χ.inv.app (op P, B))).app
          ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ≫
      evaluation A X ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) B =
    projection A c v
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
          ).rightDerivedFunctor.obj (hom A S P ((a.etaleRight v).obj B))) P ≫
      (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).map
        (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((ordinaryAdjunction A c v).counit.app
            (hom A S P ((a.etaleRight v).obj B)))).app P) ≫
      (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).map
        (evaluation A S P ((a.etaleRight v).obj B)) ≫
      (a.etalePasted v).counit.app B

end Etale

namespace ProEtale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.ProEtale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v ≅
      ImmersionProjectionComparison.ProEtale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :=
  (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.ProEtale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.ProEtale.pull A c).obj
        ((ImmersionProjectionComparison.ProEtale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).op.prod (𝟭 (D A X)) ⋙
      Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X) ≅
    (𝟭 (D A S)ᵒᵖ).prod (a.proetaleRight v) ⋙
      Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S) ⋙
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  ∀ (P : D A S) (B : D A X),
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
        (χ.inv.app (op P, B))).app
          ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj P) ≫
      evaluation A X ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj P) B =
    projection A c v
        ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
          ).rightDerivedFunctor.obj (hom A S P ((a.proetaleRight v).obj B))) P ≫
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).map
        (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((ordinaryAdjunction A c v).counit.app
            (hom A S P ((a.proetaleRight v).obj B)))).app P) ≫
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).map
        (evaluation A S P ((a.proetaleRight v).obj B)) ≫
      (a.proetalePasted v).counit.app B

end ProEtale

/-- The specified D+ direct-image mate in the ordinary unbounded categories.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def directImageMate (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (s : S ⟶ X)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (ImmersionProjectionComparison.comparison A X).map
      ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
        ).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
      ).mapDerivedCategoryPlusCompatibility.inv.app
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
          ).rightDerivedFunctorPlus.obj K) ≫
    DerivedCategory.Plus.ι.map
      ((AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus A s).app K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s
      ).rightDerivedFunctorPlusCompatibility.hom.app
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
          ).mapDerivedCategoryPlus.obj K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
        ).mapDerivedCategoryPlusCompatibility.hom.app K)

/-- Delta with exactly the canonical closed-mate and open-unit normalization.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) :=
  (ImmersionProjectionComparison.comparison A X).mapIso
      ((Etale.extensionIso A c v).app P) ≪≫
    ImmersionProjectionComparison.extensionComparison A c v P ≪≫
    ((ProEtale.extensionIso A c v).app
      ((ImmersionProjectionComparison.comparison A S).obj P)).symm

/-- The contravariant Hom identification induced by the inverse of Delta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def homChange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) (B : Etale.D A X) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X).map
    (extensionComparison A c v P).inv.op).app
      ((ImmersionProjectionComparison.comparison A X).obj B)

/-- The stratum arrow H(1,gamma) after the evaluation-defined comparison beta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def stratumMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X) :=
  AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj) ≫
    ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S).obj
      (op ((ImmersionProjectionComparison.comparison A S).obj P))).map (z.gamma.hom.app M)

/-- The exact equation and all its conditional invertibility clauses at the chosen inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def IdentityAndIsomorphisms (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X)
    (χe : Etale.HomIso A c v z.adjoints) (χp : ProEtale.HomIso A c v z.adjoints)
    (hK : DerivedCategory.TStructure.t.plus
      (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj))) : Prop :=
  (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
      homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj) =
    (ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj)) ≫
      directImageMate A (c ≫ v) ⟨_, hK⟩ ≫
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor.map (stratumMap A c v z P M)) ∧
  (IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj)) →
    IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj) ∧
    IsIso (homChange A c v P M.obj) ∧
    IsIso (χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
      (ImmersionProjectionComparison.comparison A X).obj M.obj)) ∧
    IsIso ((ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj))) ∧
    IsIso (directImageMate A (c ≫ v) ⟨_, hK⟩) ∧
    IsIso (stratumMap A c v z P M) ∧
    IsIso ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
      ).rightDerivedFunctor.map (stratumMap A c v z P M)))

/-- The conclusion for a finite coefficient ring; all auxiliary maps above are canonical data.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Conclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)] : Prop :=
  ∀ (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
    Scheme.IsFiniteLocallyConstantSheaf L →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat A (((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} A)).obj L)) →
    ∀ M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X,
    AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A S
      ((z.adjoints.etaleRight v).obj M.obj) →
    ∃ χe : Etale.HomIso A c v z.adjoints, ∃ χp : ProEtale.HomIso A c v z.adjoints,
      Etale.Normalized A c v z.adjoints χe ∧ ProEtale.Normalized A c v z.adjoints χp ∧
      ∃ hK : DerivedCategory.TStructure.t.plus
        (Etale.hom A S (ImmersionProjectionComparison.single A L)
          ((z.adjoints.etaleRight v).obj M.obj)),
        IdentityAndIsomorphisms A c v z (ImmersionProjectionComparison.single A L) M χe χp hK

```

## New

New file: lean/Sheaf/AlgebraicGeometry/StratumHomComparisonData.lean; the original module
publicly imports it, retaining the original transitive public imports.

```lean
namespace AlgebraicGeometry.StratumHomComparisonMate

/-- The two-variable internal-Hom comparison type.
Source: the stratum tensor-Hom adjunction in the finite-duality comparison proof
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def stratumHomIsoType
    {C D : Type*} [Category C] [Category D]
    (HS : Dᵒᵖ ⥤ D ⥤ D) (HX : Cᵒᵖ ⥤ C ⥤ C)
    (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C) :=
  F.op.prod (𝟭 C) ⋙ Functor.uncurry.obj HX ≅
    (𝟭 Dᵒᵖ).prod G ⋙ Functor.uncurry.obj HS ⋙ R

/-- Evaluation normalization for a tensor-Hom comparison.
Source: the inverse evaluation formula in the finite-duality comparison proof
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
@[irreducible]
def tensorHomNormalization
    {C D : Type*} [Category C] [Category D]
    (TS : D ⥤ D ⥤ D) (HS : Dᵒᵖ ⥤ D ⥤ D)
    (TX : C ⥤ C ⥤ C) (HX : Cᵒᵖ ⥤ C ⥤ C)
    (F : D ⥤ C) (G : C ⥤ D) (L : C ⥤ D) (R : D ⥤ C)
    (a : L ⊣ R) (b : F ⊣ G)
    (evX : ∀ P M : C, (TX.obj ((HX.obj (op P)).obj M)).obj P ⟶ M)
    (evS : ∀ P M : D, (TS.obj ((HS.obj (op P)).obj M)).obj P ⟶ M)
    (proj : ∀ (T : C) (P : D), (TX.obj T).obj (F.obj P) ⟶
      F.obj ((TS.obj (L.obj T)).obj P))
    (θ : stratumHomIsoType HS HX F G R) : Prop :=
      ∀ P M, (TX.map (θ.inv.app (op P, M))).app (F.obj P) ≫ evX (F.obj P) M =
        proj (R.obj ((HS.obj (op P)).obj (G.obj M))) P ≫
          F.map ((TS.map (a.counit.app ((HS.obj (op P)).obj (G.obj M)))).app P) ≫
          F.map (evS P (G.obj M)) ≫ b.counit.app M

namespace Etale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.Etale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.Etale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v ≅
      ImmersionProjectionComparison.Etale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
@[irreducible]
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :
    ImmersionProjectionComparison.Etale.pull A v ⋙
        ImmersionProjectionComparison.Etale.pull A c ⊣
      (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor :=
  (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :
    tensor A X T
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ⟶
      (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj
        (tensor A S ((ImmersionProjectionComparison.Etale.pull A c).obj
          ((ImmersionProjectionComparison.Etale.pull A v).obj T)) P) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.Etale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.Etale.pull A c).obj
        ((ImmersionProjectionComparison.Etale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  stratumHomIsoType
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v) (a.etaleRight v)
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  tensorHomNormalization
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.Etale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v) (a.etaleRight v)
    (ImmersionProjectionComparison.Etale.pull A v ⋙
      ImmersionProjectionComparison.Etale.pull A c)
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor
    (ordinaryAdjunction A c v) (a.etalePasted v)
    (evaluation A X) (evaluation A S) (projection A c v) χ

end Etale

namespace ProEtale

/-- The existing ordinary derived category, in the fixed-scalar presentation.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev D (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The existing K-injective internal Hom, with its contravariant first argument.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) T).obj (op P)).obj B

/-- The existing K-flat tensor, with the ambient factor written first.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev tensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj P).obj B

/-- Right-ordered evaluation, using the canonical signed tensor symmetry.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def evaluation (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (P B : D A T) : tensor A T (hom A T P B) P ⟶ B :=
  ((ImmersionProjectionComparison.ProEtale.symmetry A T).hom.app (hom A T P B)).app P ≫
    (AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction
      (ModuleCat.{u + 1} A) P).counit.app B

/-- Canonical identification of derived closed/open extension with exact termwise extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v ≅
      ImmersionProjectionComparison.ProEtale.extension A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  Functor.isoWhiskerRight
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c
      ).rightDerivedFunctorIsoMapDerivedCategory
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- Ordinary inverse/direct-image adjunction in the factorized restriction coordinates.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
@[irreducible]
def ordinaryAdjunction (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) :
    ImmersionProjectionComparison.ProEtale.pull A v ⋙
        ImmersionProjectionComparison.ProEtale.pull A c ⊣
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor :=
  (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) (c ≫ v)).ofNatIsoLeft
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} A) c v ≪≫
        Functor.isoWhiskerRight
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v) _ ≪≫
        Functor.isoWhiskerLeft _
          (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) c))

/-- The projection arrow of the dependency, transported to the ambient derived extension.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (T : D A X) (P : D A S) :
    tensor A X T
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj P) ⟶
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
        (tensor A S ((ImmersionProjectionComparison.ProEtale.pull A c).obj
          ((ImmersionProjectionComparison.ProEtale.pull A v).obj T)) P) :=
  ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj T).map
      ((extensionIso A c v).hom.app P) ≫
    ImmersionProjectionComparison.ProEtale.projection A c v T P ≫
    (extensionIso A c v).inv.app
      (tensor A S ((ImmersionProjectionComparison.ProEtale.pull A c).obj
        ((ImmersionProjectionComparison.ProEtale.pull A v).obj T)) P)

/-- The type of natural stratum isomorphisms for the specified ambient right adjoint.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
abbrev HomIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X) [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c) :=
  stratumHomIsoType
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v) (a.proetaleRight v)
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor

/-- The displayed inverse-transpose normalization, for all two-variable inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (a : AlgebraicGeometry.ProEtale.LocallyClosedComparisonAdjoints A c)
    (χ : HomIso A c v a) : Prop :=
  tensorHomNormalization
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v) (a.proetaleRight v)
    (ImmersionProjectionComparison.ProEtale.pull A v ⋙
      ImmersionProjectionComparison.ProEtale.pull A c)
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)).rightDerivedFunctor
    (ordinaryAdjunction A c v) (a.proetalePasted v)
    (evaluation A X) (evaluation A S) (projection A c v) χ

end ProEtale

/-- The specified D+ direct-image mate in the ordinary unbounded categories.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def directImageMate (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (s : S ⟶ X)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ImmersionProjectionComparison.comparison A X).obj
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
          ).rightDerivedFunctor.obj K.obj) ⟶
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s
        ).rightDerivedFunctor.obj ((ImmersionProjectionComparison.comparison A S).obj K.obj) :=
  (ImmersionProjectionComparison.comparison A X).map
      ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
        ).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
      ).mapDerivedCategoryPlusCompatibility.inv.app
        ((AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) s
          ).rightDerivedFunctorPlus.obj K) ≫
    DerivedCategory.Plus.ι.map
      ((AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus A s).app K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s
      ).rightDerivedFunctorPlusCompatibility.hom.app
        ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
          ).mapDerivedCategoryPlus.obj K) ≫
    (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
      ((AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S
        ).mapDerivedCategoryPlusCompatibility.hom.app K)

/-- Delta with exactly the canonical closed-mate and open-unit normalization.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def extensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) :
    (ImmersionProjectionComparison.comparison A X).obj
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) ≅
      (AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
        ((ImmersionProjectionComparison.comparison A S).obj P) :=
  (ImmersionProjectionComparison.comparison A X).mapIso
      ((Etale.extensionIso A c v).app P) ≪≫
    ImmersionProjectionComparison.extensionComparison A c v P ≪≫
    ((ProEtale.extensionIso A c v).app
      ((ImmersionProjectionComparison.comparison A S).obj P)).symm

/-- The contravariant Hom identification induced by the inverse of Delta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def homChange (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] (P : Etale.D A S) (B : Etale.D A X) :
    ProEtale.hom A X
        ((ImmersionProjectionComparison.comparison A X).obj
          ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P))
        ((ImmersionProjectionComparison.comparison A X).obj B) ⟶
      ProEtale.hom A X
        ((AlgebraicGeometry.ProEtale.locallyClosedProEtaleExtension A c v).obj
          ((ImmersionProjectionComparison.comparison A S).obj P))
        ((ImmersionProjectionComparison.comparison A X).obj B) :=
  ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) X).map
    (extensionComparison A c v P).inv.op).app
      ((ImmersionProjectionComparison.comparison A X).obj B)

/-- The stratum arrow H(1,gamma) after the evaluation-defined comparison beta.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def stratumMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X) :
    (ImmersionProjectionComparison.comparison A S).obj
        (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj)) ⟶
      ProEtale.hom A S ((ImmersionProjectionComparison.comparison A S).obj P)
        ((z.adjoints.proetaleRight v).obj
          ((ImmersionProjectionComparison.comparison A X).obj M.obj)) :=
  AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj) ≫
    ((AlgebraicGeometry.ProEtale.derivedHom (ModuleCat.{u + 1} A) S).obj
      (op ((ImmersionProjectionComparison.comparison A S).obj P))).map (z.gamma.hom.app M)

/-- The exact equation and all its conditional invertibility clauses at the chosen inputs.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def IdentityAndIsomorphisms (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)]
    (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (P : Etale.D A S) (M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X)
    (χe : Etale.HomIso A c v z.adjoints) (χp : ProEtale.HomIso A c v z.adjoints)
    (hK : DerivedCategory.TStructure.t.plus
      (Etale.hom A S P ((z.adjoints.etaleRight v).obj M.obj))) : Prop :=
  (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
        ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj ≫
      homChange A c v P M.obj ≫
      χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
        (ImmersionProjectionComparison.comparison A X).obj M.obj) =
    (ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj)) ≫
      directImageMate A (c ≫ v) ⟨_, hK⟩ ≫
      (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
        ).rightDerivedFunctor.map (stratumMap A c v z P M)) ∧
  (IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) S P
      ((z.adjoints.etaleRight v).obj M.obj)) →
    IsIso (AlgebraicGeometry.ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X
      ((AlgebraicGeometry.ProEtale.locallyClosedEtaleExtension A c v).obj P) M.obj) ∧
    IsIso (homChange A c v P M.obj) ∧
    IsIso (χp.hom.app (op ((ImmersionProjectionComparison.comparison A S).obj P),
      (ImmersionProjectionComparison.comparison A X).obj M.obj)) ∧
    IsIso ((ImmersionProjectionComparison.comparison A X).map (χe.hom.app (op P, M.obj))) ∧
    IsIso (directImageMate A (c ≫ v) ⟨_, hK⟩) ∧
    IsIso (stratumMap A c v z P M) ∧
    IsIso ((AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) (c ≫ v)
      ).rightDerivedFunctor.map (stratumMap A c v z P M)))

/-- The conclusion for a finite coefficient ring; all auxiliary maps above are canonical data.
Source: blueprint finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-stratum-hom-comparison-mate). -/
def Conclusion (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] [QuasiCompact (c ≫ v)] : Prop :=
  ∀ (z : AlgebraicGeometry.ProEtale.LocallyClosedExceptionalComparison A c v)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
    Scheme.IsFiniteLocallyConstantSheaf L →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat A (((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} A)).obj L)) →
    ∀ M : AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory A X,
    AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A S
      ((z.adjoints.etaleRight v).obj M.obj) →
    ∃ χe : Etale.HomIso A c v z.adjoints, ∃ χp : ProEtale.HomIso A c v z.adjoints,
      Etale.Normalized A c v z.adjoints χe ∧ ProEtale.Normalized A c v z.adjoints χp ∧
      ∃ hK : DerivedCategory.TStructure.t.plus
        (Etale.hom A S (ImmersionProjectionComparison.single A L)
          ((z.adjoints.etaleRight v).obj M.obj)),
        IdentityAndIsomorphisms A c v z (ImmersionProjectionComparison.single A L) M χe χp hK

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StratumHomComparisonMate | M3 | Original consumer and theorem; public names preserved, proof completed from the new equality lemma. |
| Sheaf.AlgebraicGeometry.StratumHomComparisonData | M3 | New owner of the same canonical definitions; no postponed data. |
| Sheaf.AlgebraicGeometry.StratumHomPairingIdentity | M3 | New strict equality sublemma consumes the canonical data. |

The downstream script reports zero existing downstream Lean modules of the item. Direct source
search finds the moved names only in the original module. Unfinished DAG parents continue to
use the original theorem; none is withdrawn. No forced adaptation of another group's file.

## Status

landed 20261025T163849-L-876411 2026-10-25 (merge of deliver/M3/Sheaf.AlgebraicGeometry.StratumHomComparisonMate)
