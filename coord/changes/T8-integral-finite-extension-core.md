# WeilConjectures.IntegralFiniteExtension canonical comparison core

## Reason

The three proper partial comparison statements use u, beta, unit, comp and the conclusion
predicates. The item theorem must import these statements. Relocate its prerequisite
namespace to CoefIntegralFiniteExtensionCore and publicly re-export it from the original
module, so there is no import cycle. This is dependency separation for a proof reduction;
it is not a split to evade a compile limit. Existing declaration signatures, visibility,
attributes and non-proof bodies are retained verbatim. The existing public Models import
remains public through Core. No adopted source module changes.

The new u_reduction theorem extracts the defining chosen-witness equation. The three
new theorem modules expose only strictly partial comparison assertions, each with a node,
source and proof in words. The original theorem is assembled from them with a complete
Lean proof. No target statement or definition used by a target changes its meaning.

## Old

The following namespace was in the item module (verbatim):

```lean
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)

/-- The finite-counit characterization determines the integral dualizing map uniquely.
Source: blueprint order 2494, second and third paragraphs
(blueprint: lem-coef-integral-finite-extension).
Proof: use finiteEtaleU at every target level, including the intermediate ramified
quotients. The counit composition equations make these a coherent system. Realize
it in the coefficient sequence category and take its total derived limit. The
normalized reduction counits give exactly the displayed squares. For uniqueness,
apply the coherent reduction/limit adjunction; the constructible mapping groups at
finite levels are finite, hence the inverse system is Mittag-Leffler and its lim-one
term vanishes. Thus equality of all these reductions determines the map. -/
theorem u_existsUnique :
    ∃! f : (integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj ⟶ wL.omega.obj,
      ∀ n : ℕ,
        (scalarReductionDerivedExtension l L X n).map f ≫ (wL.reduction n).hom =
          (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
            (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
              (wE.reduction n).hom ≫ finiteU l E L ι X D n := by
  let f := fun n : ℕ ↦
    (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
        (wE.reduction n).hom ≫ finiteU l E L ι X D n ≫ (wL.reduction n).inv
  let K : sfIntegralConstructibleCategory l L X :=
    ⟨(integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj,
      sfIntegralScalarExtension_constructible D.p l hl E L ι X
        wE.omega.obj wE.omega.property⟩
  obtain ⟨g, hg, huniq⟩ := integralConstructibleReductionHom D l hl L X K wL.omega f
    (finiteDualizing_reduction_coherent l E L ι X D hl wE wL)
  refine ⟨g, ?_, ?_⟩
  · intro n
    rw [hg n]
    simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro g' hg'
    apply huniq g'
    intro n
    apply (cancel_mono (wL.reduction n).hom).1
    rw [hg' n]
    simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The canonical u, chosen from a theorem determining the actual morphism uniquely.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def u : (integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj ⟶ wL.omega.obj :=
  (u_existsUnique l E L ι X D hl wE wL).exists.choose

/-- Beta is v followed by RHom(TK,u); it is not independent comparison data.
Source: blueprint order 2494, third displayed comparison
(blueprint: lem-coef-integral-finite-extension). -/
def beta (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralVerdier.dual l E X wE.omega.obj).obj (op K)) ⟶
      (IntegralVerdier.dual l L X wL.omega.obj).obj
        (op ((integralScalarExtensionOfUniverses l E L ι X).obj K)) :=
  v l E L ι X a b K wE.omega.obj hK wE.omega.property.1 ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL))

/-- The identity-extension comparison is multiplication, conjugated by completion.
Source: blueprint order 2494, last paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def unit (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X).obj K ≅ K :=
  (completion l E E (AlgHom.id (Padic l) E) X K hK).symm ≪≫
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X))).app K ≪≫
    (PurCompactSupport.tensorIdentity
      (completedIntegralCommRingSheafUnrestricted l E X)).app K

/-- The tensor associator, conjugated by the three specified completion comparisons.
Source: blueprint order 2494, last paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def comp (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l L F j X).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅
      (integralScalarExtensionOfUniverses l E F (j.comp ι) X).obj K :=
  (completion l L F j X _ (extension_complete l E L ι X K hK)).symm ≪≫
    (pbcDerivedExtend (completedCoefficientMap l L F j X)).mapIso
      (completion l E L ι X K hK).symm ≪≫
    (PurCompactSupport.tensorComposition (completedCoefficientMap l E L ι X)
      (completedCoefficientMap l L F j X) (completedCoefficientMap l E F (j.comp ι) X)
      (PurCompactSupport.completedMap_composition l E L ι F j X)).app K ≪≫
    completion l E F (j.comp ι) X K hK

/-- Scalar-extended evaluation, with all three completion comparisons displayed.
Source: blueprint order 2494, evaluation clause
(blueprint: lem-coef-integral-finite-extension). -/
def extendedEvaluation
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    b.tensor.obj ((integralScalarExtensionOfUniverses l E L ι X).obj K,
      (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M))) ⟶
      (integralScalarExtensionOfUniverses l E L ι X).obj M :=
  b.tensor.map (Prod.mkHom (completion l E L ι X K hK).inv
      (completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)).inv) ≫
    (PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
      (tensorModel X a) (tensorModel X b)).inv.app
        (K, (IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ≫
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map
      ((a.adjunction K).counit.app M) ≫ (completion l E L ι X M hM).hom

/-- The single-extension assertions, including equations for the actual evaluation,
double dual and all three finite reductions. All Hom isomorphism assertions have
constructible inputs. Tensor presentations retain their representative normalizations.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def Conclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (sE : IntegralVerdier.SignedSymmetry X _ a)
    (sL : IntegralVerdier.SignedSymmetry X _ b)
    (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n) : Prop :=
  let T := integralScalarExtensionOfUniverses l E L ι X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  let DL := IntegralVerdier.dual l L X wL.omega.obj
  (∃ (_ : T.CommShift ℤ), T.IsTriangulated) ∧
  (∀ K : sfIntegralConstructibleCategory l E X, sfIntegralConstructible l L X (T.obj K.obj)) ∧
  IsIso (u l E L ι X D hl wE wL) ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    IsIso (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (beta l E L ι X D hl wE wL a b K.obj K.property.1)) ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) ≫
        (b.adjunction (T.obj K.obj)).counit.app (T.obj M.obj) =
      extendedEvaluation l E L ι X a b K.obj M.obj K.property.1 M.property.1) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (beta l E L ι X D hl wE wL a b K.obj K.property.1)) ≫
        (b.adjunction (T.obj K.obj)).counit.app wL.omega.obj =
      extendedEvaluation l E L ι X a b K.obj wE.omega.obj
        K.property.1 wE.omega.property.1 ≫ u l E L ι X D hl wE wL) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IntegralVerdier.delta X b sL wL.omega.obj (T.obj K.obj) ≫
        DL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1).op =
      T.map (IntegralVerdier.delta X a sE wE.omega.obj K.obj) ≫
        beta l E L ι X D hl wE wL a b (DE.obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)) ∧
  (∀ n : ℕ,
    (scalarReductionDerivedExtension l L X n).map (u l E L ι X D hl wE wL) ≫
        (wL.reduction n).hom =
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n) ∧
  (∀ (n : ℕ) (K M : sfIntegralConstructibleCategory l E X),
    let rE := scalarReductionDerivedExtension l E X n
    let rL := scalarReductionDerivedExtension l L X n
    let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
    let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
    rL.map (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
        IntegralHom.comparison l L X D hl (mL n) (T.obj K.obj) (T.obj M.obj) =
      (quotient l E L ι X n (HE.obj (op K.obj, M.obj))
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
        F.map (IntegralHom.comparison l E X D hl (mE n) K.obj M.obj) ≫
        homMap X (integralScalarQuotientSheafMap l E L ι X n)
          (mE n).target (mL n).target (rE.obj K.obj) (rE.obj M.obj) ≫
        Hn.map (Prod.mkHom (quotient l E L ι X n K.obj K.property.1).hom.op
          (quotient l E L ι X n M.obj M.property.1).inv)) ∧
  (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
    let rE := scalarReductionDerivedExtension l E X n
    let rL := scalarReductionDerivedExtension l L X n
    let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
    let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
    rL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
        IntegralVerdier.comparison l L X D hl (mL n) wL.omega wL.reduction (T.obj K.obj) =
      (quotient l E L ι X n (DE.obj (op K.obj))
        (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom ≫
        F.map (IntegralVerdier.comparison l E X D hl (mE n) wE.omega wE.reduction K.obj) ≫
        homMap X (integralScalarQuotientSheafMap l E L ι X n)
          (mE n).target (mL n).target (rE.obj K.obj) (integralDualizingFiniteTerm l E D X n) ≫
        Hn.map (Prod.mkHom (quotient l E L ι X n K.obj K.property.1).hom.op
          (finiteU l E L ι X D n)))

/-- The three identity-extension equations use the specified multiplication unit.
Source: blueprint order 2494, identity-extension clause
(blueprint: lem-coef-integral-finite-extension). -/
def IdentityConclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X)) : Prop :=
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  u l E E (AlgHom.id (Padic l) E) X D hl wE wE =
      (unit l E X wE.omega.obj wE.omega.property.1).hom ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    v l E E (AlgHom.id (Padic l) E) X a a K.obj M.obj K.property.1 M.property.1 ≫
        H.map (Prod.mkHom (unit l E X K.obj K.property.1).inv.op
          (unit l E X M.obj M.property.1).hom) =
      (unit l E X (H.obj (op K.obj, M.obj))
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    beta l E E (AlgHom.id (Padic l) E) X D hl wE wE a a K.obj K.property.1 ≫
        DE.map (unit l E X K.obj K.property.1).inv.op =
      (unit l E X (DE.obj (op K.obj))
        (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom)

/-- Composition of u, v and beta, with the actual tensor associator at every endpoint.
The final clause is the associator pentagon on the unchanged ambient morphisms.
Source: blueprint order 2494, composition clause
(blueprint: lem-coef-integral-finite-extension). -/
def CompositionConclusion
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
    (c : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l F X)) : Prop :=
  let T := integralScalarExtensionOfUniverses l E L ι X
  let U := integralScalarExtensionOfUniverses l L F j X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let HF := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l F X)
  let DE := IntegralVerdier.dual l E X wE.omega.obj
  let DF := IntegralVerdier.dual l F X wF.omega.obj
  (∀ K : sfIntegralConstructibleCategory l E X,
    (comp l E E (AlgHom.id (Padic l) E) X L ι K.obj K.property.1).hom =
      T.map (unit l E X K.obj K.property.1).hom) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    (comp l E L ι X L (AlgHom.id (Padic l) L) K.obj K.property.1).hom =
      (unit l L X (T.obj K.obj)
        (extension_complete l E L ι X K.obj K.property.1)).hom) ∧
  U.map (u l E L ι X D hl wE wL) ≫ u l L F j X D hl wL wF =
      (comp l E L ι X F j wE.omega.obj wE.omega.property.1).hom ≫
        u l E F (j.comp ι) X D hl wE wF ∧
  (∀ K M : sfIntegralConstructibleCategory l E X,
    U.map (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
        v l L F j X b c (T.obj K.obj) (T.obj M.obj)
          (extension_complete l E L ι X K.obj K.property.1)
          (extension_complete l E L ι X M.obj M.property.1) ≫
        HF.map (Prod.mkHom (comp l E L ι X F j K.obj K.property.1).inv.op
          (comp l E L ι X F j M.obj M.property.1).hom) =
      (comp l E L ι X F j (HE.obj (op K.obj, M.obj))
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
        v l E F (j.comp ι) X a c K.obj M.obj K.property.1 M.property.1) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    U.map (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
        beta l L F j X D hl wL wF b c (T.obj K.obj)
          (extension_complete l E L ι X K.obj K.property.1) ≫
        DF.map (comp l E L ι X F j K.obj K.property.1).inv.op =
      (comp l E L ι X F j (DE.obj (op K.obj))
        (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom ≫
        beta l E F (j.comp ι) X D hl wE wF a c K.obj K.property.1) ∧
  (∀ (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (k : F →ₐ[Padic l] G) (K : sfIntegralConstructibleCategory l E X),
    (integralScalarExtensionOfUniverses l F G k X).map
        (comp l E L ι X F j K.obj K.property.1).hom ≫
        (comp l E F (j.comp ι) X G k K.obj K.property.1).hom =
      (comp l L F j X G k (T.obj K.obj)
        (extension_complete l E L ι X K.obj K.property.1)).hom ≫
        (comp l E L ι X G (k.comp j) K.obj K.property.1).hom)

end WeilConjectures.IntegralFiniteExtension
```

## New

The identical namespace, including its already proved u_existsUnique and all definition
bodies, is in lean/Sheaf/SixFunctors/CoefIntegralFiniteExtensionCore.lean. The original
module publicly imports Core and retains coef_integral_finite_extension with its identical
signature. Core publicly imports the existing Models module, retaining the old public API.
The only added public declaration in Core is:

```lean
/-- The canonical map has precisely the prescribed finite counit reductions.
Source: blueprint finite dualizing comparison (blueprint: lem-coef-integral-finite-extension). -/
theorem u_reduction (n : ℕ) :
    (scalarReductionDerivedExtension l L X n).map (u l E L ι X D hl wE wL) ≫
        (wL.reduction n).hom =
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n := by
  exact (u_existsUnique l E L ι X D hl wE wL).exists.choose_spec n

```

Local irreducibility attributes protect large internal-Hom constructions from proof-time
unfolding. They are file-local elaboration commands; no exported reducibility attribute
changes. The new theorem declarations are comparison_invertibility, reductionPairing and
comparison_cocycles, in separate modules with their recorded DAG attachments.

## Users

The downstream source census was generated by tools/downstream.py. Every existing direct
and transitive consumer sees the same declarations through the original module. No consumer
is adapted. Existing statements and definitions mean exactly the same thing; target statement
review is not reopened by this relocation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicCommonStageHomTranspose | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicNormalizedPurityLift | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicPurityScalarNaturality | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceConstruction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceReductionData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceScalarData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AffineSpaceProductDomain | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.AffineSpaceTraceFactorization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.CartesianSectionAdjointMates | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.CartesianSectionData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.ChartDiagonalSourceMate | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.ExceptionalRefinementMates | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.FiniteTorStability | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.GeneralHomComparisonCocycles | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.GeometricComparisonData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.GeometricOperations | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.InverseContravariantBidual | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.ProperProductCounitTranspose | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.PurAdicReconstruction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalHomScalarTranspose | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalPurityComparisonDescent | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalPurityScalarLocalization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalPuritySourceLocalization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalScalarComparisonData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalTensorSymmetry | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RelativeKunneth | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.RelativeProductInputDomains | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SfBidualityClass | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SfPackageCoefficientDomains | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SfPackageFieldOperationRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SitePerfectRationalBidual | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.SystemScalarProjectionIdentification | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TraceCorrespondences | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackSquareScalars | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.VerdierCoefficientRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.WeilChosenDualityExchange | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.WeilChosenDualityExchangeData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.WeilChosenExchangeConstruction | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.Paper.WeilChosenTransposeNaturality | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefQbarVerdier | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteExceptional | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteExceptionalData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteScalarMateData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalDualizingIdentification | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalHomIdentifications | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalOperations | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalOperationsData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdier | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdierComposition | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdierDatum | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdierExtension | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdierModels | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.RationalVerdierUnit | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.SixFunctors.WeilChosenDualityHom | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.WeilSheaf.DualRealizationComparison | claimed; not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | not adapted | Identical existing public names, signatures and bodies through the original public re-export. |

## Statement corrected (reviewer, 2026-10-26)

`WeilConjectures.coef_integral_finite_extension` (lean/Sheaf/SixFunctors/CoefIntegralFiniteExtension.lean,
held by T8). Old: the last conjunct read
`∀ F … j wF (c : IntegralHom.TensorPresentation … F …), CompositionConclusion … a b F j wF c`.
New: the same, with the hypothesis
`(∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K), c.tensor.map (Prod.mkHom (𝟙 K')
((IntegralHom.hom X _).map (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →` before `CompositionConclusion`.

Why: a `TensorPresentation` fixes its adjunction only through `evaluation`, i.e. at
objects `Q.obj P` with `P` a flat-term K-flat complex. At any other object Z the
adjunction may be replaced by `(c.adjunction Z).ofNatIsoLeft (-𝟙)`, whose counit is
the negative; every field still holds. `v l E F (j.comp ι) X a c K M` transposes along
`c.adjunction ((pbcDerivedExtend _).obj K)` and `v l L F j X b c` along
`c.adjunction ((pbcDerivedExtend _).obj (T K))`; `pbcDerivedExtend` is a chosen
derived functor, so these objects need not be K-flat complexes and twisting one of
them negates one side of the fourth composition clause only. The clause was therefore
not provable for arbitrary c. The added hypothesis is exactly the first-variable
evaluation naturality which `IntegralVerdier.signedCalculus` supplies for the chosen
a and b; it pins every adjunction through the K-flat ones.

Users of the theorem: none (rg finds coef_integral_finite_extension only in its own
module). The Prop `SfPackageScalarHom` of Sheaf.Paper.SfPackageExceptionalCoherenceRealization
(unclaimed) repeats the old form; it is not proved from this theorem and is unchanged.

The same reason gives the new statements their hypotheses: `comparison_cocycles` assumes
this naturality for a, b and c; `reductionPairing` assumes it for a, b and for every
finite target presentation `(mE n).target`, `(mL n).target` (also supplied by
signedCalculus).

## Status

landed 20261025T203301-L-2800049 2026-10-25 (merge of deliver/T8/Sheaf.SixFunctors.CoefIntegralFiniteExtension)
