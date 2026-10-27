module

public import Sheaf.Paper.PurIntegralRepresentingPairData
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.BrownTowerFiniteSiteComparison
public import Sheaf.Paper.IntegralExceptionalInverseImage
public import Sheaf.Paper.PurIntegralSupportComparison
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization
import Sheaf.Paper.PurCoordinateRepresentingFamily
import Sheaf.Paper.PurSupportPresentationAlpha

/-! # Integral representing pairs from supplied exceptional systems

Source: blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction, Hom display
and unit/counit paragraph (blueprint: lem-pur-integral-reconstructed-representing-pair).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (RX : CoefficientDerivedSystemCalculus l E X)
  (RY : CoefficientDerivedSystemCalculus l E Y)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

attribute [local irreducible] supportPresentation PurIntegralSupportComparison.beta
  PurIntegralSupportComparison.normalized finiteCoordinates finiteCounit transpose
  Padic coordinates purCoefficientModel

/-- The representing pairs and trace maps on the dependency's own integralSupport
and alpha. The coordinate presentation is the fixed normalized beta; alpha_transport
pins its compatibility with the actual published reconstruction counit.
Source: blueprint integral Hom display and final unit/counit paragraph
(blueprint: lem-pur-integral-reconstructed-representing-pair). -/
structure PublishedFamily
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) where
  coordinate : Family l E (R X) (R Y) S G H D hD
  alpha_transport : ∀ K : CondensedERealization.Integral l E X,
    (reduction l E Y (R Y)).map
        ((supportPresentation l E (R X) S G H D (beta l E S G H D)).hom.app K.obj) ≫
      (coordinates l E Y).functor.map
        ((CompactSupportCondensedRealization.alpha l E c R M).app K) =
    alpha l E (R X) (R Y) S G H D K.obj ≫
      (beta l E S G H D).hom.app
        ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj))
  hom : ∀ (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (K : CondensedERealization.Integral l E X),
    (K ⟶ A.object) ≃ₗ[PbcIntegralRing l E]
      ((CompactSupportCondensedRealization.integralSupport l E c R M).obj K ⟶ L)
  hom_formula : ∀ L A K h,
    (hom L A K h).hom =
      (supportPresentation l E (R X) S G H D (beta l E S G H D)).inv.app K.obj ≫
        (coordinate.pair L A).hom K h
  hom_natural : ∀ L A (K K' : CondensedERealization.Integral l E X)
    (b : K' ⟶ K) (h : K ⟶ A.object),
    hom L A K' (b ≫ h) =
      (CompactSupportCondensedRealization.integralSupport l E c R M).map b ≫ hom L A K h
  trace_reduction : ∀ L A,
    (reduction l E Y (R Y)).map ((hom L A A.object (𝟙 A.object)).hom) =
      (coordinates l E Y).functor.map
          ((CompactSupportCondensedRealization.alpha l E c R M).app A.object) ≫
        (beta l E S G H D).inv.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj A.object.obj)) ≫
        D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system) ≫
        D.compact.functor.map (coordinate.pair L A).theta.hom ≫
        D.counit _ (coordinate.pair L A).origin (coordinate.pair L A).normalized
          (coordinate.pair L A).finiteTor (coordinate.pair L A).lowerBound
  trace_evaluation : ∀ L A (n : ℕ),
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      ((reduction l E Y (R Y)).map ((hom L A A.object (𝟙 A.object)).hom))) =
    (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
      ((coordinates l E Y).functor.map
          ((CompactSupportCondensedRealization.alpha l E c R M).app A.object) ≫
        (beta l E S G H D).inv.app
          ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj A.object.obj)) ≫
        D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system))) ≫
      (D.compactEvaluation n).hom.app A.system ≫
      (FiniteCoefficientAdjoints.lower
        (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n) c).map
        ((D.siteX.realization n).derived.map (A.phi n).hom ≫
          (finiteCoordinates l E S G H D hD n).hom.app
            ((D.siteY.proEvaluation.evaluation n).obj ((reduction l E Y (R Y)).obj L.obj))) ≫
      finiteCounit l E S G H D n ((reduction l E Y (R Y)).obj L.obj)
        ((coordinate.pair L A).finite_etale_bound n)
  input_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (A' : Supplied l E (R X) (R Y) S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (coordinate.pair L' A').theta.hom = (coordinate.pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y (R Y)).map b.hom) →
    ∀ (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object),
      hom L' A' K (ObjectProperty.homMk (h.hom ≫ (totalLimit l E X).map a)) =
        hom L A K h ≫ b
  trace_natural : ∀ (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (A' : Supplied l E (R X) (R Y) S G H D L')
    (b : L ⟶ L') (a : A.system ⟶ A'.system),
    a ≫ (coordinate.pair L' A').theta.hom = (coordinate.pair L A).theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y (R Y)).map b.hom) →
    (CompactSupportCondensedRealization.integralSupport l E c R M).map
        (ObjectProperty.homMk ((totalLimit l E X).map a)) ≫
      hom L' A' A'.object (𝟙 A'.object) = hom L A A.object (𝟙 A.object) ≫ b


private def publishedHom
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (F : Family l E (R X) (R Y) S G H D hD)
    (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (K : CondensedERealization.Integral l E X) :
    (K ⟶ A.object) ≃ₗ[PbcIntegralRing l E]
      ((CompactSupportCondensedRealization.integralSupport l E c R M).obj K ⟶ L) :=
  ((F.pair L A).hom K).trans
    ((Linear.homCongr (PbcIntegralRing l E)
      ((supportPresentation l E (R X) S G H D (beta l E S G H D)).app K.obj)
      (Iso.refl L.obj)).trans
        (InducedCategory.homLinearEquiv
          (C := PbcCompletedDerived Y (pbcIntegralDatum l E))
          (F := fun Z : CondensedERealization.Integral l E Y ↦ Z.obj)
          (R := PbcIntegralRing l E)
          (X := (CompactSupportCondensedRealization.integralSupport l E c R M).obj K)
          (Y := L)).symm)

private theorem publishedHom_formula
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (F : Family l E (R X) (R Y) S G H D hD)
    (L : CondensedERealization.Integral l E Y)
    (A : Supplied l E (R X) (R Y) S G H D L)
    (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object) :
    (publishedHom l E S G H D R M hD F L A K h).hom =
      (supportPresentation l E (R X) S G H D (beta l E S G H D)).inv.app K.obj ≫
        (F.pair L A).hom K h := by
  change
    (((supportPresentation l E (R X) S G H D (beta l E S G H D)).app K.obj).inv ≫
      (F.pair L A).hom K h) ≫ 𝟙 L.obj = _
  rw [Category.comp_id]
  rfl

/-- Supplied normalized exceptional systems reconstruct integral representing pairs
for the dependency's own compact-support functor and actual alpha.
Source: current blueprint sk-prop-sp-integral-adjunction, Hom display and final
unit/counit paragraph (blueprint: lem-pur-integral-reconstructed-representing-pair).

Proof: first form the canonical beta from the section-normalized push comparisons,
the open-adjunction transpose, and the universal proper derived-image unit.
The fixed coordinate-equivalence unit and published coefficient-model counit give
supportPresentation beta. Naturality of the actual reduction/limit counit proves
alpha_transport; this is an equality of system maps, not just evaluations.
Uniform integral reduction supplies finite Tor bounds and bounded-below etale origin.
The supplied interval bounds the finite exceptional outputs, so Brown transport
applies. In the first recognition mode retain the given theta; in the second,
exact conservative evaluations detect concentration and the transition squares give
the strict H^r-system iso. Functorial good truncation normalized by identity on H^r
supplies theta; full faithfulness of the shifted heart proves common-degree squares.
Normalized reconstruction makes the actual unit and counit invertible. Compose the
actual adjunction Hom maps, theta, Brown's Hom map and alpha to construct coordinate
pairs. Pull back their Hom maps along supportPresentation beta to the dependency's
integralSupport. The underlying Hom is unchanged by the full subcategory inclusion;
additivity and the actual scalar action give the linear equivalences. Apply the
formula to the identity, use the triangle identities, and then alpha_transport to
obtain trace_reduction with the dependency's own alpha. Evaluate this whole-system
equality and paste the finite Brown counit normalization to obtain trace_evaluation.
Naturality of the same maps proves both published naturality formulas. -/
theorem reconstructedRepresentingPair
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))]
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) :
    Nonempty (PublishedFamily l E S G H D R M hD) := by
  classical
  obtain ⟨F⟩ := coordinateRepresentingFamily l E S G H D p _hpl k R M hD
  let e := supportPresentation l E (R X) S G H D (beta l E S G H D)
  have he (K : CondensedERealization.Integral l E X) :
      (reduction l E Y (R Y)).map (e.inv.app K.obj) ≫
          alpha l E (R X) (R Y) S G H D K.obj =
        (coordinates l E Y).functor.map
            ((CompactSupportCondensedRealization.alpha l E c R M).app K) ≫
          (beta l E S G H D).inv.app
            ((R X).reduction.obj ((purCoefficientModel l E X).functor.obj K.obj)) := by
    have h := supportPresentation_alpha l E S G H D R M K
    change (reduction l E Y (R Y)).map (e.hom.app K.obj) ≫ _ = _ at h
    apply (cancel_mono ((beta l E S G H D).hom.app _)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h]
    rw [← Category.assoc, ← Functor.map_comp, e.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id _).symm
  refine ⟨{
    coordinate := F
    alpha_transport := supportPresentation_alpha l E S G H D R M
    hom := publishedHom l E S G H D R M hD F
    hom_formula := publishedHom_formula l E S G H D R M hD F
    hom_natural := ?_
    trace_reduction := ?_
    trace_evaluation := ?_
    input_natural := ?_
    trace_natural := ?_ }⟩
  · intro L A K K' b h
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [publishedHom_formula, publishedHom_formula, (F.pair L A).hom_natural]
    change e.inv.app K'.obj ≫ (support l E (R X) S G H D).map b.hom ≫ _ =
      (CompactSupportCondensedRealization.rawSupport l E c (R X)).map b.hom ≫
        (e.inv.app K.obj ≫ _)
    rw [← Category.assoc, ← e.inv.naturality, Category.assoc]
  · intro L A
    rw [publishedHom_formula, Functor.map_comp, (F.pair L A).trace_reduction]
    convert congrArg
      (fun z ↦ z ≫ D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system) ≫
        D.compact.functor.map (F.pair L A).theta.hom ≫
        D.counit _ (F.pair L A).origin (F.pair L A).normalized
          (F.pair L A).finiteTor (F.pair L A).lowerBound) (he A.object) using 1 <;>
      (try simp only [Category.assoc]) <;> rfl
  · intro L A n
    have ht := (F.pair L A).trace_evaluation n
    have hh := congrArg (fun z ↦
      (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map z))
      (he A.object)
    have hmap := congrArg (fun z ↦
      (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
        ((reduction l E Y (R Y)).map z)))
      (publishedHom_formula l E S G H D R M hD F L A A.object (𝟙 A.object))
    simp only [Functor.map_comp] at hmap hh
    exact hmap.trans ((congrArg (fun z ↦
      (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
        ((reduction l E Y (R Y)).map (e.inv.app A.object.obj))) ≫ z) ht).trans
      (by simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ z ≫
          (D.siteY.realization n).derived.map ((D.siteY.proEvaluation.evaluation n).map
            (D.compact.functor.map ((adjunction l E X (R X)).counit.app A.system))) ≫
          (D.compactEvaluation n).hom.app A.system ≫
          (FiniteCoefficientAdjoints.lower
            (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
              (integralExceptionalUniformizer l E) n) c).map
            ((D.siteX.realization n).derived.map (A.phi n).hom ≫
              (finiteCoordinates l E S G H D hD n).hom.app
                ((D.siteY.proEvaluation.evaluation n).obj
                  ((reduction l E Y (R Y)).obj L.obj))) ≫
          finiteCounit l E S G H D n ((reduction l E Y (R Y)).obj L.obj)
            ((F.pair L A).finite_etale_bound n)) hh))
  · intro L L' A A' b a ha K h
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom]
    rw [publishedHom_formula, publishedHom_formula, F.hom_natural L L' A A' b a ha]
    simp only [Category.assoc]
  · intro L L' A A' b a ha
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      publishedHom_formula, publishedHom_formula]
    change (CompactSupportCondensedRealization.rawSupport l E c (R X)).map
        ((totalLimit l E X).map a) ≫ (e.inv.app A'.object.obj ≫ _) =
      (e.inv.app A.object.obj ≫ _) ≫ b.hom
    have hn := e.inv.naturality ((totalLimit l E X).map a)
    change (CompactSupportCondensedRealization.rawSupport l E c (R X)).map
        ((totalLimit l E X).map a) ≫ e.inv.app A'.object.obj =
      e.inv.app A.object.obj ≫
        (support l E (R X) S G H D).map ((totalLimit l E X).map a) at hn
    rw [← Category.assoc, hn, Category.assoc,
      F.trace_natural L L' A A' b a ha, Category.assoc]

end WeilConjectures.PurIntegralRepresentingPair
