module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.Paper.ContinuousModuleEncodingUniverses
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.ContinuousRingUniverseRealization
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.LatticeSheafBasic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.Paper.ContinuousIntegralModelEncodingUniverses
import Sheaf.Paper.ContinuousScalarEncodingUniverses
import Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.Paper.ContinuousIntegralCoefficientComparison
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # The internal constructible image of integral scalar extension

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Corollary 6.8.9 and the scalar-extension construction in Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-integral-scalar-constructible-image)

The completed coefficient comparison is normalized at every residue projection.
Both encodings are the specified section-action equivalences. All coefficient
carriers are in the scheme universe; module values are in its successor universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory
open scoped CategoryTheory.Obj


open CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.Scheme

/-- Identify the completed category's finite quotient with its continuous-function chart.
The quotient lift is fixed on representatives, and the last map sends constants to
constant functions. Source: Bhatt--Scholze, Lemma 6.8.2(1), Definition 6.8.10.
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def integralScalarFiniteChart (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ⟶
      finiteContinuousCoefficientSheaf l T E n :=
  (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
    (discreteContinuousCoefficientIso T).hom.app (finiteCoefficientRing l E n)

/-- The scalar map in completed coordinates is the specified comparison followed by
postcomposition with the actual valuation-ring inclusion.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-integral-scalar-constructible-image). -/
def integralScalarCoefficientMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (c : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E)) :
    pbcAdicCompletion T (pbcIntegralDatum l E) ⟶ latticeCoefficientSheaf T E :=
  c.hom ≫ latticeCoefficientSheafMap T
    (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val

private def scalarLiftSheafIso (T : Scheme.{u}) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    latticeCoefficientSheaf T A ≅ continuousCoefficientSheaf T (ULift.{u + 1} A) :=
  { hom := ⟨{
      app := fun V ↦ CommRingCat.ofHom
        { toFun := fun f ↦ ⟨fun x ↦ ULift.up (f.down x),
            continuous_uliftUp.comp f.down.continuous⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }⟩
    inv := ⟨{
      app := fun V ↦ CommRingCat.ofHom
        { toFun := fun f ↦ ULift.up ⟨fun x ↦ (f x).down,
            continuous_uliftDown.comp f.continuous⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }⟩
    hom_inv_id := by ext V f; rfl
    inv_hom_id := by ext V f; rfl }

private def scalarTopologySheafIso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (t₀ t₁ : TopologicalSpace A) (h₀ : @IsTopologicalRing A t₀ inferInstance)
    (h₁ : @IsTopologicalRing A t₁ inferInstance) (ht : t₀ = t₁) :
    @continuousCoefficientSheaf T A t₀ inferInstance h₀ ≅
      @continuousCoefficientSheaf T A t₁ inferInstance h₁ := by
  cases ht
  exact Iso.refl _

private theorem scalarTopologySheafIso_value (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] (t₀ t₁ : TopologicalSpace A)
    (h₀ : @IsTopologicalRing A t₀ inferInstance)
    (h₁ : @IsTopologicalRing A t₁ inferInstance) (ht : t₀ = t₁)
    (U : T.ProEtᵒᵖ) (s : @ContinuousMap U.unop.left A inferInstance t₁)
    (x : U.unop.left) :
    (@id (@ContinuousMap U.unop.left A inferInstance t₀)
      ((scalarTopologySheafIso T A t₀ t₁ h₀ h₁ ht).inv.hom.app U s)) x = s x := by
  cases ht
  rfl

private def scalarIntegerSheafIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [hE : NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E) ≅
      integralCoefficientSheaf l T E := by
  have hm : (coefficientExtensionNormedField l E).toMetricSpace = hE.toMetricSpace := by
    apply MetricSpace.ext
    apply Dist.ext
    funext a b
    rw [(coefficientExtensionNormedField l E).dist_eq, hE.dist_eq]
    exact (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (-a + b)).symm
  have ht := congrArg (fun m : MetricSpace E ↦
    @UniformSpace.toTopologicalSpace E
      (@PseudoMetricSpace.toUniformSpace E (@MetricSpace.toPseudoMetricSpace E m))) hm
  refine scalarLiftSheafIso T (Padic.coefficientExtensionIntegers l E) ≪≫
    scalarTopologySheafIso T _ _ _ _ _ ?_
  exact congrArg (fun t : TopologicalSpace E ↦
    @ULift.topologicalSpace (Padic.coefficientExtensionIntegers l E)
      (@TopologicalSpace.induced (Padic.coefficientExtensionIntegers l E) E Subtype.val t))
    ht.symm

private theorem scalarIntegerSheafIso_value (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (s : (integralCoefficientSheaf l T E).obj.obj U) (x : U.unop.left) :
    (((scalarIntegerSheafIso l E T).inv.hom.app U s).down x) =
      integralCoefficientValue l E T U s x := by
  change ((@id (@ContinuousMap U.unop.left _ inferInstance _)
    ((scalarTopologySheafIso T _ _ _ _ _ _).inv.hom.app U s)) x).down = _
  rw [scalarTopologySheafIso_value]
  rfl

private theorem scalarCompletedCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    ∃ c : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E),
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj U) (x : U.unop.left),
        (finiteContinuousCoefficientValue l E T n U
          ((integralScalarFiniteChart l E T n).hom.app U
            ((pbcAdicProjection T (pbcIntegralDatum l E) n).hom.app U s)) x).down =
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
            ((c.hom.hom.app U s).down x) := by
  classical
  let e := Functor.isoWhiskerLeft (finiteCoefficientRingTower l E)
    (discreteContinuousCoefficientIso T)
  let hc := Classical.choice (continuousCoefficientResidueCone_isLimit l E T)
  let i := hc.conePointsIsoOfNatIso (limit.isLimit (finiteCoefficientTower l T E)) e.symm
  let b := completedIso T l E
  let k := scalarIntegerSheafIso l E T
  let c := b ≪≫ i.symm ≪≫ k.symm
  refine ⟨c, ?_⟩
  intro n U s x
  let q := (discreteContinuousCoefficientIso T).app (finiteCoefficientRing l E n)
  have hi : i.hom ≫ limit.π (finiteCoefficientTower l T E) (op n) ≫ q.hom =
      continuousCoefficientReduction l E T n := by
    have h := hc.conePointsIsoOfNatIso_hom_comp
      (limit.isLimit (finiteCoefficientTower l T E)) e.symm (op n)
    change i.hom ≫ limit.π (finiteCoefficientTower l T E) (op n) =
      continuousCoefficientReduction l E T n ≫ q.inv at h
    rw [← Category.assoc, h, Category.assoc, q.inv_hom_id]
    exact Category.comp_id _
  have hb : b.hom ≫ limit.π (finiteCoefficientTower l T E) (op n) =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).inv ≫
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom := by
    dsimp only [b, completedIso, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π]
    dsimp only [pbcCompletedComparison]
    rw [← Category.assoc, HasLimit.isoOfNatIso_inv_π]
    rfl
  have h : pbcAdicProjection T (pbcIntegralDatum l E) n ≫
      integralScalarFiniteChart l E T n =
      (b.hom ≫ i.inv) ≫ continuousCoefficientReduction l E T n := by
    rw [← hi]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc b.hom, hb]
    rfl
  have hv := congrArg (fun f ↦
    (finiteContinuousCoefficientValue l E T n U (f.hom.app U s) x).down) h
  change _ = Ideal.Quotient.mk _
    (((k.inv.hom.app U ((b.hom ≫ i.inv).hom.app U s))).down x)
  rw [scalarIntegerSheafIso_value]
  exact hv

private theorem scalarFieldTriangulated (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) [IsNoetherian T] :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).IsTriangulated := by
  obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousCoefficientRingObj E)
    (exists_finiteFree_cover_of_condensedField_lfp l E) T
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj E) T
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).1⟩
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).2⟩
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := ⟨he _⟩
  exact isTriangulated_boundedConstructible_of_serre R

/-- Integral finite presentations give precisely the archived internal constructibility
condition, and the rational full subcategory has its induced triangulated structure.
The coefficient isomorphism is specified on every residue of every section.
Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), Corollary 6.8.9,
and the scalar-extension construction of Proposition 6.8.14(2).
(blueprint: lem-weil-pbc-integral-scalar-constructible-image).

Proof:
1. Construct the continuous completed coefficient chart from the existing
projection-normalized comparison and the limiting continuous residue cone. Equality
of the normed-algebra norm with the spectral norm identifies the actual integral
topology with the WithAbs topology. The explicit ULift chart then gives c; the cone
projection equations give precisely the displayed finite residue normalization.
2. The integral stratified-perfect characterization gives bounded cohomology with
finite completed constant scalar models. Apply the ordinary integral-model encoding
comparison to each cohomology module. The inverse encoding is an exact equivalence,
so its termwise derived functor preserves bounds and commutes with cohomology.
3. The ordinary continuous scalar comparison gives an exact internal localization
and a square with the two specified inverse encodings. The field equivalence
reflects finite limits, so sectionwise extension is exact as well. Uniqueness of
universal left-derived functors and the derived ordinary square identify the actual
pbcDerivedExtend with internal derived scalar extension. Apply the existing theorem
that exact internal scalar extension preserves bounded constructibility, and
transport through these isomorphisms. No torsion-freeness is used.
4. Apply the proved generic Serre helper directly to the specified continuous
field ring, using local finite-free presentations for its coefficients. Kernel,
cokernel and extension closure, together with isomorphism closure, give the claimed
triangulated subcategory by the existing bounded-constructible criterion.
-/
theorem integralScalarConstructibleImage (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) :
    ∃ c : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        latticeCoefficientSheaf T (Padic.coefficientExtensionIntegers l E),
      (∀ (n : ℕ) (U : T.ProEtᵒᵖ)
        (s : (pbcAdicCompletion T (pbcIntegralDatum l E)).obj.obj U) (x : U.unop.left),
        (finiteContinuousCoefficientValue l E T n U
          ((integralScalarFiniteChart l E T n).hom.app U
            ((pbcAdicProjection T (pbcIntegralDatum l E) n).hom.app U s)) x).down =
          Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
            ((c.hom.hom.app U s).down x)) ∧
      (∀ K : PbcIntegralCategory l E T hdim hl,
        boundedConstructible
          (condensedRingObj (Profinite.continuousCoefficientRingObj
            (Padic.coefficientExtensionIntegers l E)) T)
          ((completedContinuousModuleEquivalence l E T c).inverse.mapDerivedCategory.obj K.obj) ∧
        boundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)
          ((continuousFieldModuleEquivalenceUniverse l E T).inverse.mapDerivedCategory.obj
            ((pbcDerivedExtend (integralScalarCoefficientMap l E T c)).obj K.obj))) ∧
      (boundedConstructible
        (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).IsTriangulated := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  obtain ⟨c, hc⟩ := scalarCompletedCoefficient l E T
  refine ⟨c, hc, ?_, scalarFieldTriangulated l E T⟩
  have hl' : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ ⊤
    intro t ht
    simpa only [map_natCast] using hl t
  let FA := (completedContinuousModuleEquivalence l E T c).inverse
  let FE := (continuousFieldModuleEquivalenceUniverse l E T).inverse
  let a := integralScalarCoefficientMap l E T c
  let φ := continuousInternalScalarMapUniverses l E T
  let L := Mod.extendScalars.{u + 1, u + 2} φ
  obtain ⟨hL, ⟨e⟩⟩ := continuousScalarEncodingUniverses l E T c
  let : PreservesFiniteLimits L := hL
  let : PreservesColimitsOfSize.{0, 0} (pbcExtend a) :=
    (pbcScalarAdjunction a).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits (pbcExtend a) := inferInstance
  let : PreservesFiniteLimits (pbcExtend a ⋙ FE) :=
    preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteLimits (pbcExtend a) :=
    preservesFiniteLimits_of_reflects_of_preserves (pbcExtend a) FE
  let V := HomotopyCategory.quasiIso
    (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) (.up ℤ)
  let : (pbcDerivedExtend a).IsLeftDerivedFunctor (pbcExtensionCounit a) V :=
    pbcDerivedExtension_universal a
  let : (pbcExtend a).mapDerivedCategory.IsLeftDerivedFunctor
      (pbcExtend a).mapDerivedCategoryFactorsh.hom V :=
    Functor.isLeftDerivedFunctor_of_inverts V _ (pbcExtend a).mapDerivedCategoryFactorsh
  let d : pbcDerivedExtend a ≅ (pbcExtend a).mapDerivedCategory :=
    Functor.leftDerivedNatIso _ _ (pbcExtensionCounit a)
      (pbcExtend a).mapDerivedCategoryFactorsh.hom V (Iso.refl _)
  let de : pbcDerivedExtend a ⋙ FE.mapDerivedCategory ≅
      FA.mapDerivedCategory ⋙ L.mapDerivedCategory :=
    Functor.isoWhiskerRight d FE.mapDerivedCategory ≪≫
      Functor.mapDerivedCategorySquareIso e
  intro K
  have hchar := integralStratifiedPerfectCharacterization T l E hdim hl' K.obj
  have hmodels := hchar.2.mp (hchar.1.mp K.property)
  obtain ⟨b₀, b₁, _, hge, hle⟩ := hmodels.1
  have hb : DerivedCategory.TStructure.t.bounded K.obj := ⟨⟨b₀, hge⟩, ⟨b₁, hle⟩⟩
  have hi : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers l E)) T)
      (FA.mapDerivedCategory.obj K.obj) := by
    refine ⟨FA.bounded_mapDerivedCategory_obj hb, fun q ↦ ?_⟩
    have hq := continuousIntegralModelEncodingUniverses l E T c
      ((DerivedCategory.homologyFunctor _ q).obj K.obj) (hmodels.2 q)
    exact IsConstructibleModuleObject.of_iso
      ((FA.mapDerivedCategoryHomologyFunctorIso q).app K.obj) hq
  refine ⟨hi, ?_⟩
  have hout := boundedConstructible_leftDerivedExtendScalars_obj _ _ φ
    (FA.mapDerivedCategory.obj K.obj) hi
  let dl : L.leftDerivedFunctor ≅ L.mapDerivedCategory :=
    Functor.leftDerivedNatIso _ _ L.leftDerivedFunctorCounit
      L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) (Iso.refl _)
  exact (boundedConstructible _).prop_of_iso
    ((dl.app (FA.mapDerivedCategory.obj K.obj)) ≪≫ (de.app K.obj).symm) hout

end AlgebraicGeometry.Scheme
