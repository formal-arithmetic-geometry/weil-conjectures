module

public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModels
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.CategoryTheory.SystemScalarModel
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

import Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Restriction, reduction, and the finite Postnikov sequence

Source: blueprint latest, sec-smooth-purity/sk-def-sp-normalized-towers,
normalized-towers-reduction, constructibility paragraph; Stacks Tags 03EL,
06YS, 08J5 and 093U(3)
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).

All derived categories are ordinary unbounded localizations. Index n denotes the
positive exponent n+1. The integral coefficient ring is literally the limit of the
recorded ell-power tower. No truncation is interchanged with derived reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance high] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The integral ring of the statement, as the limit of its positive ell-power quotients.
Source: blueprint latest, normalized-towers-reduction, coefficient convention
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedRing (T : Scheme.{u}) :
    Sheaf (ProEt.topology T) CommRingCat.{u + 1} := limit (spCoefficientCommRings.{u, u} l E T)

/-- The finite scalar ring at positive exponent n+1.
Source: blueprint latest, normalized-towers-reduction, coefficient convention
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedScalar (n : ℕ) :=
  Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)

/-- Quotient maps on constant scalars form the canonical cone.
Source: blueprint latest, coefficient convention; Stacks Tag 0H7J
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: each composite is the constant sheaf of the same quotient homomorphism.
The quotient map followed by a quotient transition is the smaller quotient map;
functoriality of the constant sheaf preserves this equation. -/
theorem spStratifiedScalarCone_naturality (T : Scheme.{u}) {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
        (spCoefficientConstantQuotient.{u, u} l E T a.unop) ≫
      (spCoefficientCommRings.{u, u} l E T).map f =
    (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
      (spCoefficientConstantQuotient.{u, u} l E T b.unop) := by
  let c : (Functor.const ℕᵒᵖ).obj
      (proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E)) ⟶
      spCoefficientCommRings.{u, u} l E T :=
    NatTrans.ofOpSequence
      (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))).comp
              ULift.ringEquiv.toRingHom)))) (by
        intro n
        simp only [Functor.const_obj_map, spCoefficientCommRings,
          Functor.ofOpSequence_map_homOfLE_succ]
        rw [← Functor.map_comp]
        congr 1)
  have hpre (n : ℕ) :
      (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
          (spCoefficientConstantQuotient.{u, u} l E T n) = c.app (op n) := by
    apply (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_injective
    rw [Functor.map_preimage]
    rfl
  rw [hpre, hpre]
  exact (Category.id_comp _).symm.trans (c.naturality f).symm

/-- The scalar inclusion is the limit lift of the actual constant quotient maps.
Source: blueprint latest, normalized-towers-reduction, scalar local models
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def spStratifiedScalarMap (T : Scheme.{u}) :
    proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E) ⟶
      spStratifiedRing l E T :=
  limit.lift (spCoefficientCommRings.{u, u} l E T)
    { pt := proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E)
      π :=
        { app (n : ℕᵒᵖ) := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
            (spCoefficientConstantQuotient.{u, u} l E T n.unop)
          naturality _ _ f := (Category.id_comp _).trans
            (spStratifiedScalarCone_naturality l E T f).symm } }

/-- The category of modules over the literal completed coefficient ring.
Source: blueprint latest, ordinary derived coefficient convention
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedModules (T : Scheme.{u}) : Type (u + 2) :=
  SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (spStratifiedRing l E T))


/-- Mathlib's existing Abelian structure, with the coefficient universe explicit.
Source: Stacks Tag 03DA
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedSiteModulesAbelian {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u + 1}) : Abelian (SheafOfModules.{u + 1} R) := inferInstance

/-- The same Abelian structure on completed coefficient modules.
Source: Stacks Tag 03DA
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedModulesAbelian (T : Scheme.{u}) : Abelian (spStratifiedModules l E T) :=
  spStratifiedSiteModulesAbelian (ProEt.topology T)
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (spStratifiedRing l E T))

attribute [local instance 40000] spStratifiedModulesAbelian

/-- Standard localization, retaining the small pro-etale site's two different universes.
Source: Stacks Tag 05RU
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
instance spStratified_hasDerived (T : Scheme.{u}) :
    HasDerivedCategory (spStratifiedModules l E T) := HasDerivedCategory.standard _

/-- The ordinary sheaf tensor and its universal K-flat-derived scalar extension.
The choice is of a universal pair, hence is unique up to its counit-compatible iso.
Source: Stacks Tags 06YS and 06YY
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def spStratifiedReductionModel (T : Scheme.{u}) (n : ℕ) :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (J := ProEt.topology T) (O := spStratifiedRing l E T)
      (S := proEtaleConstantRing T (spStratifiedScalar l E n))
      (limit.π (spCoefficientCommRings.{u, u} l E T) (op n)) :=
  Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
    (J := ProEt.topology T) (O := spStratifiedRing l E T)
    (S := proEtaleConstantRing T (spStratifiedScalar l E n))
    (limit.π (spCoefficientCommRings.{u, u} l E T) (op n)))

/-- The finite constant coefficient comparisons commute with the quotient transitions.
Source: Stacks Tags 0H7J and 03EL
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: adjoint both composites under the sheaf inverse-image adjunction. Naturality
of constant sections identifies both adjuncts with the same constant quotient map. -/
theorem spStratifiedFiniteMap_naturality {S T : Scheme.{u}} (i : S ⟶ T)
    {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (proEtaleSheafInverseImage i CommRingCat.{u + 1}).map
        ((spCoefficientCommRings.{u, u} l E T).map f) ≫
      proEtaleCoefficientInverseImageMap i (spStratifiedScalar l E b.unop) =
    proEtaleCoefficientInverseImageMap i (spStratifiedScalar l E a.unop) ≫
      (spCoefficientCommRings.{u, u} l E S).map f := by
  let L := proEtaleSheafInverseImage i CommRingCat.{u + 1}
  let c : spCoefficientCommRings.{u, u} l E T ⋙ L ⟶
      spCoefficientCommRings.{u, u} l E S :=
    NatTrans.ofOpSequence
      (fun n ↦ proEtaleCoefficientInverseImageMap i (spStratifiedScalar l E n)) (by
        intro n
        simpa only [Functor.comp_map, spCoefficientCommRings,
          Functor.ofOpSequence_map_homOfLE_succ] using
          proEtaleConstantInverseImageMap_naturality i
            (CommRingCat.ofHom
              (ULift.ringEquiv.symm.toRingHom.comp
                ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
                  ULift.ringEquiv.toRingHom))))
  exact c.naturality f

/-- The canonical map on integral rings is the limit lift of the finite comparison maps.
Source: blueprint latest, coefficient-preserving stratum restriction; Stacks Tag 03CO
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def spStratifiedRingMap {S T : Scheme.{u}} (i : S ⟶ T) :
    (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (spStratifiedRing l E T) ⟶
      spStratifiedRing l E S :=
  limit.lift (spCoefficientCommRings.{u, u} l E S)
    { pt := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
        (spStratifiedRing l E T)
      π :=
        { app (n : ℕᵒᵖ) := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).map
            (limit.π (spCoefficientCommRings.{u, u} l E T) n) ≫
              proEtaleCoefficientInverseImageMap i (spStratifiedScalar l E n.unop)
          naturality := by
            intro a b f
            dsimp
            rw [Category.id_comp, Category.assoc,
              ← spStratifiedFiniteMap_naturality l E i f,
              ← Category.assoc, ← Functor.map_comp, limit.w] } }

private theorem spStratifiedScalarFinite (n : ℕ) :
    Finite (spStratifiedScalar l E n) := by
  obtain ⟨m, hm⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  let : Finite (Padic.coefficientExtensionIntegers l E ⧸
      Padic.coefficientExtensionIdeal l E (m + 1)) :=
    Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.le_add_left 1 m)
  have hle : Padic.coefficientExtensionIdeal l E (m + 1) ≤
      spEllIdeal l E ^ (n + 1) :=
    (Ideal.pow_le_pow_right (Nat.le_succ m)).trans hm
  exact Finite.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)

/-- On an actual locally closed stratum the canonical completed coefficient map is
invertible; the finite maps already are the canonical constant-ring identifications.
Source: blueprint latest, coefficient-preserving restriction; Stacks Tags 03EL and 0941
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: realize the completed constant coefficients by continuous integral functions
on pro-etale test objects. Their base change to the stratum represents the same
coefficient functor. Its finite quotient maps are the constant-section comparisons.
The projection equations for the limit identify this isomorphism with the displayed
limit lift. This concerns this coefficient limit, not arbitrary inverse-image limits. -/
@[instance] theorem spStratifiedRingMap_isIso {S T : Scheme.{u}} (i : S ⟶ T)
    [IsImmersion i] : IsIso (spStratifiedRingMap l E i) := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n : ℕ ↦ CommRingCat.of (ULift.{u + 1}
      (spStratifiedScalar l E n)))
    (fun n ↦ CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
          ULift.ringEquiv.toRingHom)))
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ by
    let := spStratifiedScalarFinite l E n.unop
    exact inferInstanceAs (Finite (ULift.{u + 1} (spStratifiedScalar l E n.unop)))
  let towerIso (W : Scheme.{u}) :
      Q ⋙ constantSheaf (ProEt.topology W) CommRingCat.{u + 1} ≅
        spCoefficientCommRings.{u, u} l E W := by
    let c : Q ⋙ constantSheaf (ProEt.topology W) CommRingCat.{u + 1} ⟶
        spCoefficientCommRings.{u, u} l E W :=
      NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
        intro n
        simp only [Functor.comp_map, Q, spCoefficientCommRings,
          Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id, Category.id_comp])
    exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ c.naturality f)
  let L := proEtaleSheafInverseImage i CommRingCat.{u + 1}
  let : PreservesLimit (Q ⋙ constantSheaf (ProEt.topology T) CommRingCat.{u + 1}) L :=
    proEtaleSheafInverseImage_preserves_finite_tower i Q
  let : PreservesLimit (spCoefficientCommRings.{u, u} l E T) L :=
    preservesLimit_of_iso_diagram L (towerIso T)
  let d : spCoefficientCommRings.{u, u} l E T ⋙ L ≅
      spCoefficientCommRings.{u, u} l E S :=
    NatIso.ofComponents
      (fun n ↦ proEtaleConstantRingComparison i (spStratifiedScalar l E n.unop))
      (fun f ↦ spStratifiedFiniteMap_naturality l E i f)
  let hc := isLimitOfPreserves L (limit.isLimit (spCoefficientCommRings.{u, u} l E T))
  let hd := limit.isLimit (spCoefficientCommRings.{u, u} l E S)
  let e := hc.conePointsIsoOfNatIso hd d
  have he : spStratifiedRingMap l E i = e.hom := by
    apply limit.hom_ext
    intro n
    exact (limit.lift_π _ n).trans
      (hc.conePointsIsoOfNatIso_hom_comp hd d n).symm
  rw [he]
  infer_instance

/-- Exact inverse image, with scalar action transported through the canonical ring iso.
Source: Stacks Tag 04JC; blueprint latest, coefficient-preserving restriction
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedPull {S T : Scheme.{u}} (i : S ⟶ T) [IsImmersion i] :=
  proEtaleRingModulePullback i (spStratifiedRing l E T) (spStratifiedRing l E S)
    (asIso (spStratifiedRingMap l E i))

/-- Reduction in the ordinary unbounded derived category, from its universal pair.
Source: Stacks Tag 06YY
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedReduction (T : Scheme.{u}) (n : ℕ) :=
  (spStratifiedReductionModel l E T n).T

/-- The shift structure carried by the universal derived scalar-extension pair.
Source: Stacks Tag 06YY
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
instance spStratifiedReduction_commShift (T : Scheme.{u}) (n : ℕ) :
    (spStratifiedReduction l E T n).CommShift ℤ :=
  (spStratifiedReductionModel l E T n).triangulated.choose

/-- Triangulated exactness with the preceding shift structure.
Source: Stacks Tag 06YY
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
instance spStratifiedReduction_triangulated (T : Scheme.{u}) (n : ℕ) :
    (spStratifiedReduction l E T n).IsTriangulated :=
  (spStratifiedReductionModel l E T n).triangulated.choose_spec

/-- The finite scalar ring is finite also for ramified coefficient fields.
Source: blueprint latest, coefficient convention; DVR coefficient finiteness
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: in the DVR of integers ell is a unit times a positive power of a uniformizer.
Consequently its positive-power quotient is a positive uniformizer-power quotient.
The residue field is finite and the successive quotients of the maximal-ideal
filtration are one-dimensional over it, proving finiteness by induction. -/
@[instance] theorem spStratifiedScalar_finite (n : ℕ) : Finite (spStratifiedScalar l E n) := by
  exact spStratifiedScalarFinite l E n

/-- Reduction followed by exact restriction to the specified stratum, with the
finite constant coefficient identification, in the ordinary derived category.
Source: blueprint latest, normalized-towers-reduction, constructibility paragraph
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedReducedPull {S T : Scheme.{u}} (i : S ⟶ T) (n : ℕ) :=
  spStratifiedReduction l E T n ⋙
    (proEtaleConstantRingPullback (spStratifiedScalar l E n) i).mapDerivedCategory

/-- First exact restriction with the canonical integral scalar transport, then reduction.
Source: blueprint latest, normalized-towers-reduction, constructibility paragraph
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
abbrev spStratifiedPullReduced {S T : Scheme.{u}} (i : S ⟶ T) [IsImmersion i] (n : ℕ) :=
  (spStratifiedPull l E i).mapDerivedCategory ⋙ spStratifiedReduction l E S n

/-- The original section carried through the normalized inverse-image tensor unit.
Source: Stacks Tags 03D7 and 03EL
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def spStratifiedPullUnitSection {S T : Scheme.{u}} (i : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ B)
    (N : proEtaleRingModules T R) (U : T.ProEt) (x : N.val.obj (op U)) :
    ((proEtaleRingModulePullback i R B c).obj N).val.obj
      (op ((proEtaleBaseChange i).obj U)) :=
  (toSheafify (ProEt.topology S)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom
      ((proEtaleModuleInverseImage i R).obj N)).presheaf).app
        (op ((proEtaleBaseChange i).obj U))
    (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      (c.hom.hom.app (op ((proEtaleBaseChange i).obj U))).hom).unit.app
        (((proEtaleModuleInverseImage i R).obj N).val.obj
          (op ((proEtaleBaseChange i).obj U))))
      (AlgebraicGeometry.ProEtaleTensorComparison.inverseSection.{u} i N U x))

/-- The ordinary comparison is fixed, not merely chosen up to a scalar automorphism:
it carries the pulled-back local tensor c tensor x to pullback(c) tensor pullback(x).
Source: Stacks Tag 03EL; blueprint latest, coefficient-preserving restriction
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: the coefficient projection square is the defining equation of the limit
lift. The pure-tensor formula is consequently balanced. Sheafification and the
inverse-image adjunction give the comparison. The inverse formula and naturality
hold on the same generators, which locally generate both modules; this proves
invertibility and uniqueness with the displayed normalization. -/
theorem spStratifiedOrdinaryComparison_existsUnique {S T : Scheme.{u}}
    (i : S ⟶ T) [IsImmersion i] (n : ℕ) :
    ∃! b : (spStratifiedReductionModel l E T n).E ⋙
        proEtaleConstantRingPullback (spStratifiedScalar l E n) i ≅
      spStratifiedPull l E i ⋙ (spStratifiedReductionModel l E S n).E,
      ∀ (N : spStratifiedModules l E T) (U : T.ProEt)
        (c : (proEtaleConstantRing T (spStratifiedScalar l E n)).obj.obj (op U))
        (x : N.val.obj (op U)),
        (b.hom.app N).val.app (op ((proEtaleBaseChange i).obj U))
          (spStratifiedPullUnitSection i _ _
            (proEtaleConstantRingComparison i (spStratifiedScalar l E n))
            ((spStratifiedReductionModel l E T n).E.obj N) U
            (SheafOfModules.systemModelTmul (spStratifiedReductionModel l E T n) N (op U) c x)) =
        SheafOfModules.systemModelTmul (spStratifiedReductionModel l E S n)
          ((spStratifiedPull l E i).obj N) (op ((proEtaleBaseChange i).obj U))
          (((proEtaleCoefficientDirectImageMap i (spStratifiedScalar l E n)).hom.app
            (op U)) c)
          (spStratifiedPullUnitSection i _ _ (asIso (spStratifiedRingMap l E i)) N U x) := by
  sorry

/-- The ordinary comparison selected by its unique pure-tensor normalization.
Source: Stacks Tag 03EL
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def spStratifiedOrdinaryComparison {S T : Scheme.{u}} (i : S ⟶ T)
    [IsImmersion i] (n : ℕ) :=
  (spStratifiedOrdinaryComparison_existsUnique l E i n).exists.choose

/-- The representative characterization pins the derived comparison to the
ordinary pure-tensor comparison and the two universal K-flat counits.
Source: Stacks Tags 06YY and 03EL
(blueprint: lem-sp-stratified-reduction-postnikov-comparison). -/
def SpStratifiedComparisonFormula {S T : Scheme.{u}} (i : S ⟶ T)
    [IsImmersion i] (n : ℕ)
    (e : spStratifiedReducedPull l E i n ≅ spStratifiedPullReduced l E i n) : Prop :=
  ∀ P : CochainComplex (spStratifiedModules l E T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spStratifiedRing l E T) P →
    e.hom.app (DerivedCategory.Q.obj P) ≫
        (spStratifiedReduction l E S n).map
          ((spStratifiedPull l E i).mapDerivedCategoryFactors.hom.app P) ≫
        (spStratifiedReductionModel l E S n).ε.app
          (((spStratifiedPull l E i).mapHomologicalComplex (.up ℤ)).obj P) =
      (proEtaleConstantRingPullback (spStratifiedScalar l E n) i).mapDerivedCategory.map
          ((spStratifiedReductionModel l E T n).ε.app P) ≫
        (Functor.mapDerivedCategoryFactors
          (proEtaleConstantRingPullback (spStratifiedScalar l E n) i)).hom.app
            (((spStratifiedReductionModel l E T n).E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (spStratifiedOrdinaryComparison l E i n).hom
            (.up ℤ)).app P)

/-- Reduction preserves the images of the finite canonical truncation sequence on
one given global partition, uniformly in the reduction level and cohomological degree.
Finite presentation of local constant modules over the finite scalar ring is
finite type, since that ring is Noetherian. The third vertex of each displayed
canonical triangle is identified with the reduction of H^q(M)[-q]. The fourth
vertex is the shifted first vertex. The initial vertex is zero and the final
augmentation is invertible; reduction is never interchanged with truncation.

Source: blueprint latest, normalized-towers-reduction, constructibility paragraph;
Stacks Tags 03EL, 06YS, 08J5, 05RS, 093U(3) and 099Y
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).

Proof:
1. Exact module inverse image over the actual inverse-image ring commutes with
cohomology. The canonical coefficient isomorphism transports that scalar action
without changing exactness. Termwise inverse image preserves shifts and the signed
mapping-cone differential, so its ordinary derived functor is triangulated.
2. Resolve by a flat-term K-flat complex. Pullback keeps it K-flat. On each term
inverse image commutes with sheafified scalar tensor, by the pure-tensor map
x tensor a to the tensor of their inverse images. Balancing and sheafification
make this an invertible natural chain map; localization gives the natural iso.
The same formulas commute with shifts and the signed cone, hence with triangles.
3. Apply this exact derived functor to the canonical successive truncation triangles
for r through s. The truncation below r is acyclic and the augmentation at s is
invertible. Their images give the asserted finite sequence and its endpoints.
4. On every constant-model chart a cohomology sheaf is extension of a finitely
presented O_E-module. A finite free presentation over the DVR has finite free
kernel. Flatness of the completed coefficient sheaf over constant O_E gives the
same two-term scalar matrix after reduction. Its cohomology is finite constant
in degrees -1 and 0. The shifted q-th atom has degrees q-1 and q.
5. The long exact sequence expresses each cohomology of the next vertex as an
extension of a cokernel by a kernel. Over the finite Noetherian quotient ring,
locally constant finite-type modules form a weak Serre class (093U(3)). Induction
therefore gives finite-type locally constant cohomology at every vertex, and
support [r-1,s] at the final vertex. Shifts only reindex this property.
6. Exact restriction identifies these cohomology objects with restrictions of the
reduced cohomology on T. Finite-type models over the finite scalar ring have finite
underlying sets, so their geometric stalks are finite. The given partition works
for every n and every degree. No Noetherian or qcqs condition on a scheme is used.
Zero M and the empty scheme satisfy the same argument, with vacuous stalk clauses.
-/
theorem sp_stratified_reduction_postnikov_comparison
    (T : Scheme.{u}) (M : DerivedCategory (spStratifiedModules l E T))
    (r s : ℤ)
    (hsupport : ∀ q : ℤ, q < r ∨ s < q →
      IsZero ((DerivedCategory.homologyFunctor (spStratifiedModules l E T) q).obj M))
    (P : Scheme.FiniteLocallyClosedStratification T)
    (hconstructible : ∀ a : Fin P.n, Topology.IsConstructible (P.stratum a))
    (hlocal : ∀ (a : Fin P.n) (q : ℤ),
      letI : IsImmersion (P.immersion a) := P.isImmersion a
      HasFiniteConstantRingedLocalModel (P.domain a) (Padic.coefficientExtensionIntegers l E)
        (spStratifiedRing l E (P.domain a)) (spStratifiedScalarMap l E (P.domain a))
        ((spStratifiedPull l E (P.immersion a)).obj
          ((DerivedCategory.homologyFunctor (spStratifiedModules l E T) q).obj M))) :
    (∀ (a : Fin P.n) (n : ℕ),
      letI : IsImmersion (P.immersion a) := P.isImmersion a
      ∃ e : spStratifiedReducedPull l E (P.immersion a) n ≅
          spStratifiedPullReduced l E (P.immersion a) n,
        SpStratifiedComparisonFormula l E (P.immersion a) n e ∧
        NatTrans.CommShift e.hom ℤ ∧
        (let F := spStratifiedReducedPull l E (P.immersion a) n
         let t := DerivedCategory.TStructure.t (C := spStratifiedModules l E T)
         IsZero (F.obj ((t.truncLT r).obj M)) ∧
         IsIso (F.map ((t.truncLEι s).app M)) ∧
         (∀ q : ℤ, r ≤ q → q ≤ s →
           let Δ := (t.triangleLTLTGELT q (q + 1) (by omega)).obj M
           F.mapTriangle.obj Δ ∈ distTriang _ ∧
           Nonempty (F.obj Δ.obj₃ ≅
             F.obj (((DerivedCategory.singleFunctor (spStratifiedModules l E T) 0).obj
               ((DerivedCategory.homologyFunctor (spStratifiedModules l E T) q).obj M))⟦-q⟧)) ∧
           (∀ k : ℤ,
             Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
               ((DerivedCategory.homologyFunctor _ k).obj (F.obj Δ.obj₁)) ∧
             Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
               ((DerivedCategory.homologyFunctor _ k).obj (F.obj Δ.obj₂)) ∧
             Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
               ((DerivedCategory.homologyFunctor _ k).obj (F.obj Δ.obj₃)) ∧
             Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
               ((DerivedCategory.homologyFunctor _ k).obj ((F.obj Δ.obj₁)⟦(1 : ℤ)⟧)))) ∧
         (∀ k : ℤ,
           Scheme.IsFinitelyPresentedLocallyConstantProEtaleModule
             ((DerivedCategory.homologyFunctor _ k).obj (F.obj M))) ∧
         (∀ k : ℤ, k < r - 1 ∨ s < k →
           IsZero ((DerivedCategory.homologyFunctor _ k).obj (F.obj M))))) ∧
    (∀ (n : ℕ) (k : ℤ),
      IsConstructibleProEtaleModuleSheaf T (spStratifiedScalar l E n)
        ((DerivedCategory.homologyFunctor _ k).obj
          ((spStratifiedReduction l E T n).obj M)) ∧
      ∀ a : Fin P.n,
        IsLocallyConstantProEtaleModuleSheaf (P.domain a) (spStratifiedScalar l E n)
          (proEtaleConstantModulePullback (P.immersion a) (spStratifiedScalar l E n)
            ((DerivedCategory.homologyFunctor _ k).obj
              ((spStratifiedReduction l E T n).obj M))) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ P.domain a),
        Finite (proEtaleGeometricModuleStalk y
          (proEtaleConstantRing (P.domain a) (spStratifiedScalar l E n))
          (proEtaleConstantModulePullback (P.immersion a) (spStratifiedScalar l E n)
            ((DerivedCategory.homologyFunctor _ k).obj
              ((spStratifiedReduction l E T n).obj M))))) := by
  sorry

/-- The degreewise comparison is induced by the canonical derived isomorphism;
it is not a collection of independently chosen cohomology isomorphisms.
Source: blueprint latest, normalized-towers-reduction, coefficient-preserving
restriction paragraph; Stacks Tags 03EL and 05RS
(blueprint: lem-sp-stratified-reduction-postnikov-comparison).
Proof: the K-flat representative comparison constructed in steps 1--2 of the main
proof is defined for every immersion and every complex, before a partition or
cohomological bound is used. Apply each homology functor to its components. Functors preserve
isomorphisms, yielding exactly the displayed maps for every M and every q. -/
theorem sp_stratified_reduction_homology_comparison {S T : Scheme.{u}}
    (i : S ⟶ T) [IsImmersion i] (n : ℕ) :
    ∃ e : spStratifiedReducedPull l E i n ≅ spStratifiedPullReduced l E i n,
      SpStratifiedComparisonFormula l E i n e ∧
      ∀ (M : DerivedCategory (spStratifiedModules l E T)) (q : ℤ),
        IsIso ((DerivedCategory.homologyFunctor _ q).map (e.hom.app M)) := by
  sorry

end AlgebraicGeometry.ProEtale
