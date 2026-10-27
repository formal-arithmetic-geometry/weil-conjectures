module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.Paper.SfIntegralConstructibleTriangulated
public import Sheaf.Paper.IntegralPullbackCompletedComparison
public import Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms
public import Sheaf.Paper.SfScalarExtensionComposition
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.IntegralOpenEmptyPullbackVanishing
import Sheaf.Paper.IntegralStratumChartRestrictionsFunctorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Complementary restriction of open compact support

Source: latest blueprint, quasi-finite proof (1); Bhatt--Scholze, Lemma 6.1.12
(blueprint: lem-zl-open-compact-support-restriction-identities).
The helper structures package this node's clauses on the existing functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] WeilConjectures.integralDerivedPullback
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ZeroObject
private theorem zeroFunctorIso {C : Type*} [Category* C] {B : Type*} [Category* B]
    [HasZeroObject B] (F : C ⥤ B) (h : ∀ K, IsZero (F.obj K)) :
    Nonempty (F ≅ (Functor.const C).obj (0 : B)) := by
  exact ⟨NatIso.ofComponents (fun K ↦ (h K).isoZero)
    (fun _ ↦ (isZero_zero B).eq_of_tgt _ _)⟩

private theorem emptyModulesZero {T : Scheme.{u}} [IsEmpty T]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) (M : SheafOfModules.{u + 1} R) :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply (SheafOfModules.toSheaf R).map_injective
  exact (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty T)
    ((SheafOfModules.toSheaf R).obj M)).hom_ext _ _

private theorem emptyDerivedZero {T : Scheme.{u}} [IsEmpty T]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    [HasDerivedCategory (SheafOfModules.{u + 1} R)]
    (K : DerivedCategory (SheafOfModules.{u + 1} R)) : IsZero K := by
  have : K.IsLE 0 := (K.isLE_iff 0).2 fun _ _ ↦ emptyModulesZero R _
  have : K.IsGE 1 := (K.isGE_iff 1).2 fun _ _ ↦ emptyModulesZero R _
  exact DerivedCategory.TStructure.t.isZero K 0 1

private theorem emptyOpenExtensionZero
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {W Z : Scheme.{u}} [IsEmpty W] (j : W ⟶ Z) (hj : IsOpenImmersion j)
    (K : d.derived W) : IsZero ((cbcDerivedOpenShriek d j hj).obj K) := by
  haveI : (cbcDerivedOpenShriek d j hj).Additive := by
    unfold cbcDerivedOpenShriek
    infer_instance
  exact Functor.map_isZero _ (emptyDerivedZero _ K)

namespace WeilConjectures.ZlOpenComplement
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U₀ X₀ Z₀ : Over (Spec (.of D.k₀))}
  [hUft : LocallyOfFiniteType U₀.hom] [hUqc : QuasiCompact U₀.hom]
  [hUsep : IsSeparated U₀.hom]
  [hXft : LocallyOfFiniteType X₀.hom] [hXqc : QuasiCompact X₀.hom]
  [hXsep : IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
  (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]

include i₀ hXft in
/-- The closed complement is finite type over the base, as a composite of
its closed immersion with X₀'s structure map.
Proof: Over.w identifies this structure map with i₀.left followed by X₀.hom.
Closed immersions are locally of finite type; composition preserves this property.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
theorem closedDomainFT : LocallyOfFiniteType Z₀.hom := by
  rw [← Over.w i₀]
  infer_instance

include i₀ hXqc in
/-- Quasi-compactness of the closed complement follows from the same composite.
Proof: Over.w identifies Z₀.hom with i₀.left followed by X₀.hom.
Closed immersions are quasi-compact, and quasi-compact morphisms compose.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
theorem closedDomainQC : QuasiCompact Z₀.hom := by
  rw [← Over.w i₀]
  infer_instance

section ComplementFiniteType
variable [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]

/-- The actual geometric base change of a morphism over the finite field.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
abbrev map {W₀ T₀ : Over (Spec (.of D.k₀))} (h₀ : W₀ ⟶ T₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map h₀).left

/-- Finite type is inherited by the actual Over pullback.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
instance overPullbackFT {B T : Scheme.{u}} (f : T ⟶ B)
    (W : Over B) [LocallyOfFiniteType W.hom] :
    LocallyOfFiniteType (((Over.pullback f).obj W).left ↘ T) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd W.hom f))

/-- Quasi-compactness is inherited by the actual Over pullback.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
instance overPullbackQC {B T : Scheme.{u}} (f : T ⟶ B)
    (W : Over B) [QuasiCompact W.hom] :
    QuasiCompact (((Over.pullback f).obj W).left ↘ T) :=
  inferInstanceAs (QuasiCompact (pullback.snd W.hom f))

/-- The geometric base change of the specified open immersion.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
instance mapOpen : IsOpenImmersion (map D j₀) :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

/-- The geometric open immersion remains quasi-compact.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
instance mapQC : QuasiCompact (map D j₀) :=
  MorphismProperty.overPullbackMap (P := @QuasiCompact)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance

/-- The geometric base change of the specified closed immersion.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
instance mapClosed : IsClosedImmersion (map D i₀) :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) i₀ inferInstance

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified integral composite Li* Rj!, using compactification (j,id).
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
@[irreducible] def integral :
    sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left ⥤
      sfIntegralConstructibleCategory l E (D.geometricFiber Z₀).left :=
  sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion (map D j₀)) E ⋙
  @constructibleIntegralPullback l _ E _ _ _ _ _ (map D i₀)
    (sfWeilPrimeInvertible D l hl Z₀)
    (sfWeilPrimeInvertible D l hl X₀)

/-- The rationalized composite, on the recorded integral object carriers.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
@[irreducible] def rational :
    sfRationalConstructibleCategory l E (D.geometricFiber U₀).left ⥤
      sfRationalConstructibleCategory l E (D.geometricFiber Z₀).left :=
  sfCompactSupportFiniteFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl)
    (Compactification.ofIsOpenImmersion (map D j₀)) E ⋙
  @rationalDerivedPullback l _ E _ _ _ _ _ (map D i₀)
    (sfWeilPrimeInvertible D l hl Z₀)
    (sfWeilPrimeInvertible D l hl X₀)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The existing normalized common-stage compact-support action for (j,id).
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
def Action := SfCompactSupportCoefficientAction l D.k
  (PurCompactSupport.coefficientPrimeUnit l D hl) Ω
  (Compactification.ofIsOpenImmersion (map D j₀))

/-- The existing common-stage action followed by completed derived pullback.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
@[irreducible] def common (S : Action D l hl j₀ Ω) :
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left :=
  S.system.functor ⋙ @commonStageDerivedPullback l _ Ω _ _ _ _ _ (map D i₀)
    (sfWeilPrimeInvertible D l hl Z₀)
    (sfWeilPrimeInvertible D l hl X₀)


open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The integral and rational natural zero isomorphisms, rationalization equation,
and vanishing in the coherent strict system before any finite evaluation.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
structure StageComparison where
  integralIso : integral D l hl j₀ i₀ E ≅ (Functor.const _).obj (0 :
    sfIntegralConstructibleCategory l E (D.geometricFiber Z₀).left)
  integral_zero : integralIso.hom = 0
  rationalIso : rational D l hl j₀ i₀ E ≅ (Functor.const _).obj (0 :
    sfRationalConstructibleCategory l E (D.geometricFiber Z₀).left)
  rational_localization : ∀ K : sfRationalConstructibleCategory l E
      (D.geometricFiber U₀).left,
    ∃ h : (rational D l hl j₀ i₀ E).obj K =
        (sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left).obj
          ((integral D l hl j₀ i₀ E).obj K.obj),
      rationalIso.hom.app K = eqToHom h ≫
        (sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left).map
          (integralIso.hom.app K.obj) ≫
        (sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left).mapZeroObject.hom
  finite_zero : ∀ n : ℕ,
    Functor.whiskerRight integralIso.hom
      (integralSystemReduction l E (D.geometricFiber Z₀).left ⋙
        finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) (D.geometricFiber Z₀).left n) = 0
  strict_zero : Functor.whiskerRight integralIso.hom
      (integralSystemReduction l E (D.geometricFiber Z₀).left) = 0

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The recorded completed integral coefficient-extension functor.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
abbrev scalar (T : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι T

-- The scalar mate is the specified integral pullback mate followed by the
-- projection-normalized compact-support scalar mate.
/-- The canonical scalar mate: normalized pullback comparison followed by the
projection-normalized compact-support scalar map.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
def scalarRestriction
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left) :
    (scalar l E L ι (D.geometricFiber Z₀).left).obj
        ((integral D l hl j₀ i₀ E).obj K) ⟶
      (integral D l hl j₀ i₀ L).obj
        ((scalar l E L ι (D.geometricFiber U₀).left).obj K) := by
  unfold integral
  exact (@integralPullbackScalarComparison l _ E _ _ _ L _ _ _ ι _ _ (map D i₀)
      (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀)
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl)
        (Compactification.ofIsOpenImmersion (map D j₀)) E).obj K)).hom ≫
    (@constructibleIntegralPullback l _ L _ _ _ _ _ (map D i₀)
      (sfWeilPrimeInvertible D l hl Z₀) (sfWeilPrimeInvertible D l hl X₀)).map
        (ObjectProperty.homMk (sfCompactSupportScalarSystemMap l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          (Compactification.ofIsOpenImmersion (map D j₀)) E L ι K))

variable (hcomp : Set.range i₀.left = (Set.range j₀.left)ᶜ)

-- Canonical square, with its actual fibre product rather than a chosen empty object.
/-- The actual cartesian square of j along i, retaining its literal fibre product.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
def square : OpenImmersionSquare
    (pullback.fst (map D j₀) (map D i₀))
    (pullback.snd (map D j₀) (map D i₀)) (map D j₀) (map D i₀) where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _
  isOpenImmersion := inferInstance
  isOpenImmersion' := inferInstance

/-- The empty-open and completed-exchange normalization clauses. The equation
quantifies every identification of endpoints: maps to zero are unique, so it
includes the prescribed d_j and completed-pullback identifications without
substituting an arbitrarily chosen comparison. Strict normalization is retained
in the open-reduction Comparison and StageComparison.strict_zero.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
structure CompletedNormalization (z : StageComparison D l hl j₀ i₀ E) where
  empty : IsEmpty ↥(pullback (map D j₀) (map D i₀) : Scheme.{u})
  openReduction : ∃ (SX : CoefficientDerivedSystemCalculus l E (D.geometricFiber X₀).left)
      (SU : CoefficientDerivedSystemCalculus l E (D.geometricFiber U₀).left)
      (_cX : CoefficientDerivedSystemCoherence l E (D.geometricFiber X₀).left SX)
      (_cU : CoefficientDerivedSystemCoherence l E (D.geometricFiber U₀).left SU)
      (o : IntegralOpenReduction.Operations l E (map D j₀))
      (tensor : IntegralOpenReduction.TensorComparison l E (map D j₀) o),
    Nonempty (IntegralOpenReduction.Comparison l E (map D j₀) o SX SU tensor)
  pullbackComparison : Nonempty
    (IntegralCompletedComparison.Comparison l E (map D i₀))
  ordinary_zero : cbcDatumOrdinaryExchange (pbcIntegralDatum l E) (square D j₀ i₀) = 0
  completed_zero : ∀ (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal),
    cbcDatumCompletedExchange (pbcIntegralDatum l E) (square D j₀ i₀) r a ha = 0
  comparison_equation : ∀ (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
      (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left)
      (Q : (cbcCompleteProperty (pbcIntegralDatum l E)
        (D.geometricFiber U₀).left r a ha).FullSubcategory)
      (source : ((integral D l hl j₀ i₀ E).obj K).obj ≅
        (IntegralCompletedComparison.derived l E (D.geometricFiber Z₀).left).obj
          (((pbcIntegralDatum l E).completedPull (map D i₀)).obj
            ((cbcDerivedOpenShriek (pbcIntegralDatum l E) (map D j₀)
              (square D j₀ i₀).isOpenImmersion).obj Q.obj)))
      (target : (IntegralCompletedComparison.derived l E (D.geometricFiber Z₀).left).obj
        ((cbcDerivedOpenShriek (pbcIntegralDatum l E)
          (pullback.snd (map D j₀) (map D i₀))
          (square D j₀ i₀).isOpenImmersion').obj
            (((pbcIntegralDatum l E).completedPull
              (pullback.fst (map D j₀) (map D i₀))).obj Q.obj)) ≅
        (0 : sfIntegralConstructibleCategory l E (D.geometricFiber Z₀).left).obj),
    (z.integralIso.hom.app K).hom = source.hom ≫
      (IntegralCompletedComparison.derived l E (D.geometricFiber Z₀).left).map
        ((cbcDatumCompletedExchange (pbcIntegralDatum l E)
          (square D j₀ i₀) r a ha).app Q) ≫ target.hom
  completed_target_zero : ∀ (r : ℕ) (a : Fin r → PbcIntegralRing l E)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum l E)
        (D.geometricFiber U₀).left r a ha).FullSubcategory),
    IsZero ((cbcDerivedOpenShriek (pbcIntegralDatum l E)
      (pullback.snd (map D j₀) (map D i₀))
      (square D j₀ i₀).isOpenImmersion').obj
        (((pbcIntegralDatum l E).completedPull
          (pullback.fst (map D j₀) (map D i₀))).obj K.obj))

/-- Finite-extension compatibility, its actual scalar associator square, and the
common-stage image of the rationalized integral zero comparison.
Source: blueprint, quasi-finite proof (1), complementary restriction
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
structure FieldDescent
    (z : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E], StageComparison D l hl j₀ i₀ E) where
  scalar_compatibility : ∀ (E L : Type u) [Field E] [Field L]
      [Algebra (Padic l) E] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L)
      (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
    scalarRestriction D l hl j₀ i₀ E L ι K ≫
        (z L).integralIso.hom.app ((scalar l E L ι (D.geometricFiber U₀).left).obj K) =
      (scalar l E L ι (D.geometricFiber Z₀).left).map ((z E).integralIso.hom.app K) ≫
        (0 : (scalar l E L ι (D.geometricFiber Z₀).left).obj 0 ⟶ 0)
  scalar_associator : ∀ (E L M : Type u) [Field E] [Field L] [Field M]
      [Algebra (Padic l) E] [Algebra (Padic l) L] [Algebra (Padic l) M]
      [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
      [FiniteDimensional (Padic l) M] (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M)
      (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
    (sfIntegralScalarComp l E L ι (D.geometricFiber Z₀).left 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app
        ((integral D l hl j₀ i₀ E).obj K) ≫
      scalarRestriction D l hl j₀ i₀ E M (κ.comp ι) K ≫
      (z M).integralIso.hom.app
        ((scalar l E M (κ.comp ι) (D.geometricFiber U₀).left).obj K) =
    (scalar l L M κ (D.geometricFiber Z₀).left).map
        (scalarRestriction D l hl j₀ i₀ E L ι K) ≫
      scalarRestriction D l hl j₀ i₀ L M κ
        ((scalar l E L ι (D.geometricFiber U₀).left).obj K) ≫
      (integral D l hl j₀ i₀ M).map
        ((sfIntegralScalarComp l E L ι (D.geometricFiber U₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M κ).hom.app K) ≫
      (z M).integralIso.hom.app
        ((scalar l E M (κ.comp ι) (D.geometricFiber U₀).left).obj K)
  commonIso : ∀ S : Action D l hl j₀ Ω, common D l hl j₀ i₀ Ω S ≅ (Functor.const _).obj
    (0 : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Z₀).left)
  common_normalization : ∀ (S : Action D l hl j₀ Ω)
      (F : Padic.FiniteCoefficientFields l Ω)
      (K : Stage l Ω (D.geometricFiber U₀).left F),
    ∃ h : (common D l hl j₀ i₀ Ω S).obj ⟨F, K⟩ =
        (inclusion (l := l) (Ω := Ω) (Y := (D.geometricFiber Z₀).left) F).obj
          ((rational D l hl j₀ i₀ (Coefficient.{u} l Ω F)).obj K),
      (commonIso S).hom.app ⟨F, K⟩ = eqToHom h ≫
        (inclusion (l := l) (Ω := Ω) (Y := (D.geometricFiber Z₀).left) F).map
          ((z (Coefficient.{u} l Ω F)).rationalIso.hom.app K) ≫
        (inclusion (l := l) (Ω := Ω)
          (Y := (D.geometricFiber Z₀).left) F).mapZeroObject.hom

/-- Prime invertibility at any geometric test point, induced from its map to X.
Source: blueprint, quasi-finite proof (1), arbitrary geometric points
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
@[instance_reducible] def pointInvertible {F : Type u} [Field F]
    (g : Spec (.of F) ⟶ (D.geometricFiber X₀).left)
    (x : Spec (.of F)) : Invertible (l : (Spec (.of F)).residueField x) :=
  (show IsUnit (l : (Spec (.of F)).residueField x) from
    by simpa only [map_natCast] using
      (D.geometricFiber_coefficientPrimeInvertible l hl X₀ (g x)).map
        (g.residueFieldMap x).hom).invertible

/-- The last clause, at every algebraically closed test field and every geometric
point missing U. No closedness of the image point is required.
Source: blueprint, quasi-finite proof (1)
(blueprint: lem-zl-open-compact-support-restriction-identities). -/
def GeometricVanishing : Prop :=
  ∀ (F : Type u) [Field F] [IsAlgClosed F]
    (g : Spec (.of F) ⟶ (D.geometricFiber X₀).left)
    (_hg : Disjoint (Set.range g) (Set.range (map D j₀))),
    ∃ f : Spec (.of F) ⟶ (D.geometricFiber Z₀).left,
      f ≫ map D i₀ = g ∧
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E]
        (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((integralDerivedPullback l E f).obj
          ((integral D l hl j₀ i₀ E).obj K).obj)) ∧
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E]
        (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left),
        IsZero ((@rationalDerivedPullback l _ E _ _ _ _ _ f
          (pointInvertible D l hl g) (sfWeilPrimeInvertible D l hl Z₀)).obj
            ((rational D l hl j₀ i₀ E).obj K))) ∧
      (∀ (S : Action D l hl j₀ Ω)
        (K : generalAlgebraicallyClosedConstructibleCategory l Ω
          (D.geometricFiber U₀).left),
        IsZero ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ f
          (pointInvertible D l hl g) (sfWeilPrimeInvertible D l hl Z₀)).obj
            ((common D l hl j₀ i₀ Ω S).obj K)))

end ComplementFiniteType

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (hcomp : Set.range i₀.left = (Set.range j₀.left)ᶜ)

section
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)
variable [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]

private theorem baseChangeRange {W₀ : Over (Spec (.of D.k₀))} (f₀ : W₀ ⟶ X₀) :
    Set.range (map D f₀) =
      (pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⁻¹' Set.range f₀.left := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hm : map D f₀ = pullback.map W₀.hom b X₀.hom b
      f₀.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [map, b]
  rw [hm]
  have hid : Set.range (𝟙 (Spec (.of D.k)) : Spec (.of D.k) ⟶ _) = Set.univ :=
    Set.range_eq_univ.mpr (fun x ↦ ⟨x, rfl⟩)
  simpa only [hid, Set.preimage_univ, Set.inter_univ, b, Over.pullback_obj_left] using
    (Pullback.range_map (f := W₀.hom) (g := b) X₀.hom b f₀.left
      (𝟙 _) (𝟙 _) (by simp) (by simp))

include hcomp in
private theorem complementRange :
    Set.range (map D i₀) = (Set.range (map D j₀))ᶜ := by
  rw [baseChangeRange D i₀, baseChangeRange D j₀, hcomp]
  rfl

include hcomp in
private theorem emptySquare : IsEmpty ↥(pullback (map D j₀) (map D i₀) : Scheme.{u}) := by
  rw [Scheme.isEmpty_pullback_iff, complementRange D j₀ i₀ hcomp]
  exact disjoint_compl_right

include hcomp in
private theorem pointFactor {F : Type u} [Field F]
    (g : Spec (.of F) ⟶ (D.geometricFiber X₀).left)
    (hg : Disjoint (Set.range g) (Set.range (map D j₀))) :
    ∃ f : Spec (.of F) ⟶ (D.geometricFiber Z₀).left, f ≫ map D i₀ = g := by
  have hr : Set.range g ⊆ Set.range (map D i₀) := by
    rw [complementRange D j₀ i₀ hcomp]
    exact Set.disjoint_left.mp hg
  have hs : Surjective (pullback.snd (map D i₀) g) := by
    rw [surjective_iff, ← Set.range_eq_univ, Pullback.range_snd]
    exact Set.eq_univ_of_forall (fun x ↦ hr ⟨x, rfl⟩)
  letI := hs
  have hi : IsIso (pullback.snd (map D i₀) g) :=
    isIso_of_isClosedImmersion_of_surjective _
  letI := hi
  refine ⟨inv (pullback.snd (map D i₀) g) ≫ pullback.fst (map D i₀) g, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

include hcomp in
private theorem integralZero (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber U₀).left) :
    IsZero ((integral D l hl j₀ i₀ E).obj K) := by
  letI := emptySquare D j₀ i₀ hcomp
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  unfold integral
  exact integralOpenEmptyPullbackVanishing l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) (map D j₀) (map D i₀) K

private theorem rationalObject (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left) :
    (rational D l hl j₀ i₀ E).obj K =
      (sfRationalConstructibleLocalization l E (D.geometricFiber Z₀).left).obj
        ((integral D l hl j₀ i₀ E).obj K.obj) := by
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  unfold rational integral
  exact (rationalDerivedPullback_existsUnique l E (map D i₀)).exists.choose_spec.2.1 _

private theorem commonObject (S : Action D l hl j₀ Ω)
    (F : Padic.FiniteCoefficientFields l Ω)
    (K : Stage l Ω (D.geometricFiber U₀).left F) :
    (common D l hl j₀ i₀ Ω S).obj ⟨F, K⟩ =
      (inclusion (l := l) (Ω := Ω) (Y := (D.geometricFiber Z₀).left) F).obj
        ((rational D l hl j₀ i₀ (Coefficient.{u} l Ω F)).obj K) := by
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Z₀
  unfold common
  dsimp only [Functor.comp_obj, StageSystem.Morphism.functor_obj]
  rw [S.finite_eq]
  simpa only [commonStageDerivedPullback, commonStagePullbackObject,
    rational, Functor.comp_obj, FiniteFieldDatum.geometricFiber,
    inclusion, StageSystem.ι_obj] using
    (commonStageDerivedPullback_existsUnique l Ω (map D i₀)).exists.choose_spec.1
      ⟨F, (sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl)
        (Compactification.ofIsOpenImmersion (map D j₀)) (Coefficient.{u} l Ω F)).obj K⟩

include hcomp in
private theorem rationalZero (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfRationalConstructibleCategory l E (D.geometricFiber U₀).left) :
    IsZero ((rational D l hl j₀ i₀ E).obj K) := by
  rw [rationalObject D l hl j₀ i₀ E K]
  exact Functor.map_isZero _ (integralZero D l hl j₀ i₀ hcomp E K.obj)

include hcomp in
private theorem commonZero (S : Action D l hl j₀ Ω)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber U₀).left) :
    IsZero ((common D l hl j₀ i₀ Ω S).obj K) := by
  rcases K with ⟨F, K⟩
  rw [commonObject D l hl j₀ i₀ Ω S F K]
  exact Functor.map_isZero _ (rationalZero D l hl j₀ i₀ hcomp _ K)

include hcomp in
@[irreducible] private def stageComparison (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] : StageComparison D l hl j₀ i₀ E where
  integralIso := (zeroFunctorIso _ (integralZero D l hl j₀ i₀ hcomp E)).some
  integral_zero := by
    apply NatTrans.ext
    funext K
    exact (isZero_zero (sfIntegralConstructibleCategory l E
      (D.geometricFiber Z₀).left)).eq_of_tgt _ _
  rationalIso := (zeroFunctorIso _ (rationalZero D l hl j₀ i₀ hcomp E)).some
  rational_localization := by
    intro K
    refine ⟨rationalObject D l hl j₀ i₀ E K, ?_⟩
    exact (isZero_zero _).eq_of_tgt _ _
  finite_zero := by
    intro n
    ext K
    dsimp only [Functor.whiskerRight_app, NatTrans.app_zero]
    let S := (coefficientDerivedSystemEvaluationCalculus l E
      (D.geometricFiber Z₀).left).choose
    letI : S.reduction.IsLeftAdjoint := S.adjunction.isLeftAdjoint
    letI : S.reduction.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isLeftAdjoint S.reduction
    haveI : (integralSystemReduction l E (D.geometricFiber Z₀).left).PreservesZeroMorphisms := by
      change ((sfIntegralConstructible l E (D.geometricFiber Z₀).left).ι ⋙
        S.reduction).PreservesZeroMorphisms
      exact Functor.preservesZeroMorphisms_comp _ _
    exact (Functor.map_isZero
      (integralSystemReduction l E (D.geometricFiber Z₀).left ⋙
        finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) (D.geometricFiber Z₀).left n)
      (isZero_zero _)).eq_of_tgt _ _
  strict_zero := by
    ext K
    dsimp only [Functor.whiskerRight_app, NatTrans.app_zero]
    let S := (coefficientDerivedSystemEvaluationCalculus l E
      (D.geometricFiber Z₀).left).choose
    letI : S.reduction.IsLeftAdjoint := S.adjunction.isLeftAdjoint
    letI : S.reduction.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isLeftAdjoint S.reduction
    haveI : (integralSystemReduction l E (D.geometricFiber Z₀).left).PreservesZeroMorphisms := by
      change ((sfIntegralConstructible l E (D.geometricFiber Z₀).left).ι ⋙
        S.reduction).PreservesZeroMorphisms
      exact Functor.preservesZeroMorphisms_comp _ _
    exact (Functor.map_isZero
      (integralSystemReduction l E (D.geometricFiber Z₀).left)
      (isZero_zero _)).eq_of_tgt _ _

include hcomp in
private theorem fieldDescent
    (z : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E], StageComparison D l hl j₀ i₀ E) :
    Nonempty (FieldDescent D l hl j₀ i₀ Ω z) := by
  refine ⟨{
    scalar_compatibility := ?_
    scalar_associator := ?_
    commonIso := fun S ↦ (zeroFunctorIso _ (commonZero D l hl j₀ i₀ Ω hcomp S)).some
    common_normalization := ?_ }⟩
  · intros
    exact (isZero_zero _).eq_of_tgt _ _
  · intros
    exact (isZero_zero _).eq_of_tgt _ _
  · intro S F K
    exact ⟨commonObject D l hl j₀ i₀ Ω S F K, (isZero_zero _).eq_of_tgt _ _⟩

private theorem globalPrimeUnit (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)] : IsUnit (l : Γ(T, ⊤)) := by
  apply AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ T.toSheafedSpace ⊤
  intro x _
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  simpa only [map_natCast] using (isUnit_of_invertible (l : T.residueField x)).ne_zero

include hcomp in
private theorem completedNormalization
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (z : StageComparison D l hl j₀ i₀ E) :
    Nonempty (CompletedNormalization D l hl j₀ i₀ E z) := by
  letI := emptySquare D j₀ i₀ hcomp
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl U₀
  have hz (K : (pbcIntegralDatum l E).derived (D.geometricFiber U₀).left) :
      IsZero ((cbcDerivedOpenShriek (pbcIntegralDatum l E)
        (pullback.snd (map D j₀) (map D i₀))
        (square D j₀ i₀).isOpenImmersion').obj
          (((pbcIntegralDatum l E).completedPull
            (pullback.fst (map D j₀) (map D i₀))).obj K)) :=
    emptyOpenExtensionZero _ _ _ _
  refine ⟨{
    empty := inferInstance
    openReduction := IntegralOpenReduction.integralOpenReductionComparison l E (map D j₀)
      (globalPrimeUnit l _) (globalPrimeUnit l _)
    pullbackComparison := IntegralCompletedComparison.integralPullback_completedComparison
      l E (map D i₀) ?_ ?_
    ordinary_zero := ?_
    completed_zero := ?_
    comparison_equation := ?_
    completed_target_zero := fun _ _ _ K ↦ hz K.obj }⟩
  · intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (D.geometricFiber_coefficientPrimeInvertible l hl Z₀ x).ne_zero
  · intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (D.geometricFiber_coefficientPrimeInvertible l hl X₀ x).ne_zero
  · ext K
    exact (emptyOpenExtensionZero _ _ _ _).eq_of_tgt _ _
  · intro r a ha
    ext K
    exact (hz K.obj).eq_of_tgt _ _
  · intros
    exact (Functor.map_isZero (sfIntegralConstructible l E
      (D.geometricFiber Z₀).left).ι (isZero_zero _)).eq_of_tgt _ _

include hcomp in
private theorem geometricVanishing : GeometricVanishing D l hl j₀ i₀ Ω := by
  intro F _ _ g hg
  letI := pointInvertible D l hl g
  letI := sfWeilPrimeInvertible D l hl Z₀
  obtain ⟨f, hf⟩ := pointFactor D j₀ i₀ hcomp g hg
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro E _ _ _ K
    have : LocallyOfFiniteType (D.geometricFiber Z₀).hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd Z₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    have : QuasiCompact (D.geometricFiber Z₀).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd Z₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    have : IsNoetherian (D.geometricFiber Z₀).left :=
      isNoetherian_of_locallyOfFiniteType (D.geometricFiber Z₀).hom
    have hstalk (T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]
        (x : T) : IsUnit (l : T.presheaf.stalk x) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      simpa only [map_natCast] using (isUnit_of_invertible (l : T.residueField x)).ne_zero
    obtain ⟨c⟩ := IntegralCompletedComparison.integralPullback_completedComparison
      l E f (hstalk _) (hstalk _)
    have : (integralDerivedPullback l E f).Additive :=
      (IntegralStratumCharts.integral_stratum_pullback_functorial l E f
        (exists_topologicalKrullDim_le (D.geometricFiber Z₀).hom)
        (exists_topologicalKrullDim_le (𝟙 (Spec (.of F))))
        (globalPrimeUnit l _) (globalPrimeUnit l _) c).1
    exact Functor.map_isZero _ (Functor.map_isZero
      (sfIntegralConstructible l E (D.geometricFiber Z₀).left).ι
      (integralZero D l hl j₀ i₀ hcomp E K))
  · intro E _ _ _ K
    haveI : (@rationalDerivedPullback l _ E _ _ _ _ _ f
        (pointInvertible D l hl g) (sfWeilPrimeInvertible D l hl Z₀)).Additive :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.1
    exact Functor.map_isZero _ (rationalZero D l hl j₀ i₀ hcomp E K)
  · intro S K
    let P := commonStageDerivedPullback l Ω f
    let A := Padic.finiteCoefficientBase l Ω
    let I := inclusion (l := l) (Ω := Ω) (Y := (D.geometricFiber Z₀).left) A
    let N := I.obj (0 : Stage l Ω (D.geometricFiber Z₀).left A)
    have hN : IsZero N := Functor.map_isZero I (isZero_zero _)
    have hzN : IsZero (P.obj N) := by
      change IsZero ((commonStageDerivedPullback l Ω f).obj N)
      unfold commonStageDerivedPullback
      rw [(commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 N]
      change IsZero ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of F)) A).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω A) f).obj 0))
      haveI : (rationalDerivedPullback l (Coefficient.{u} l Ω A) f).Additive :=
        (rationalDerivedPullback_existsUnique l (Coefficient.{u} l Ω A)
          f).exists.choose_spec.1
      exact Functor.map_isZero _ (Functor.map_isZero _ (isZero_zero _))
    have hz : IsZero (P.obj 0) := hzN.of_iso (P.mapIso hN.isoZero).symm
    letI : P.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_map_zero_object hz.isoZero
    exact Functor.map_isZero P (commonZero D l hl j₀ i₀ Ω hcomp S K)

end

include hcomp hUsep hXsep in
/-- Complementary restriction of open compact support is canonically zero at
integral, rational and algebraically closed common stages, with the specified
completed/open-reduction normalization and at every geometric point outside U.
Source: latest blueprint, sec-deligne-laumon-general/sk-l-dl-general-quasifinite,
lem-zl-quasi-finite.proof.md (1); Bhatt--Scholze, Lemma 6.1.12
(blueprint: lem-zl-open-compact-support-restriction-identities).

Proof: the complement hypothesis makes the actual fibre product U ×_X Z empty.
The empty cover makes every module sheaf on it zero. Direct-sum extension from
this site is zero before sheafification, and hence after it and termwise on
complexes. Use the specified integral open-reduction comparison d_j and its
strict comparison r_j, and the integral/completed pullback comparison, to
identify Li* Rj! with the source of completed open exchange. That exchange is
invertible and its target is extension from the empty open, hence zero. Its
strict reduction is the zero morphism of coherent systems, including all
quotient transitions; evaluation gives the zero map at every finite level.
Since every morphism into a zero object is unique, this identifies the resulting
isomorphism with the displayed completed-exchange composite for every endpoint
identification, in particular the canonical d_j comparison. Localize the
integral map on objects and Hom groups to obtain the rational isomorphism.
The normalized compact-support and pullback scalar mates give the displayed
scalar square; uniqueness into zero also proves its actual associator square.
Pass these maps to common stages, where the same uniqueness proves independence
of all further finite extensions. Finally any field-valued point missing U
factors through Z: on an affine neighbourhood its kernel prime contains the
ideal cutting out Z, so the ring map factors uniquely through the quotient.
These local factorizations glue because a closed immersion is a monomorphism.
Pullback preserves zero on strict finite towers and their derived-limit
construction, and therefore also after rationalization and common-stage descent.
This argument imposes no closedness on the image of the geometric point. -/
theorem restrictionIdentities :
    letI : LocallyOfFiniteType Z₀.hom := closedDomainFT D i₀
    letI : QuasiCompact Z₀.hom := closedDomainQC D i₀
    ∃ z : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E], StageComparison D l hl j₀ i₀ E,
      Nonempty (FieldDescent D l hl j₀ i₀ Ω z) ∧
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E], Nonempty (CompletedNormalization D l hl j₀ i₀ E (z E))) ∧
      GeometricVanishing D l hl j₀ i₀ Ω := by
  letI := closedDomainFT D i₀
  letI := closedDomainQC D i₀
  exact ⟨stageComparison D l hl j₀ i₀ hcomp,
    fieldDescent D l hl j₀ i₀ Ω hcomp _,
    fun E _ _ _ ↦ completedNormalization D l hl j₀ i₀ hcomp E _,
    geometricVanishing D l hl j₀ i₀ Ω hcomp⟩

end WeilConjectures.ZlOpenComplement
