/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Root-normalized frames of the internal Tate module

Source: current blueprint, coefficient twists (order 1251) and Frobenius on coefficient
 twists (order 2855). (blueprint: lem-pur-condensed-internal-tate-frame).

All lines below are the published internal-module constructions. Positive root levels
are indexed by n : N with exponent n+1; the upstream Tate tower also has its zero level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  Functor.LaxMonoidal
open scoped CategoryTheory.Obj CategoryTheory.MonObj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The prescribed root as a global section of the actual sheafification of roots.
Source: coefficient twists, finite-root display
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameRoot (D : WeilConjectures.FiniteFieldDatum.{u}) (m : ℕ)
    (z : rootsOfUnity m D.k) :
    𝟙_ (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ⟶
      rootsOfUnitySheaf (Spec (.of D.k)) m :=
  ε (presheafToSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ≫
    (presheafToSheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}).map
      (Sheaf.unitPresheafHomOfSection (Scheme.ProEt.isTerminalMkId (Spec (.of D.k)))
        (P := rootsOfUnityPresheaf (Spec (.of D.k)) m)
        (ULift.up (Additive.ofMul
          (restrictRootsOfUnity (Scheme.ΓSpecIso (.of D.k)).inv.hom m z))))

/-- The section 1 tensor z of a free internal module on an abelian root sheaf.
Source: internal tensor F_r, not the free module on a set
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameFreeRoot (D : WeilConjectures.FiniteFieldDatum.{u}) (m : ℕ)
    (z : rootsOfUnity m D.k)
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) [MonObj R] :
    𝟙_ (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}) ⟶
      ((Mod.freeFunctor R).obj (rootsOfUnitySheaf (Spec (.of D.k)) m)).X :=
  (λ_ _).inv ≫ (η[R] ⊗ₘ purFrameRoot D m z)

/-- The scalar inclusion from Z_l into the recorded ring of integers of E.
Source: coefficient twists, O_E scalar action
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameIntMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ℤ_[l] →+* Padic.coefficientExtensionIntegers l E :=
  ((algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom).codRestrict _ (fun x ↦ by
    apply ((Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 _).mpr
    change spectralNorm ℚ_[l] E (algebraMap ℚ_[l] E (x : ℚ_[l])) ≤ 1
    rw [spectralNorm_extends]
    exact PadicInt.norm_le_one x)

/-- The ring-sheaf presentation of the published integral coefficient ring object.
Source: pulled-back continuous coefficients
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameIntRingSheaf (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionIntegers l E)

/-- Condensed scalar inclusion, with source in Type 0 and target in the scheme universe.
Source: pulled-back continuous coefficients in the coefficient-twist definition
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameIntRingMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Profinite.padicIntCondensedRing.{u} l ⟶
      purFrameIntRingSheaf l E := by
  letI := spectralNorm.normedField ℚ_[l] E
  letI := spectralNorm.normedAlgebra ℚ_[l] E
  refine ⟨?_⟩
  exact
    { app := fun T ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((purFrameIntMap l E).compLeftContinuous T.unop
            (((continuous_algebraMap ℚ_[l] E).comp continuous_subtype_val).subtype_mk _)).comp
              ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }

/-- The same structural coefficient map on abelian ring objects.
Source: O_E tensor over R_s (blueprint: lem-pur-condensed-internal-tate-frame). -/
abbrev purFrameIntCondensedMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶ twistIntegralRing l E :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (purFrameIntRingMap l E)

/-- The finite projection of the framed Tate-module basis.
Source: b_T normalization in coefficient twists
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def PurFrameTateNormalized (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (b : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
        (Spec (.of D.k))) ≅ tateModule (Spec (.of D.k)) l) : Prop :=
  ∀ n : ℕ, η[condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
      (Spec (.of D.k))] ≫ b.hom.hom ≫
      (limit.π (tateModuleSystem (Spec (.of D.k)) l) (op (n + 1))).hom =
    purFrameFreeRoot D (l ^ (n + 1)) (z n) _

/-- The finite coordinates of the integral frame, using the fixed exponent n+1.
Source: e_E and the integral-limit display
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def PurFrameIntegralNormalized (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (b : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l E (Spec (.of D.k))) : Prop :=
  ∀ n : ℕ, η[condensedRingObj (twistIntegralRing l E)
      (Spec (.of D.k))] ≫ b.hom.hom ≫
      (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k))) (op n)).hom =
    purFrameFreeRoot D (l ^ (n + 1)) (z n)
      (condensedRingObj (twistFiniteRing l E n) (Spec (.of D.k)))

/-- Scalar extension of a frame, sending 1 to 1 tensor the given generator.
Source: scalar-extension displays (blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameExtend {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (f : R ⟶ S) [IsMonHom f]
    {M : Mod C R} (b : Mod.regular R ≅ M) :
    Mod.regular S ≅ (Mod.extendScalars f).obj M :=
  (Mod.extendScalarsObjRegularIso f).symm ≪≫ (Mod.extendScalars f).mapIso b

/-- The root-preserving comparison between scalar extensions of framed lines.
Source: c_E and the rational and algebraically closed comparisons
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameCompare {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (f : R ⟶ S) [IsMonHom f]
    {M : Mod C R} {N : Mod C S} (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N) :
    (Mod.extendScalars f).obj M ≅ N :=
  (purFrameExtend f b).symm ≪≫ c

/-- Continuous field inclusion between the recorded spectral coefficient fields.
Source: finite coefficient inclusions (blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameFieldMap (l : ℕ) [Fact l.Prime] {E F : Type u}
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F) :
    twistRationalRing l E ⟶ twistRationalRing l F :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI := spectralNorm.normedSpace ℚ_[l] E
  letI := spectralNorm.normedField ℚ_[l] F
  letI := spectralNorm.normedSpace ℚ_[l] F
  twistContinuousMap i.toRingHom i.toLinearMap.continuous_of_finiteDimensional

/-- The ring-sheaf presentation of the recorded rational coefficient ring.
Source: E coefficient paragraph (blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameRationalRingSheaf (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := spectralNorm.normedField ℚ_[l] E
  Profinite.continuousCoefficientRingSheaf E

/-- The ring-sheaf inclusion of a finite field into the actual finite-subextension-valued
condensed algebraic closure. The embedding, rather than an arbitrary sheaf map, determines it.
Source: algebraically closed comparison (blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameQbarRingMap (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    purFrameRationalRingSheaf l E ⟶ Profinite.padicAlgClCondensedRing.{u} l := by
  letI := spectralNorm.normedField ℚ_[l] E
  letI := spectralNorm.normedSpace ℚ_[l] E
  refine ⟨?_⟩
  exact
    { app := fun T ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((i.toRingHom.compLeftContinuous T.unop
              i.toLinearMap.continuous_of_finiteDimensional).codRestrict
            (PadicAlgCl.finiteIntermediateFieldValued l T.unop)
            (fun a ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff l _ _).mpr
              ⟨i.fieldRange, i.toLinearMap.finiteDimensional_range,
                fun x ↦ ⟨a x, rfl⟩⟩)).comp ULift.ringEquiv.toRingHom))
      naturality := fun _ _ _ ↦ rfl }

/-- The same inclusion of coefficient ring objects.
Source: algebraically closed comparison (blueprint: lem-pur-condensed-internal-tate-frame). -/
abbrev purFrameQbarMap (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (i : E →ₐ[ℚ_[l]] PadicAlgCl l) :
    twistRationalRing l E ⟶ Profinite.padicAlgClRingObj.{u} l :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (purFrameQbarRingMap l E i)

/-- The balanced reduction of O_E tensor T to the fixed finite root line. Its formula
is a tensor of the coefficient quotient with the root projection, followed by multiplication.
Source: c_E finite projection clause (blueprint: lem-pur-condensed-internal-tate-frame). -/
def purFrameFiniteProjection (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    condensedRingObj (twistIntegralRing l E) (Spec (.of D.k)) ⊗
        (tateModule (Spec (.of D.k)) l).X ⟶
      (coefficientIntegralTwistLevel l E (Spec (.of D.k)) n).X :=
  (𝟙 _ ⊗ₘ (limit.π (tateModuleSystem (Spec (.of D.k)) l) (op (n + 1))).hom) ≫
    (α_ _ _ _).inv ≫
    ((coefficientMap (twistReduction l E n) (Spec (.of D.k)) ⊗ₘ
      (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k)) ≫
        coefficientMap (twistReduction l E n) (Spec (.of D.k)))) ▷ _) ≫
    (MonObj.mul ▷ _)

/-- A comparison sends the scalar-extended source generator to the target generator.
Source: all displayed root formulas (blueprint: lem-pur-condensed-internal-tate-frame). -/
def PurFrameComparisonNormalized {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (f : R ⟶ S) [IsMonHom f]
    {M : Mod C R} {N : Mod C S} (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N)
    (e : (Mod.extendScalars f).obj M ≅ N) : Prop :=
  η[R] ≫ b.hom.hom ≫ Mod.extendUnitHom f M ≫ e.hom.hom = η[S] ≫ c.hom.hom

/-- Composition of the specified coefficient comparisons, with the ordinary balancing
associator S'' tensor_S' (S' tensor_S M) = S'' tensor_S M.
Source: coefficient-inclusion chain clause
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def PurFrameComparisonComp {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C]
    [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] (g : S ⟶ T) [IsMonHom g]
    {M : Mod C R} {N : Mod C S} {P : Mod C T}
    (b : Mod.regular R ≅ M) (c : Mod.regular S ≅ N) (d : Mod.regular T ≅ P) : Prop :=
  ((Mod.extendScalarsComp f g).hom.app M) ≫
      (Mod.extendScalars g).map (purFrameCompare f b c).hom ≫
        (purFrameCompare g c d).hom = (purFrameCompare (f ≫ g) b d).hom

/-- The rational frame obtained by extending the actual integral frame.
Source: E(1) scalar-extension display
(blueprint: lem-pur-condensed-internal-tate-frame). -/
abbrev purFrameRationalBasis (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (b : Mod.regular (condensedRingObj (twistIntegralRing l E) X) ≅
      coefficientIntegralTwistOne l E X) :=
  purFrameExtend (coefficientMap (twistIntegralToRational l E) X) b

/-- The algebraically closed frame of the published tateTwistOne construction.
Source: Omega(1) scalar-extension display
(blueprint: lem-pur-condensed-internal-tate-frame). -/
abbrev purFrameQbarBasis (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (b : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X) ≅
      tateModule X l) :=
  purFrameExtend (coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X) b

/-- Every clause of the finite-coefficient comparisons, including finite projections,
rational and algebraically closed generators, and composition of coefficient inclusions.
Source: framed internal comparison, coefficient twists and Frobenius coefficient twists
(blueprint: lem-pur-condensed-internal-tate-frame). -/
def PurFrameCoefficientLaws (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (z : ∀ n : ℕ, rootsOfUnity (l ^ (n + 1)) D.k)
    (bT : Mod.regular (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l])
        (Spec (.of D.k))) ≅ tateModule (Spec (.of D.k)) l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (iE : E →ₐ[ℚ_[l]] PadicAlgCl l)
    (bE : Mod.regular (condensedRingObj (twistIntegralRing l E) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l E (Spec (.of D.k))) : Prop :=
  PurFrameComparisonNormalized
    (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k))) bT bE
    (purFrameCompare (coefficientMap (purFrameIntCondensedMap l E)
      (Spec (.of D.k))) bT bE) ∧
  (∀ c : (Mod.extendScalars
      (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k)))).obj
        (tateModule (Spec (.of D.k)) l) ≅
          coefficientIntegralTwistOne l E (Spec (.of D.k)),
    PurFrameComparisonNormalized
      (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k))) bT bE c →
    c = purFrameCompare (coefficientMap (purFrameIntCondensedMap l E)
      (Spec (.of D.k))) bT bE) ∧
  (∀ n : ℕ,
    Mod.extendπ (coefficientMap (purFrameIntCondensedMap l E) (Spec (.of D.k)))
        (tateModule (Spec (.of D.k)) l) ≫
      (purFrameCompare (coefficientMap (purFrameIntCondensedMap l E)
        (Spec (.of D.k))) bT bE).hom.hom ≫
          (limit.π (coefficientIntegralTwistSystem l E (Spec (.of D.k))) (op n)).hom =
            purFrameFiniteProjection D l E n) ∧
  PurFrameComparisonNormalized
    (coefficientMap (purFrameQbarMap l E iE) (Spec (.of D.k)))
    (purFrameRationalBasis l E (Spec (.of D.k)) bE)
    (purFrameQbarBasis l (Spec (.of D.k)) bT)
    (purFrameCompare (coefficientMap (purFrameQbarMap l E iE) (Spec (.of D.k)))
      (purFrameRationalBasis l E (Spec (.of D.k)) bE)
      (purFrameQbarBasis l (Spec (.of D.k)) bT)) ∧
  (∀ (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (iF : F →ₐ[ℚ_[l]] PadicAlgCl l) (f : E →ₐ[ℚ_[l]] F), iF.comp f = iE →
    ∀ bF : Mod.regular (condensedRingObj (twistIntegralRing l F) (Spec (.of D.k))) ≅
      coefficientIntegralTwistOne l F (Spec (.of D.k)),
      PurFrameIntegralNormalized D l z F bF →
    PurFrameComparisonNormalized
      (coefficientMap (purFrameFieldMap l f) (Spec (.of D.k)))
      (purFrameRationalBasis l E (Spec (.of D.k)) bE)
      (purFrameRationalBasis l F (Spec (.of D.k)) bF)
      (purFrameCompare (coefficientMap (purFrameFieldMap l f) (Spec (.of D.k)))
        (purFrameRationalBasis l E (Spec (.of D.k)) bE)
        (purFrameRationalBasis l F (Spec (.of D.k)) bF)) ∧
    PurFrameComparisonComp
      (coefficientMap (purFrameFieldMap l f) (Spec (.of D.k)))
      (coefficientMap (purFrameQbarMap l F iF) (Spec (.of D.k)))
      (purFrameRationalBasis l E (Spec (.of D.k)) bE)
      (purFrameRationalBasis l F (Spec (.of D.k)) bF)
      (purFrameQbarBasis l (Spec (.of D.k)) bT) ∧
    ∀ (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
      (iG : G →ₐ[ℚ_[l]] PadicAlgCl l) (g : F →ₐ[ℚ_[l]] G), iG.comp g = iF →
      ∀ bG : Mod.regular (condensedRingObj (twistIntegralRing l G) (Spec (.of D.k))) ≅
        coefficientIntegralTwistOne l G (Spec (.of D.k)),
        PurFrameIntegralNormalized D l z G bG →
      PurFrameComparisonComp
        (coefficientMap (purFrameFieldMap l f) (Spec (.of D.k)))
        (coefficientMap (purFrameFieldMap l g) (Spec (.of D.k)))
        (purFrameRationalBasis l E (Spec (.of D.k)) bE)
        (purFrameRationalBasis l F (Spec (.of D.k)) bF)
        (purFrameRationalBasis l G (Spec (.of D.k)) bG))

end AlgebraicGeometry.ProEtale
