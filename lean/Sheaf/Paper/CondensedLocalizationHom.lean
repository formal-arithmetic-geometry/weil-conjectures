/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.StratifiedDualizableHomContinuity
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Sheaf.CategoryTheory.RingedSiteModules

import Sheaf.CategoryTheory.RingedSiteLocalization
import Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection
import Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore
import Sheaf.Paper.StratifiedDualizableBounded
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Hom localization for stratified dualizable condensed sheaves

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.3,
Section 5.3, Proposition 5.5 (blueprint: lem-pod-condensed-localization-hom).

## Main definitions and statements

* `localized`: actual condensed coefficient localization.
* `stratifiedDualizable`: the full-subcategory predicate in Definition 3.3.
* `IsHomComparison`: the canonical Hom bijections and raw fully faithful functor.
* `condensed_localization_hom`: Hom localization, tensor coherence and restriction.

The auxiliary definitions spell out the subcategory and the canonical scalar actions and
comparisons in this statement. The coefficient localization is sheafified sectionwise
localization, with its actual ring multiplication. All categories use ordinary unbounded
complexes and the published relative derived tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedLocalization

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]

/-- The ordinary unbounded derived category with coefficients pulled back from Λ.
Source: HRS Definition 3.3 (blueprint: lem-pod-condensed-localization-hom). -/
abbrev D (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X))

/-- The actual scalar ring Γ(*,Λ).
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
abbrev R := condensedScalarRing Λ.X

/-- The scalar t as a compatible family on the profinite site, restricted from its point.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def scalarSection (t : R Λ) :
    ((condensedSectionRing Λ.X).obj ⋙ forget CommRingCat).sections :=
  ⟨fun S ↦ (condensedSectionRing Λ.X).obj.map (terminal.from S.unop).op t,
    fun f ↦ by
      change (condensedSectionRing Λ.X).obj.map f
        ((condensedSectionRing Λ.X).obj.map (terminal.from _).op t) = _
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      congr 2
      exact congrArg (condensedSectionRing Λ.X).obj.map
        (congrArg Quiver.Hom.op (terminal.comp_from f.unop))⟩

/-- Sheafified localization, with multiplication of actual ring fractions.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def localizedRing (t : R Λ) : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (condensedSectionRing Λ.X) (scalarSection Λ t)

/-- The canonical coefficient homomorphism, before forgetting commutativity.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def localizedRingMap (t : R Λ) : condensedSectionRing Λ.X ⟶ localizedRing Λ t :=
  ringedLocalizationRingUnitOfUniverses (condensedSectionRing Λ.X) (scalarSection Λ t)

/-- The same localization as an internal condensed ring, using the existing ring-sheaf functor.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def localized (t : R Λ) : Profinite.CondensedRing.{u} :=
  Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (localizedRing Λ t)))

/-- The localization is commutative with the pointwise multiplication just specified.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
instance localizedComm (t : R Λ) : IsCommMonObj (localized Λ t).X :=
  Sheaf.isCommMonObj_sheafCompose_obj _
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (localizedRing Λ t))
    (fun S a b ↦ @mul_comm ((localizedRing Λ t).obj.obj S) inferInstance a b)

/-- The actual localization map on the underlying abelian sheaves.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def coefficientLocalizationMap (t : R Λ) : Λ.X ⟶ (localized Λ t).X :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (localizedRingMap Λ t))

/-- Localization preserves the unit and multiplication of the original internal ring.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom).
Proof: reconstructing sections retains the original internal multiplication. The
sectionwise localization homomorphisms preserve one and multiplication. The monoidal
sheafification adjunction carries these identities back to the original ring object. -/
theorem coefficientLocalizationMap_isMonHom (t : R Λ) :
    IsMonHom (coefficientLocalizationMap Λ t) := by
  sorry

/-- The actual coefficient map is a ring morphism.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
instance coefficientLocalizationMapMon (t : R Λ) :
    IsMonHom (coefficientLocalizationMap Λ t) := coefficientLocalizationMap_isMonHom Λ t

/-- The map on scalar rings is uniquely determined by its value at the point.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom).
Proof: evaluate the monoid homomorphism at the point. The pointwise section-ring
construction preserves its one and multiplication identities; additivity is inherited
from the abelian sheaf map. Extensionality of ring homomorphisms gives uniqueness. -/
theorem scalarRingMap_existsUnique (t : R Λ) :
    ∃! j : R Λ →+* R (localized Λ t),
      ∀ r, j r = (coefficientLocalizationMap Λ t).hom.app (op (⊤_ Profinite.{u})) r := by
  sorry

/-- The canonical scalar homomorphism, selected by its pointwise characterization.
Source: HRS Section 5.3 (blueprint: lem-pod-condensed-localization-hom). -/
def scalarRingMap (t : R Λ) : R Λ →+* R (localized Λ t) :=
  Classical.choose (scalarRingMap_existsUnique Λ t).exists

/-- Finite constructible stratification with a dual pair on every immersed stratum.
`HasRightDual` contains evaluation D tensor M → B, coevaluation B → M tensor D,
and both contraction identities, with the actual associators and unitors.
Source: HRS Definition 3.3 (blueprint: lem-pod-condensed-localization-hom). -/
def stratifiedDualizable (X : Scheme.{u}) : ObjectProperty (D Λ X) := fun M ↦
  ∃ s : Scheme.FiniteLocallyClosedStratification X,
    (∀ i, Topology.IsConstructible (s.stratum i)) ∧
      ∀ i, Nonempty (HasRightDual
        ((CondensedRing.upperStar Λ.X (s.immersion i)).mapDerivedCategory.obj M))

/-- Scalar extension along the specified condensed-ring morphism, derived using K-flat complexes.
Source: HRS Proposition 5.5 (blueprint: lem-pod-condensed-localization-hom). -/
abbrev extension {Λ' : Profinite.CondensedRing.{u}} [IsCommMonObj Λ'.X]
    (a : Λ.X ⟶ Λ'.X) [IsMonHom a] (X : Scheme.{u}) : D Λ X ⥤ D Λ' X :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor

/-- Shift comparison transported from exact termwise scalar extension.
Source: HRS Proposition 5.5 (blueprint: lem-pod-condensed-localization-hom). -/
def extensionShiftIso {Λ' : Profinite.CondensedRing.{u}} [IsCommMonObj Λ'.X]
    (a : Λ.X ⟶ Λ'.X) [IsMonHom a] (X : Scheme.{u})
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    (N : D Λ X) (r : ℤ) :
    (extension Λ a X).obj (N⟦r⟧) ≅ ((extension Λ a X).obj N)⟦r⟧ :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    ((Mod.extendScalars (coefficientMap a X)).mapDerivedCategory.commShiftIso r).app N ≪≫
    (shiftFunctor (D Λ' X) r).mapIso
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorIsoMapDerivedCategory.app N).symm

/-- Normalization to the existing canonical pulled-back central coefficient action.
Source: HRS Lemma 5.3 and Proposition 5.5
(blueprint: lem-pod-condensed-localization-hom). -/
def IsScalarAction {A : Type (u + 1)} [CommRing A] (X : Scheme.{u})
    (j : A →+* R Λ) [Linear A (D Λ X)] : Prop :=
  ∀ (M N : D Λ X) (f : M ⟶ N) (r : A),
    r • f = (stratifiedHomScalarMap Λ X (j r)).app M ≫ f

/-- Representative square defining the canonical derived balanced tensor comparison.
The lower comparison is the actual total-complex map induced by the ordinary tensorator.
Source: HRS Proposition 5.5, Stacks 0FPT
(blueprint: lem-pod-condensed-localization-hom). -/
def IsDerivedComparisonNormalized
    {C₀ C₁ : Type (u + 2)} [Category.{u + 1} C₀] [Category.{u + 1} C₁]
    [Abelian C₀] [Abelian C₁]
    [IsGrothendieckAbelian.{u + 1} C₀] [IsGrothendieckAbelian.{u + 1} C₁]
    [MonoidalCategory C₀] [MonoidalCategory C₁]
    [MonoidalPreadditive C₀] [MonoidalPreadditive C₁]
    [MonoidalClosed C₀] [MonoidalClosed C₁]
    [BraidedCategory C₀] [BraidedCategory C₁]
    [Abelian.HasFunctorialFlatResolution C₀] [Abelian.HasFunctorialFlatResolution C₁]
    (F : C₀ ⥤ C₁) [F.Additive] [F.IsLeftAdjoint] [F.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Monoidal] [F.leftDerivedFunctor.Monoidal] : Prop :=
  ∀ P Q : HomotopyCategory C₀ (ComplexShape.up ℤ),
    Functor.OplaxMonoidal.δ F.leftDerivedFunctor
        (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q) ≫
      ((Functor.derivedTensorLeftDerivedCounit F).app P).app Q =
    ((Functor.leftDerivedDerivedTensorCounit F).app P).app Q ≫
      DerivedCategory.Qh.map
        (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans
          (ComplexShape.up ℤ) F).app P).app Q)

/-- Canonical balanced comparison and unit, including their representative normalization.
Source: HRS Proposition 5.5, Stacks 07A4
(blueprint: lem-pod-condensed-localization-hom). -/
def IsExtensionMonoidalNormalized {Λ' : Profinite.CondensedRing.{u}} [IsCommMonObj Λ'.X]
    (a : Λ.X ⟶ Λ'.X) [IsMonHom a] (X : Scheme.{u})
    [(Mod.extendScalars (coefficientMap a X)).Monoidal]
    [(Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.Monoidal]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] : Prop :=
  (∀ M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X),
    Mod.tensorObjπ M N ≫ (Mod.extendUnit (coefficientMap a X) (M ⊗ N)).hom ≫
        (Functor.OplaxMonoidal.δ (Mod.extendScalars (coefficientMap a X)) M N).hom =
      ((Mod.extendUnit (coefficientMap a X) M).hom ⊗ₘ
        (Mod.extendUnit (coefficientMap a X) N).hom) ≫
          Mod.tensorObjπ ((Mod.extendScalars (coefficientMap a X)).obj M)
            ((Mod.extendScalars (coefficientMap a X)).obj N)) ∧
  (Mod.extendπ (coefficientMap a X) (Mod.regular (condensedRingObj Λ.X X)) ≫
      (Functor.OplaxMonoidal.η (Mod.extendScalars (coefficientMap a X))).hom =
    condensedRingObj Λ'.X X ◁ coefficientMap a X ≫ μ[(condensedRingObj Λ'.X X)]) ∧
  IsDerivedComparisonNormalized (Mod.extendScalars (coefficientMap a X))

/-- The asserted Hom bijections and the raw scalar-localized fully faithful functor.
The pure-tensor equation fixes every map, and therefore implies all naturality,
identity and composition formulas, including the displayed fraction formula.
Source: HRS Proposition 5.5 (blueprint: lem-pod-condensed-localization-hom). -/
def IsHomComparison (t : R Λ) (Y : Scheme.{u})
    [Linear (R Λ) (D Λ Y)] [Linear (Localization.Away t) (D (localized Λ t) Y)]
    [PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (coefficientLocalizationMap Λ t) Y))] : Prop :=
  (∀ (M N : D Λ Y), stratifiedDualizable Λ Y M → stratifiedDualizable Λ Y N →
    ∀ r : ℤ, ∃ e : ((M ⟶ N⟦r⟧) ⊗[R Λ] Localization.Away t) ≃+
      ((extension Λ (coefficientLocalizationMap Λ t) Y).obj M ⟶
        ((extension Λ (coefficientLocalizationMap Λ t) Y).obj N)⟦r⟧),
      ∀ (f : M ⟶ N⟦r⟧) (a : Localization.Away t),
        e (f ⊗ₜ[R Λ] a) = a •
          ((extension Λ (coefficientLocalizationMap Λ t) Y).map f ≫
            (extensionShiftIso Λ (coefficientLocalizationMap Λ t) Y N r).hom)) ∧
  (∃ F : ScalarLocalization (R Λ) (stratifiedDualizable Λ Y).FullSubcategory t ⥤
      D (localized Λ t) Y,
    F.Full ∧ F.Faithful ∧ F.Additive ∧
    (∀ M, F.obj M = (extension Λ (coefficientLocalizationMap Λ t) Y).obj M.obj.obj) ∧
    (∀ (M N : (stratifiedDualizable Λ Y).FullSubcategory)
      (f : M ⟶ N) (a : Localization.Away t),
      HEq (F.map (a ⊗ₜ[R Λ] f : ScalarLocalization.mk (R := R Λ) (p := t) M ⟶
        ScalarLocalization.mk (R := R Λ) (p := t) N))
        (a • (extension Λ (coefficientLocalizationMap Λ t) Y).map f.hom)))

/-- Scalar localization of Hom for arbitrary stratified dualizable condensed coefficients.
All choices of linear structures below are fixed to the central scalar action by
`IsScalarAction`. The scalar-ring map extends the actual localization map at the point.
The functor on raw localized objects is fully faithful; no objects or retracts are added.
The derived tensorator is normalized by its ordinary balanced-tensor representative square.
The derived tensorator is braided for the published Koszul braiding.
The restriction isomorphism is the existing canonical coefficient-change comparison
`CondensedRing.derivedPullIso`, monoidal for the canonical strong monoidal structures
`CondensedRing.monoidal_leftDerivedUpperStar` of both derived inverse images.

Source: HRS Definition 3.3, Lemma 5.3 and Proposition 5.5
(blueprint: lem-pod-condensed-localization-hom).

Proof:
1. The ordinary sheaf localization is the scalar telescope with stage-n leg t^(-n)
   times its unit. This is def-weil-pbc-ringed-site-section-localization,
   lem-sfb-derived-scalar-localization-reflection and
   lem-weil-pbc-scalar-localization-complex-colimit; the unit is x ↦ 1 tensor x.
2. By lem-pod-stratified-dualizable-bounded, N has a bounded-below representative.
   Apply lem-pod-stratified-dualizable-hom-continuity to its scalar telescope, with
   source M. The common lower bound is preserved by the transition maps and shifts.
3. lem-sc-module-localization-filtered-colimit identifies the Hom telescope with
   localized Hom. The balanced maps f tensor a/t^n ↦ af/t^n and the inverse
   f/t^n ↦ f tensor t^(-n) identify it with the stated tensor product.
4. The normalized adjunction of lem-pur-sheaf-ring-derived-coefficient-adjunction
   sends the unit followed by f to E(f). Thus the resulting map sends f/t^n to
   t^(-n)E(f), with its canonical shift comparison.
5. Naturality and composition follow on fractions from functoriality of E and
   bilinearity: denominators multiply, and id/1 maps to id. These are exactly
   def-weil-linear-scalar-localization, hence give the raw fully faithful functor.
6. Common finite constructible refinements and dual pairs show tensor closure.
   lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback supply the canonical tensor map.
7. The map (a tensor x) tensor (b tensor y) ↦ ab tensor (x tensor y) and its
   inverse establish the balanced tensor normalization. The unit is multiplication.
   lem-sf-ringed-tensor-complex-constraints proves associativity, unit and symmetry
   coherence, with the Koszul sign on homogeneous generators.
8. For g:Z→Y use def-weil-proetale-inverse-image and
   sk-def-sfb-pullback-from-point-comp. Inverse image preserves the scalar telescope.
   On pulled-back tensors both coefficient-change routes are the identity. They
   preserve the unit, fractions and tensor comparisons. Constructible strata pull
   back by lem-pur-scheme-constructible-preimage, and their dual pairs pull back
   by the same monoidal comparisons. This proves all restriction assertions.
The empty scheme, zero ring, t=0 and nilpotent t are included throughout. -/
theorem condensed_localization_hom (t : R Λ) :
    ∃ (k : Localization.Away t →+* R (localized Λ t))
      (exactness : ∀ X : Scheme.{u}, PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap (coefficientLocalizationMap Λ t) X)))
      (l₀ : ∀ X : Scheme.{u}, Linear (R Λ) (D Λ X))
      (l₁ : ∀ X : Scheme.{u}, Linear (Localization.Away t) (D (localized Λ t) X)),
      k.comp (algebraMap (R Λ) (Localization.Away t)) = scalarRingMap Λ t ∧
      (fun [lin₀ : ∀ X : Scheme.{u}, Linear (R Λ) (D Λ X)]
        [lin₁ : ∀ X : Scheme.{u}, Linear (Localization.Away t) (D (localized Λ t) X)]
        [ex : ∀ X : Scheme.{u}, PreservesFiniteLimits
          (Mod.extendScalars (coefficientMap (coefficientLocalizationMap Λ t) X))] ↦
        (∀ X : Scheme.{u}, IsScalarAction Λ X (RingHom.id _) ∧
          IsScalarAction (localized Λ t) X k) ∧
        (∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y], IsHomComparison Λ t Y ∧
          stratifiedDualizable Λ Y (𝟙_ (D Λ Y)) ∧
          ∀ M N : D Λ Y, stratifiedDualizable Λ Y M → stratifiedDualizable Λ Y N →
            stratifiedDualizable Λ Y (M ⊗ N)) ∧
        (∃ (m : ∀ X : Scheme.{u},
            (Mod.extendScalars (coefficientMap (coefficientLocalizationMap Λ t) X)).Monoidal)
          (n : ∀ X : Scheme.{u}, (extension Λ (coefficientLocalizationMap Λ t) X).Monoidal),
          (fun [ordM : ∀ X : Scheme.{u},
              (Mod.extendScalars (coefficientMap (coefficientLocalizationMap Λ t) X)).Monoidal]
            [derM : ∀ X : Scheme.{u}, (extension Λ (coefficientLocalizationMap Λ t) X).Monoidal] ↦
            (∀ X : Scheme.{u}, IsExtensionMonoidalNormalized Λ (coefficientLocalizationMap Λ t) X ∧
              ∀ M N : D Λ X,
                Functor.LaxMonoidal.μ (extension Λ (coefficientLocalizationMap Λ t) X) M N ≫
                    (extension Λ (coefficientLocalizationMap Λ t) X).map (β_ M N).hom =
                  (β_ ((extension Λ (coefficientLocalizationMap Λ t) X).obj M)
                    ((extension Λ (coefficientLocalizationMap Λ t) X).obj N)).hom ≫
                    Functor.LaxMonoidal.μ (extension Λ (coefficientLocalizationMap Λ t) X) N M) ∧
            (∀ (Z Y : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
              [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Z ⟶ Y),
              NatTrans.IsMonoidal
                (CondensedRing.derivedPullIso (coefficientLocalizationMap Λ t) g).hom))
            (ordM := m) (derM := n)) ∧
        (∀ (Z Y : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]
          [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Z ⟶ Y) (M : D Λ Y),
          stratifiedDualizable Λ Y M → stratifiedDualizable Λ Z
            ((CondensedRing.upperStar Λ.X g).mapDerivedCategory.obj M)))
        (lin₀ := l₀) (lin₁ := l₁) (ex := exactness) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedLocalization

