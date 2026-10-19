/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Comparison with completed condensed coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-qlbar-colimit-x, the three comparisons and inverse-image compatibility
(blueprint: sk-prop-sfb-qlbar-colimit-x).

The comparisons are expressed by universal properties of the specified reduction maps
and localization cocone. Thus no choice of an unrelated isomorphism is involved.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Convert a condensed ring sheaf to its existing ring object, then pull back to `X`.
Source: blueprint comparison with completed coefficients, notation `Λ_X`
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable abbrev completedCoefficient (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :=
  coefficientRing X
    (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))

/-- Pull back an actual condensed ring homomorphism, including all its ring structure.
Source: blueprint comparison with completed coefficients, its canonical maps
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficientMap (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}} (f : R ⟶ S) :
    completedCoefficient X R ⟶ completedCoefficient X S :=
  (sfbPullbackFromPoint X).mapMon.map
    (Mon.Hom.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f))

/-- The usual constant ring sheaf, expressed in the existing ring-object encoding.
Source: blueprint comparison with completed coefficients, its finite constant coefficients
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable abbrev completedConstantRing (X : Scheme.{u}) (R : Type) [Ring R] :=
  Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1} R))))

/-- The map of constant ring sheaves induced by an actual ring homomorphism.
Source: blueprint comparison with completed coefficients, finite reduction transitions
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedConstantMap (X : Scheme.{u}) {R S : Type} [Ring R] [Ring S]
    (f : R →+* S) : completedConstantRing X R ⟶ completedConstantRing X S :=
  Mon.Hom.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).map
      (RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (f.comp ULift.ringEquiv.toRingHom)))))

/-- The finite quotient, with its quotient topology; level `n` means exponent `n+1`.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
abbrev completedResidue (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ) :=
  PadicAlgCl.integers l E ⧸ (Ideal.span {π}) ^ (n + 1)

/-- The actual reduction of continuous integer-valued functions modulo `π^(n+1)`.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedReduction (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    Profinite.padicIntegersCondensedRing.{u} l E ⟶
      Profinite.continuousMapRingSheaf (completedResidue l E π n) :=
  Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk _) continuous_quot_mk

/-- Transition between consecutive quotient rings, applied to continuous functions.
Source: blueprint comparison with completed coefficients, first comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedResidueTransition (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ) :
    Profinite.continuousMapRingSheaf.{u} (completedResidue l E π (n + 1)) ⟶
      Profinite.continuousMapRingSheaf (completedResidue l E π n) :=
  Profinite.continuousMapRingSheafMap
    (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)))
    ((QuotientRing.isOpenQuotientMap_mk ((Ideal.span {π}) ^ (n + 2))).isQuotientMap
      |>.continuous_iff.mpr continuous_quot_mk)

/-- The regular integral module maps to the rational ring, restricted along its inclusion.
Source: blueprint comparison with completed coefficients, localization comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedRationalModule (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  (Mod.comap (completedCoefficientMap X
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)).hom).obj
    (Mod.regular (completedCoefficient X (Profinite.padicSubfieldCondensedRing l E)).X)

/-- The existing finite-field diagram, bundled with its ring homomorphisms.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldDiagram (l : ℕ) [Fact l.Prime] :
    PadicAlgCl.FiniteIntermediateField l ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.Hom.mk (Profinite.padicSubfieldRingObjMap l (leOfHom f))
  map_id E := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_id l E)
  map_comp f g := Mon.Hom.ext (Profinite.padicSubfieldRingObjMap_comp l
    (leOfHom f) (leOfHom g))

/-- The existing canonical algebraic-closure cocone, bundled in ring objects.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPointSubfieldCocone (l : ℕ) [Fact l.Prime] :
    Cocone (completedPointSubfieldDiagram.{u} l) where
  pt := Mon.mk (Profinite.padicAlgClRingObj l)
  ι := {
    app E := Mon.Hom.mk (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
    naturality _E _F f := Mon.Hom.ext
      ((Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl l (leOfHom f)).trans
        (Category.comp_id _).symm) }

/-- The canonical ring cocone on a scheme is the image of the point cocone under p_X^*.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedSubfieldCocone (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (sfbPullbackFromPoint X).mapMon.mapCocone (completedPointSubfieldCocone l)

/-- The finite-subextension inclusions, with their canonical ring-homomorphism structures.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedSubfieldInclusion (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField l} (h : E ≤ F) :=
  completedCoefficientMap X (Profinite.padicSubfieldCondensedRingMap l h)

/-- The finite-subextension legs into the algebraic-closure ring sheaf.
Source: blueprint comparison with completed coefficients, third comparison
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedSubfieldLeg (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  completedCoefficientMap X (Profinite.padicSubfieldCondensedRingToPadicAlgCl l E)

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.MonObj CategoryTheory.MonoidalCategory in
private noncomputable def siftedRingCoconeIsColimit
    {C : Type*} [Category C] [MonoidalCategory C]
    {J : Type*} [Category J] [IsSifted J]
    {D : J ⥤ Mon C} (c : Cocone D)
    (hc : IsColimit ((Mon.forget C).mapCocone c))
    [PreservesColimit₂ (D ⋙ Mon.forget C) (D ⋙ Mon.forget C) (curriedTensor C)] :
    IsColimit c := by
  let desc (s : Cocone D) : c.pt ⟶ s.pt := by
    let d : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
    have hd (j : J) : (c.ι.app j).hom ≫ d = (s.ι.app j).hom :=
      hc.fac ((Mon.forget C).mapCocone s) j
    have : IsMonHom d := by
      constructor
      · obtain ⟨j⟩ := IsSifted.nonempty (C := J)
        rw [← IsMonHom.one_hom (c.ι.app j).hom, Category.assoc, hd j]
        exact IsMonHom.one_hom (s.ι.app j).hom
      · apply (hc.tensor hc).hom_ext
        intro j
        change ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ μ[c.pt.X] ≫ d =
          ((c.ι.app j).hom ⊗ₘ (c.ι.app j).hom) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X]
        rw [← IsMonHom.mul_hom_assoc, hd j,
          tensorHom_comp_tensorHom_assoc, hd j]
        exact IsMonHom.mul_hom (s.ι.app j).hom
    exact Mon.Hom.mk d
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    apply Mon.Hom.ext
    exact hc.fac ((Mon.forget C).mapCocone s) j
  · intro s m hm
    apply Mon.Hom.ext
    apply hc.hom_ext
    intro j
    exact (congrArg Mon.Hom.hom (hm j)).trans
      (hc.fac ((Mon.forget C).mapCocone s) j).symm

/-- Integral comparison with the inverse limit of the finite constant quotient rings.
A uniformizer is specified by generating the maximal ideal. Each pulled-back quotient
is identified as the constant sheaf with that finite quotient ring as value.
Source: blueprint comparison with completed coefficients, first display
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: Apply det-prop-sfb-qlbar-colimit-x-integral-limit. Finite constant sheaves
are represented by the disjoint unions of copies of X. The profinite test scheme
X[O_E] represents both the inverse limit of those sheaves and the pullback of the
condensed integers. The representing maps are precisely the reductions used here;
the representing addition, multiplication, zero and unit give the ring universal
property. In particular this does not use preservation of arbitrary limits by p_X^*.
-/
theorem completedCondensedIntegral (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) :
    (∃ (c : Cone (Functor.ofOpSequence
        (X := fun n ↦ completedCoefficient X
          (Profinite.continuousMapRingSheaf (completedResidue l E π n))) (fun n ↦
        completedCoefficientMap X (completedResidueTransition l E π n))))
      (e : completedCoefficient X (Profinite.padicIntegersCondensedRing l E) ≅ c.pt),
      (∀ n, e.hom ≫ c.π.app (op n) =
        completedCoefficientMap X (completedReduction l E π n)) ∧ Nonempty (IsLimit c)) ∧
    (∀ n, Finite (completedResidue l E π n)) ∧
    (∃ k : ∀ n, completedCoefficient X
        (Profinite.continuousMapRingSheaf (completedResidue l E π n)) ≅
          completedConstantRing X (completedResidue l E π n),
      ∀ n, completedCoefficientMap X (completedResidueTransition l E π n) ≫ (k n).hom =
        (k (n + 1)).hom ≫ completedConstantMap X
          (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)))) := by
  sorry

/-- Inverting `l` is the sequential colimit in integral modules, with the localization
ring structure inherited from the specified rational ring. The zero-th leg is the integral
inclusion, and the recurrence fixes the `l^(-m)` legs because `l` is invertible on the vertex.
Source: blueprint comparison with completed coefficients, second display
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: Apply det-prop-sfb-qlbar-colimit-x-invert-ell to the inclusion of condensed
integers into E and pull it back from the point. Multiplication by l is invertible
on E_X. The m-th leg is l^(-m) times the inclusion. A section of E is locally a
fraction with integral numerator and l-power denominator, so these maps give the
module-colimit universal property. Multiplication of fractions is the multiplication
of E_X; the denominator recursion and the integral inclusion determine its localization
ring structure. The argument includes the zero module and the empty scheme.
-/
theorem completedCondensedRational (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    ∃ j : ∀ X : Scheme.{u}, ℕ →
      (Mod.regular (completedCoefficient X (Profinite.padicIntegersCondensedRing l E)).X ⟶
        completedRationalModule X l E),
      (∀ X : Scheme.{u},
        IsIso (l • 𝟙 (completedCoefficient X (Profinite.padicSubfieldCondensedRing l E)).X) ∧
        (j X 0).hom = (completedCoefficientMap X
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)).hom ∧
        (∀ n, l • j X (n + 1) = j X n) ∧
        (∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (completedCoefficient X (Profinite.padicIntegersCondensedRing l E)).X)
          (b : ℕ → (Mod.regular
            (completedCoefficient X (Profinite.padicIntegersCondensedRing l E)).X ⟶ B)),
          (∀ n, l • b (n + 1) = b n) →
          ∃! a : completedRationalModule X l E ⟶ B, ∀ n, j X n ≫ a = b n)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
        ((f)^*[Ab.{u + 1}]).map (j Y n).hom ≫
            ((coefficientPullbackIso f
              (Mon.mk (Profinite.continuousMapRingObj E))).hom).hom =
          ((coefficientPullbackIso f
              (Mon.mk (Profinite.padicIntegersRingObj l E))).hom).hom ≫ (j X n).hom) := by
  sorry

/-- The canonical finite-subextension cocone is a colimit in ring objects.
Source: blueprint comparison with completed coefficients, third display
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: A section of the condensed algebraic closure belongs to some finite subfield.
A compatible family of additive maps therefore glues uniquely, independently of the
chosen field because two fields lie in a common finite compositum. Pullback from the
point preserves this colimit, being a left adjoint. The descended map preserves the
unit at the base field. For multiplication, tensor preserves colimits in each variable;
compare on E_X tensor F_X and pass to a common finite compositum H. Both restrictions
are multiplicative there. Additive uniqueness then proves uniqueness as a ring map.
These are steps 3--5 of the node's proof.
-/
theorem completedCondensedAlgebraicClosure (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Nonempty (IsColimit (completedSubfieldCocone X l)) := by
  have : IsSifted (PadicAlgCl.FiniteIntermediateField l) := IsFiltered.isSifted
  refine ⟨siftedRingCoconeIsColimit _ ?_⟩
  change IsColimit (padicAlgClRingObjCocone X l)
  exact isColimitPadicAlgClRingObjCocone X l

/-- Inverse image respects every reduction, integral inclusion and finite-field leg.
Together with the limit and colimit universal properties this states compatibility of
all three canonical comparisons with every scheme morphism, including identities.
Source: blueprint comparison with completed coefficients, inverse-image sentence
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: By adjunction and Yoneda, inverse image of a represented sheaf h_V is
h_(V times_Y X). Base change identifies Y[O_E] with X[O_E], and the reduction projections
with those over X. This proves the integral comparison, using representability rather
than arbitrary-limit preservation. The monoidal comparison f^*p_Y^* = p_X^* respects
the integral inclusion, multiplication by l and every finite-field inclusion. Since
inverse image preserves colimits, uniqueness on all legs gives compatibility for the
other two comparisons. This is steps 6--8 of the node's proof.
-/
theorem completedCondensedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) :
    (∀ n, ((f)^*[Ab.{u + 1}]).map
          (completedCoefficientMap Y (completedReduction l E π n)).hom ≫
        ((coefficientPullbackIso f
          (Mon.mk (Profinite.continuousMapRingObj (completedResidue l E π n)))).hom).hom =
      ((coefficientPullbackIso f
        (Mon.mk (Profinite.padicIntegersRingObj l E))).hom).hom ≫
          (completedCoefficientMap X (completedReduction l E π n)).hom) ∧
    (((f)^*[Ab.{u + 1}]).map
          (completedCoefficientMap Y
            (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)).hom ≫
        ((coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj E))).hom).hom =
      ((coefficientPullbackIso f
        (Mon.mk (Profinite.padicIntegersRingObj l E))).hom).hom ≫
          (completedCoefficientMap X
            (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)).hom) ∧
    (((f)^*[Ab.{u + 1}]).map (completedSubfieldLeg Y l E).hom ≫
        ((coefficientPullbackIso f (Mon.mk (Profinite.padicAlgClRingObj l))).hom).hom =
      ((coefficientPullbackIso f (Mon.mk (Profinite.continuousMapRingObj E))).hom).hom ≫
        (completedSubfieldLeg X l E).hom) ∧
    (∃ (c : Cone (Functor.ofOpSequence
        (X := fun n ↦ completedCoefficient Y
          (Profinite.continuousMapRingSheaf (completedResidue l E π n))) (fun n ↦
        completedCoefficientMap Y (completedResidueTransition l E π n))))
      (e : completedCoefficient Y (Profinite.padicIntegersCondensedRing l E) ≅ c.pt),
      (∀ n, e.hom ≫ c.π.app (op n) =
        completedCoefficientMap Y (completedReduction l E π n)) ∧
      Nonempty (IsLimit c) ∧ Nonempty (IsLimit (((f)^*[Ab.{u + 1}]).mapMon.mapCone c))) ∧
    Nonempty (IsColimit (((f)^*[Ab.{u + 1}]).mapMon.mapCocone
      (completedSubfieldCocone Y l))) := by
  sorry

/-- The usual continuous reduction of p-adic integers to Z/l^(n+1).
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPadicReduction (l : ℕ) [Fact l.Prime] (n : ℕ) :=
  Profinite.continuousMapRingSheafMap.{u} (PadicInt.toZModPow (p := l) (n + 1))
    (PadicInt.continuous_toZModPow (n + 1))

/-- The usual reduction between consecutive finite residue rings.
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPadicTransition (l : ℕ) [Fact l.Prime] (n : ℕ) :=
  Profinite.continuousMapRingSheafMap.{u}
    (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1))))
    continuous_of_discreteTopology

/-- The specified p-adic rational ring as a module over the p-adic integral ring.
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedPadicRationalModule (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  (Mod.comap (completedCoefficientMap X
    (Profinite.padicIntCondensedRingToPadicCondensedRing l)).hom).obj
    (Mod.regular (completedCoefficient X (Profinite.padicCondensedRing l)).X)

/-- The base-field integral formula, explicitly with the constant rings Z/l^n.
The specified cone remains a limit after every scheme inverse image.
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: Take E = Q_l in the integral comparison. Its ring of integers is Z_l,
l generates its maximal ideal, and PadicInt.toZModPow identifies its quotient by
l^n with Z/l^n. The identifications commute with reduction because they send every
integer class to itself. Thus they identify the reduction cones, their ring
structures and their inverse images. This is step 9 of the node's proof.
-/
theorem completedCondensedPadicIntegral (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    (∃ (c : Cone (Functor.ofOpSequence
        (X := fun n ↦ completedCoefficient X
          (Profinite.continuousMapRingSheaf (ZMod (l ^ (n + 1)))))
        (fun n ↦ completedCoefficientMap X (completedPadicTransition l n))))
      (e : completedCoefficient X (Profinite.padicIntCondensedRing l) ≅ c.pt),
      (∀ n, e.hom ≫ c.π.app (op n) =
        completedCoefficientMap X (completedPadicReduction l n)) ∧
      Nonempty (IsLimit c) ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ X),
        Nonempty (IsLimit (((f)^*[Ab.{u + 1}]).mapMon.mapCone c)))) ∧
    (∃ k : ∀ n, completedCoefficient X
        (Profinite.continuousMapRingSheaf (ZMod (l ^ (n + 1)))) ≅
          completedConstantRing X (ZMod (l ^ (n + 1))),
      ∀ n, completedCoefficientMap X (completedPadicTransition l n) ≫ (k n).hom =
        (k (n + 1)).hom ≫ completedConstantMap X
          (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1))))) ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ X) (n : ℕ),
      ((f)^*[Ab.{u + 1}]).map
          (completedCoefficientMap X (completedPadicReduction l n)).hom ≫
        ((coefficientPullbackIso f
          (Mon.mk (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))))).hom).hom =
      ((coefficientPullbackIso f
        (Mon.mk (Profinite.continuousMapRingObj ℤ_[l]))).hom).hom ≫
          (completedCoefficientMap Y (completedPadicReduction l n)).hom) := by
  sorry

/-- The base-field rationalization formula Q_l,X = Z_l,X[1/l], including its
canonical module-colimit legs and their inverse-image compatibility.
Source: blueprint comparison with completed coefficients, final paragraph
(blueprint: sk-prop-sfb-qlbar-colimit-x).

Proof: Specialize the rational comparison to E = Q_l and use the canonical
identification of its integers with Z_l. The inclusion is the usual Z_l to Q_l
map. Multiplication by l is invertible on Q_l,X, so the zero-th leg and recurrence
uniquely specify all l^(-n) legs. They are the module-colimit maps and commute
with every inverse image, by the already established coefficient comparisons.
This is the rational part of step 9 of the node's proof.
-/
theorem completedCondensedPadicRational (l : ℕ) [Fact l.Prime] :
    ∃ j : ∀ X : Scheme.{u}, ℕ →
      (Mod.regular (completedCoefficient X (Profinite.padicIntCondensedRing l)).X ⟶
        completedPadicRationalModule X l),
      (∀ X : Scheme.{u},
        IsIso (l • 𝟙 (completedCoefficient X (Profinite.padicCondensedRing l)).X) ∧
        (j X 0).hom = (completedCoefficientMap X
          (Profinite.padicIntCondensedRingToPadicCondensedRing l)).hom ∧
        (∀ n, l • j X (n + 1) = j X n) ∧
        (∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (completedCoefficient X (Profinite.padicIntCondensedRing l)).X)
          (b : ℕ → (Mod.regular
            (completedCoefficient X (Profinite.padicIntCondensedRing l)).X ⟶ B)),
          (∀ n, l • b (n + 1) = b n) →
          ∃! a : completedPadicRationalModule X l ⟶ B, ∀ n, j X n ≫ a = b n)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
        ((f)^*[Ab.{u + 1}]).map (j Y n).hom ≫
            ((coefficientPullbackIso f
              (Mon.mk (Profinite.continuousMapRingObj ℚ_[l]))).hom).hom =
          ((coefficientPullbackIso f
              (Mon.mk (Profinite.continuousMapRingObj ℤ_[l]))).hom).hom ≫ (j X n).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
