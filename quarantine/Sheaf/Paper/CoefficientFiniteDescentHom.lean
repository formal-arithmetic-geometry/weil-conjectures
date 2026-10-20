/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Paper.CondensedCoefficientComparisons
public import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit
import all Sheaf.Paper.CondensedFiniteModelProofAPI
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful
public import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Finite descent of derived coefficient morphisms

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md and its proof
(blueprint: det-lem-coefficient-finite-descent-hom).

All coefficient maps, adjunctions, and tensor comparisons below are the recorded
constructions. The Hom-colimit assertion is expressed by surjectivity on finite
representatives and equality after passing to a common finite field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vA uA vB uB vC uC vZ uZ

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- Transport a shifted morphism by scalar extension and the given canonical tensor
comparison. Source: blueprint coefficient-finite-descent-hom, proof paragraph (1),
tensor transitivity (blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentDerivedHomMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} (S : B ⥤ V) [S.CommShift ℤ] {W : A ⥤ V}
    (α : T ⋙ S ≅ W) (C D : A) (r : ℤ)
    (f : T.obj C ⟶ (T.obj D)⟦r⟧) : W.obj C ⟶ (W.obj D)⟦r⟧ :=
  α.inv.app C ≫ S.map f ≫ (S.commShiftIso r).hom.app (T.obj D) ≫
    (α.hom.app D)⟦r⟧'

/-- The coefficient-inclusion map on restricted extensions is the adjunction mate
of tensor transitivity and the old counit. This fixes the actual transition map.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (1), unit and counit
formulas (blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentDerivedRestrictionMap
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {T : A ⥤ B} {U : B ⥤ A} (a : T ⊣ U)
    (S : B ⥤ V) [S.CommShift ℤ]
    {W : A ⥤ V} {Z : V ⥤ A} (b : W ⊣ Z) (α : T ⋙ S ≅ W)
    (D : A) (r : ℤ) : U.obj ((T.obj D)⟦r⟧) ⟶ Z.obj ((W.obj D)⟦r⟧) :=
  b.homEquiv _ _
    (α.inv.app _ ≫ S.map (a.counit.app ((T.obj D)⟦r⟧)) ≫
      (S.commShiftIso r).hom.app (T.obj D) ≫ (α.hom.app D)⟦r⟧')

private theorem descentHomMap_comp {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] [HasShift B ℤ]
    {V : Type uC} [Category.{vC} V] [HasShift V ℤ]
    {Z : Type uZ} [Category.{vZ} Z] [HasShift Z ℤ]
    {T : A ⥤ B} (U : B ⥤ V) [U.CommShift ℤ]
    (S : V ⥤ Z) [S.CommShift ℤ]
    {W : A ⥤ V} {R : B ⥤ Z} [R.CommShift ℤ] {Q : A ⥤ Z}
    (α : T ⋙ U ≅ W) (β : U ⋙ S ≅ R) [NatTrans.CommShift β.hom ℤ]
    (γ : W ⋙ S ≅ Q) (δ : T ⋙ R ≅ Q)
    (hc : ∀ M, S.map (α.hom.app M) ≫ γ.hom.app M =
      β.hom.app (T.obj M) ≫ δ.hom.app M)
    (C D : A) (r : ℤ) (f : T.obj C ⟶ (T.obj D)⟦r⟧) :
    coefficientDescentDerivedHomMap S γ C D r
      (coefficientDescentDerivedHomMap U α C D r f) =
        coefficientDescentDerivedHomMap R δ C D r f := by
  have hs (M : A) : γ.inv.app M ≫ S.map (α.inv.app M) =
      δ.inv.app M ≫ β.inv.app (T.obj M) := by
    apply (cancel_mono (S.map (α.hom.app M) ≫ γ.hom.app M)).mp
    simp only [Category.assoc, ← S.map_comp_assoc, Iso.inv_hom_id_app,
      Iso.inv_hom_id_app]
    rw [hc]
    simp
  dsimp only [coefficientDescentDerivedHomMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, hs]
  simp only [Category.assoc]
  rw [S.commShiftIso_hom_naturality_assoc]
  have hb := NatTrans.shift_app_comm β.hom r (T.obj D)
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  rw [← (shiftFunctor Z r).map_comp, hc, (shiftFunctor Z r).map_comp]
  rw [reassoc_of% hb]
  have hn := β.hom.naturality f
  change S.map (U.map f) ≫ β.hom.app _ = β.hom.app _ ≫ R.map f at hn
  rw [reassoc_of% hn]
  simp

private theorem adjunction_comparison_naturality {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] {V : Type uC} [Category.{vC} V]
    {T : A ⥤ B} {U : B ⥤ A} (a : T ⊣ U) (S : B ⥤ V)
    {W : A ⥤ V} {Z : V ⥤ A} (b : W ⊣ Z) (α : T ⋙ S ≅ W)
    (C : A) (Y : B) (Y' : V) (f : T.obj C ⟶ Y) (q : S.obj Y ⟶ Y') :
    b.homEquiv C Y' (α.inv.app C ≫ S.map f ≫ q) =
      a.homEquiv C Y f ≫ b.homEquiv (U.obj Y) Y'
        (α.inv.app (U.obj Y) ≫ S.map (a.counit.app Y) ≫ q) := by
  rw [← b.homEquiv_naturality_left]
  congr 1
  rw [α.inv.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← S.map_comp_assoc]
  have hh := (a.homEquiv C Y).symm_apply_apply f
  rw [a.homEquiv_counit] at hh
  rw [hh]

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The specified finite-field extension map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentHomTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsSubfield X ℓ (h.trans k)).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsSubfield X ℓ k)
    (condensedCoefficientCompIso X ℓ h k) C D r f

/-- The specified extension-to-algebraic-closure map on shifted derived Hom.
Source: blueprint coefficient-finite-descent-hom, clauses (1) and (3)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentHomToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ)
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C ⟶
      ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧ :=
  coefficientDescentDerivedHomMap (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (derivedExtendScalarsCompIso X ℓ h) C D r f

/-- The finite-stage transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentRestrictionTransition
    {E F G : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (k : F ≤ G)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedRestriction X ℓ (h.trans k)).obj
        (((derivedExtendScalarsSubfield X ℓ (h.trans k)).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsSubfield X ℓ k)
    (finiteCoefficientDerivedAdjunction X ℓ (h.trans k))
    (condensedCoefficientCompIso X ℓ h k) D r

/-- The algebraic-closure transition on restricted shifted derived extensions.
Source: blueprint coefficient-finite-descent-hom, clause (1), transition identity
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentRestrictionToAlgCl
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) :
    (finiteCoefficientDerivedRestriction X ℓ h).obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) ⟶
      (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
        (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D)⟦r⟧) :=
  coefficientDescentDerivedRestrictionMap (finiteCoefficientDerivedAdjunction X ℓ h)
    (derivedExtendScalarsToPadicAlgCl X ℓ F)
    (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    (derivedExtendScalarsCompIso X ℓ h) D r

/-- The poset of finite fields containing E, lifted to the coefficient universe.
Source: blueprint coefficient-finite-descent-hom, proof paragraph (2)
(blueprint: det-lem-coefficient-finite-descent-hom). -/
def coefficientDescentFields (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

private lemma constructibleToPadicAlgCl_map_hom (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K L : PadicSubfieldConstructible X ℓ E} (f : K ⟶ L) :
    ((constructibleToPadicAlgCl X ℓ E).map f).hom =
      (derivedExtendScalarsToPadicAlgCl X ℓ E).map f.hom := rfl

private lemma tensorComp_hom {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact Category.id_comp _

private lemma tensorComp_inv {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (K : PadicSubfieldConstructible X ℓ E) :
    ((constructibleToPadicAlgClCompIso X ℓ h).inv.app K).hom =
      (finiteCoefficientDerivedTensorCompIso X ℓ h).inv.app K.obj := by
  change (boundedConstructible (padicAlgClRingObj X ℓ)).ι.map _ = _
  unfold constructibleToPadicAlgClCompIso
  rw [Functor.fullyFaithfulCancelRight_inv_app, Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.refl_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.comp_id]
  rfl

private lemma tensorCompShift {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    NatTrans.CommShift (finiteCoefficientDerivedTensorCompIso X ℓ h).hom ℤ := by
  exact Functor.leftComp_shift
    (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ F))
    ((Mod.extendScalarsComp _ _).symm ≪≫
      Mod.extendScalarsIsoOfEq (padicSubfieldRingObjMap_comp_toPadicAlgCl X ℓ h))


private lemma descentHomToAlgCl_transition [TopologicalSpace.NoetherianSpace X]
    {E F G : FiniteIntermediateField ℓ} (h : E ≤ F) (j : F ≤ G)
    (C D : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      ((derivedExtendScalarsSubfield X ℓ h).obj D)⟦r⟧) :
    coefficientDescentHomToAlgCl X ℓ (h.trans j) C D r
      (coefficientDescentHomTransition X ℓ h j C D r f) =
        coefficientDescentHomToAlgCl X ℓ h C D r f := by
  let : NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ j).hom ℤ :=
    tensorCompShift X ℓ j
  exact descentHomMap_comp (derivedExtendScalarsSubfield X ℓ j)
    (derivedExtendScalarsToPadicAlgCl X ℓ G)
    (condensedCoefficientCompIso X ℓ h j) (derivedExtendScalarsCompIso X ℓ j)
    (derivedExtendScalarsCompIso X ℓ (h.trans j)) (derivedExtendScalarsCompIso X ℓ h)
    (fun M ↦ by
      have hc := congr_app (congrArg Iso.hom
        ((condensedCoefficientCoherence X ℓ).2.1 E F G h j)) M
      simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Category.id_comp] using hc) C D r f

set_option backward.isDefEq.respectTransparency true in
private lemma descentHomToAlgCl_injective
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (C D : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (r : ℤ) : Function.Injective (coefficientDescentHomToAlgCl X ℓ h C D r) := by
  let : (derivedExtendScalarsToPadicAlgCl X ℓ F).Faithful :=
    faithful_leftDerivedExtendScalarsToPadicAlgCl X ℓ F
  intro f g e
  dsimp only [coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap] at e
  apply (derivedExtendScalarsToPadicAlgCl X ℓ F).map_injective
  have e' := (cancel_epi ((derivedExtendScalarsCompIso X ℓ h).inv.app C)).mp e
  simpa only [← Category.assoc, cancel_mono] using e' 

/-- Derived coefficient Hom adjunction, its coefficient naturality, the uniformly
bounded-below coefficient tensor colimit, and bijectivity on finite representatives.
Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit,
sk-lem-coefficient-finite-descent-hom.md, clauses (1)--(3)
(blueprint: det-lem-coefficient-finite-descent-hom).

Proof, following the ten DAG steps:
1. On a small skeleton of the pro-etale site, sheaf tensor is closed and preserves
colimits (sk-def-sfb-sheaf-tensor). The extension/restriction adjunction of
sk-def-sfb-change-of-scalars has exact restriction; lem-sfb-subfield-flat and
lem-sfb-qlbar-flat make extension exact as well.
2. Lift this adjunction to complexes by lem-weil-pbc-termwise-adjunction-homotopy.
Exact functors preserve quasi-isomorphisms by
lem-weil-pbc-exact-functor-derived-factorization. Apply lem-sfb-adjunction-localization:
the Hom map is restriction followed by the unit, and its inverse is extension
followed by the counit. Restriction commutes with shifts.
3. Identify the recorded left-derived extensions with these termwise extensions
by the exact-functor clause of sk-def-sfb-derived-categories.
4. Tensor multiplication and insertion of 1 give inverse transitivity maps.
Their unit compatibility and lem-weil-pbc-conjugate-iso-unit-equation identify
them with def-sfb-derived-extend-comp-iso and the recorded finite comparison.
5. The inclusion map sends the old unit to the new one. Counit naturality gives
the two displayed Hom-naturality identities, also for the algebraic closure.
6. The finite fields containing E form a nonempty directed poset, by finite
composita (det-def-sfb-qlbar-condensed-subextensions). The ring cocone of
sk-prop-sfb-qlbar-colimit-x remains colimiting on this tail: extend a cocone on
the tail to every finite H via EH. All legs remain the actual inclusions.
7. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence and
lem-sfb-directed-ring-sheaf-module-colimit to identify this same cocone as a
colimit of E-module sheaves.
8. Tensor with each term of the representative preserves this colimit, by
lem-weil-pbc-independent-sheaf-tensor-colimits; its balancing maps are those of
def-sfb-modobj-relative-tensor. The comparisons commute with differentials.
Additivity preserves every zero term below the given lower bound.
9. The standing scheme is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
Bounded constructibility and lem-sfb-bounded-representative give a bounded
representative of D.
10. Apply sk-lem-constructible-ext-continuity with source C, the coefficient
diagram of steps 6--8, and degree r. The identities of step 5 identify its
comparison with coefficient extension on Hom. A filtered-colimit element is a
finite representative, and equality is equality at a common later stage. Thus
the last two clauses say exactly that this canonical comparison is bijective.
-/
theorem coefficient_finite_descent_hom
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i => leOfHom (ULift.down i).hom) (fun i => leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j => leOfHom (ULift.down j).hom)
            (fun j => leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F h
    exact (finiteCoefficientDerivedHomEquiv X ℓ h C.obj _).bijective
  · exact (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _).bijective
  · intro F G h j f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsSubfield X ℓ j)
      (finiteCoefficientDerivedAdjunction X ℓ (h.trans j))
      (condensedCoefficientCompIso X ℓ h j) C.obj _ _ f _
  · intro F h f
    exact adjunction_comparison_naturality
      (finiteCoefficientDerivedAdjunction X ℓ h)
      (derivedExtendScalarsToPadicAlgCl X ℓ F)
      (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
      (derivedExtendScalarsCompIso X ℓ h) C.obj _ _ f _
  · intro K e a b hK
    let : (coefficientDescentFields ℓ E).Final := by
      dsimp [coefficientDescentFields]
      infer_instance
    refine ⟨?_, ?_, ?_⟩
    · exact IsFiltered.of_equivalence (AsSmall.equiv (C := Under E))
    · exact nonempty_isColimit_coefficientComplexCocone X ℓ K
        (coefficientDescentFields ℓ E) _ _
    · intro i n hn
      exact (Mod.comap (padicSubfieldRingObjMap X ℓ
        (leOfHom (ULift.down i).hom))).map_isZero
          ((Mod.extendScalars (padicSubfieldRingObjMap X ℓ
            (leOfHom (ULift.down i).hom))).map_isZero (hK n (Or.inl hn)))
  · intro f
    have : (boundedConstructible (padicSubfieldRingObj X ℓ E)).IsTriangulated :=
      finiteBoundedTriangulated X ℓ E
    let D' : BoundedConstructible (padicSubfieldRingObj X ℓ E) :=
      ⟨D.obj⟦r⟧, (boundedConstructible (padicSubfieldRingObj X ℓ E)).le_shift r _ D.property⟩
    let f' := f ≫ ((derivedExtendScalarsToPadicAlgCl X ℓ E).commShiftIso r).inv.app D.obj
    obtain ⟨F, h, j, g, hg⟩ := constructibleCocone_homSurj X ℓ E E C D'
      (ObjectProperty.homMk f')
    let g' := g.hom ≫ ((derivedExtendScalarsSubfield X ℓ h).commShiftIso r).hom.app D.obj
    refine ⟨F, h, g', ?_⟩
    have hh := congrArg (·.hom) hg
    dsimp only [constructibleCocone] at hh
    simp only [ObjectProperty.FullSubcategory.comp_hom, tensorComp_inv, tensorComp_hom,
      constructibleToPadicAlgCl_map_hom] at hh
    have : NatTrans.CommShift (derivedExtendScalarsCompIso X ℓ h).hom ℤ :=
      tensorCompShift X ℓ h
    have hc := NatTrans.shift_app_comm (derivedExtendScalarsCompIso X ℓ h).hom r D.obj
    simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hc
    change f' = (derivedExtendScalarsCompIso X ℓ h).inv.app C.obj ≫
      (derivedExtendScalarsToPadicAlgCl X ℓ F).map g.hom ≫
        (derivedExtendScalarsCompIso X ℓ h).hom.app (D.obj⟦r⟧) at hh
    dsimp only [g', coefficientDescentHomToAlgCl, coefficientDescentDerivedHomMap]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    rw [← Category.assoc, ← Category.assoc]
    rw [← Category.assoc] at hh
    rw [← hh]
    simp only [f', Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id f
  · intro F G h j f g heq
    let H := IsFiltered.max F G
    have hF : F ≤ H := leOfHom (IsFiltered.leftToMax F G)
    have hG : G ≤ H := leOfHom (IsFiltered.rightToMax F G)
    refine ⟨H, hF, hG, ?_⟩
    apply descentHomToAlgCl_injective X ℓ (h.trans hF) C.obj D.obj r
    rw [descentHomToAlgCl_transition, descentHomToAlgCl_transition]
    exact heq

end AlgebraicGeometry.ProEtale
