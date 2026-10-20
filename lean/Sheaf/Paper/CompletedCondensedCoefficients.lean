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
import all Sheaf.Paper.ContinuousIntegralScalarExact
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import Sheaf.Paper.ContinuousIntegralCoefficients

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
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem completedRingComparisonNaturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (A B : Mon C) (a : A.X ⟶ B.X) :
    G.map (F.map a) ≫
        (((Functor.mapMonCompIso (F := F) (G := G)).symm.app B ≪≫
          (Functor.mapMonNatIso e).app B).hom).hom =
      (((Functor.mapMonCompIso (F := F) (G := G)).symm.app A ≪≫
        (Functor.mapMonNatIso e).app A).hom).hom ≫ H.map a := by
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Mon.comp_hom',
    Functor.mapMonCompIso_inv_app_hom, Functor.mapMonNatIso_hom_app_hom]
  change G.map (F.map a) ≫ (𝟙 _ ≫ e.hom.app B.X) =
    (𝟙 _ ≫ e.hom.app A.X) ≫ H.map a
  simp only [Category.id_comp]
  exact e.hom.naturality a

private theorem completedLimitTransport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E) (e : F ⋙ H ≅ G)
    {A : C} (T : ℕ → C) (t : ∀ n, T (n + 1) ⟶ T n) (r : ∀ n, A ⟶ T n)
    (cY : Cone (Functor.ofOpSequence (X := fun n ↦ F.obj (T n)) (fun n ↦ F.map (t n))))
    (cX : Cone (Functor.ofOpSequence (X := fun n ↦ G.obj (T n)) (fun n ↦ G.map (t n))))
    (aY : F.obj A ≅ cY.pt) (aX : G.obj A ≅ cX.pt)
    (hY : ∀ n, aY.hom ≫ cY.π.app (op n) = F.map (r n))
    (hX : ∀ n, aX.hom ≫ cX.π.app (op n) = G.map (r n))
    (hcX : IsLimit cX) : Nonempty (IsLimit (H.mapCone cY)) := by
  let β : Functor.ofOpSequence (X := fun n ↦ F.obj (T n)) (fun n ↦ F.map (t n)) ⋙ H ⟶
      Functor.ofOpSequence (X := fun n ↦ G.obj (T n)) (fun n ↦ G.map (t n)) :=
    NatTrans.ofOpSequence (fun n ↦ e.hom.app (T n)) (fun n ↦ by
      simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
      exact e.hom.naturality (t n))
  have hβ (n : ℕᵒᵖ) : IsIso (β.app n) := by
    change IsIso (e.hom.app (T n.unop))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let v : H.obj cY.pt ≅ cX.pt := H.mapIso aY.symm ≪≫ e.app A ≪≫ aX
  have hw (n : ℕᵒᵖ) :
      (H.mapCone cY).π.app n ≫ β.app n = v.hom ≫ cX.π.app n := by
    apply (cancel_epi (H.map aY.hom)).1
    change H.map aY.hom ≫ (H.map (cY.π.app n) ≫ e.hom.app (T n.unop)) =
      H.map aY.hom ≫ v.hom ≫ cX.π.app n
    rw [← H.map_comp_assoc, hY n.unop]
    dsimp only [v, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [← H.map_comp_assoc, aY.hom_inv_id, H.map_id,
      Category.id_comp, hX n.unop]
    exact e.hom.naturality (r n.unop)
  exact ⟨(IsLimit.equivOfNatIsoOfIso (asIso β) (H.mapCone cY) cX
    (Cone.ext v hw)).symm hcX⟩

/-- Convert a condensed ring sheaf to its existing ring object, then pull back to `X`.
Source: blueprint comparison with completed coefficients, notation `Λ_X`
(blueprint: sk-prop-sfb-qlbar-colimit-x). -/
noncomputable def completedCoefficient (X : Scheme.{u})
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

open CategoryTheory.MonObj CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
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

private theorem completedSequenceUniversal
    {C : Type*} [Category C] [Preadditive C] (l : ℕ) {A B : C}
    (c : Cocone (Functor.ofSequence (fun _ ↦ l • 𝟙 A)))
    (hc : IsColimit c) (e : c.pt ≅ B) :
    ∃ j : ℕ → (A ⟶ B), j 0 = c.ι.app 0 ≫ e.hom ∧
      (∀ n, l • j (n + 1) = j n) ∧
      (∀ (D : C) (b : ℕ → (A ⟶ D)), (∀ n, l • b (n + 1) = b n) →
        ∃! a : B ⟶ D, ∀ n, j n ≫ a = b n) := by
  let d := c.extend e.hom
  have hd : IsColimit d := hc.ofIsoColimit (Cocone.ext e)
  refine ⟨fun n ↦ d.ι.app n, rfl, ?_, ?_⟩
  · intro n
    have h := d.w (homOfLE (Nat.le_succ n))
    rw [Functor.ofSequence_map_homOfLE_succ] at h
    change (l • 𝟙 A) ≫ (d.ι.app (n + 1) : A ⟶ B) = d.ι.app n at h
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  · intro D b hb
    let β : Functor.ofSequence (fun _ ↦ l • 𝟙 A) ⟶ (Functor.const ℕ).obj D :=
      NatTrans.ofSequence b (fun n ↦ by
        simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        change (l • 𝟙 A) ≫ b (n + 1) = b n ≫ 𝟙 D
        simpa only [Preadditive.nsmul_comp, Category.id_comp, Category.comp_id] using hb n)
    let s : Cocone (Functor.ofSequence (fun _ ↦ l • 𝟙 A)) := ⟨D, β⟩
    exact ⟨hd.desc s, hd.fac s, fun a ha ↦ hd.uniq s a ha⟩

private theorem completedSequenceNaturality
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (l : ℕ) (F : C ⥤ D) [F.Additive] {A B : C} {A' B' : D}
    [IsIso (l • 𝟙 B')] (a : F.obj A ⟶ A') (b : F.obj B ⟶ B')
    (j : ℕ → (A ⟶ B)) (k : ℕ → (A' ⟶ B'))
    (hj : ∀ n, l • j (n + 1) = j n) (hk : ∀ n, l • k (n + 1) = k n)
    (hzero : F.map (j 0) ≫ b = a ≫ k 0) :
    ∀ n, F.map (j n) ≫ b = a ≫ k n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    apply (cancel_mono (l • 𝟙 B')).1
    simp only [Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, ← CategoryTheory.Functor.map_nsmul, hj]
    rw [Preadditive.nsmul_comp, ← Preadditive.comp_nsmul, hk]
    exact ih

namespace CondensedRing
attribute [local irreducible] localizationCoconeIsColimit
attribute [local irreducible] pointUpperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

private theorem completedTransportRegularTelescope
    (ℓ : ℕ) {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {M : A}
    (c : Cocone (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 M)))
    (hc : IsColimit (F.mapCocone c)) {N P : B}
    (er : F.obj M ≅ N) (es : F.obj c.pt ≅ P)
    (V : B ⥤ C) (φ : V.obj N ⟶ V.obj P)
    (hz : V.map (F.map (c.ι.app 0) ≫ es.hom) = V.map er.hom ≫ φ) :
    ∃ c' : Cocone (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 N)),
      Nonempty (IsColimit c') ∧ ∃ e : c'.pt ≅ P,
        V.map (c'.ι.app 0 ≫ e.hom) = φ := by
  let α : Functor.ofSequence (fun _ ↦ ℓ • 𝟙 M) ⋙ F ⟶ Functor.ofSequence (fun _ ↦ ℓ • 𝟙 N) :=
    NatTrans.ofSequence (fun _ ↦ er.hom) (by
      intro n
      simp only [Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ]
      change F.map (ℓ • 𝟙 M) ≫ er.hom = er.hom ≫ (ℓ • 𝟙 N)
      rw [F.map_nsmul, F.map_id]
      simp)
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso er.hom
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c' := (Cocone.precompose (asIso α).inv).obj (F.mapCocone c)
  refine ⟨c', ⟨(IsColimit.precomposeHomEquiv (asIso α).symm _).symm hc⟩, es, ?_⟩
  have hi : (asIso α).inv.app 0 = er.inv := by
    apply (cancel_mono er.hom).1
    change (asIso α).inv.app 0 ≫ (asIso α).hom.app 0 = er.inv ≫ er.hom
    simp; rfl
  change V.map (((asIso α).inv.app 0 ≫ F.map (c.ι.app 0)) ≫ es.hom) = φ
  rw [hi, Category.assoc, V.map_comp, hz, ← Category.assoc,
    ← V.map_comp, er.inv_hom_id]
  change V.map (𝟙 N) ≫ φ = φ
  rw [V.map_id, Category.id_comp]

private noncomputable def completedMappedRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (R : C) [MonObj R]
    (A : D) [MonObj A] (a : L.obj R ≅ A) [IsMonHom a.hom] :
    (L.mapMod R ⋙ Mod.comap a.inv).obj (Mod.regular R) ≅ Mod.regular A :=
  (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
    restrictedRegularIso a.inv (𝟙 A) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId A).app _

private noncomputable def completedMappedRestrictedIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] {R S : C} [MonObj R] [MonObj S]
    (φ : R ⟶ S) [IsMonHom φ] {A B : D} [MonObj A] [MonObj B]
    (a : L.obj R ≅ A) (b : L.obj S ≅ B) [IsMonHom a.hom] [IsMonHom b.hom]
    (ψ : A ⟶ B) [IsMonHom ψ] (h : L.map φ ≫ b.hom = a.hom ≫ ψ) :
    (L.mapMod R ⋙ Mod.comap a.inv).obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
  (Mod.comap a.inv).mapIso
    ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
      (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
    (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
    restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
      rw [Category.assoc, h, Iso.inv_hom_id_assoc])

private theorem completedSchemeCoefficientIsoIsMonHom (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    IsMonHom (schemeCoefficientIso X R).hom := by
  rw [Functor.monObjObj_comp]
  exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
    (pointCoefficientIso R).hom

attribute [local irreducible] schemeCoefficientIso pointCoefficientIso

private theorem completedUpperStarLeftAdjoint (X : Scheme.{u}) :
    (upperStarFromPoint X).IsLeftAdjoint := by
  unfold upperStarFromPoint
  exact (pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint

private theorem completedIntegralRegularTelescope
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    ∃ c : Cocone (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
        (condensedRingObj (integralCoeff ℓ E) X)))),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (integralScalarMap ℓ E) X)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)),
        (c.ι.app 0 ≫ e.hom).hom = coefficientMap (integralScalarMap ℓ E) X := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have : (upperStarFromPoint X).IsLeftAdjoint := completedUpperStarLeftAdjoint X
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (continuousIntegers ℓ E)
  let S := coefficientPresheaf.{u} E
  let A := condensedRingObj (integralCoeff ℓ E) X
  let B := condensedRingObj (Profinite.continuousMapRingObj E) X
  let a := schemeCoefficientIso X (continuousIntegers ℓ E)
  let b := schemeCoefficientIso X E
  let φ := integralPresheafMap.{u} ℓ E
  let ψ := coefficientMap (integralScalarMap ℓ E) X
  have : IsMonHom a.hom := completedSchemeCoefficientIsoIsMonHom X (continuousIntegers ℓ E)
  have : IsMonHom a.inv := by infer_instance
  have : IsMonHom b.hom := completedSchemeCoefficientIsoIsMonHom X E
  let F := L.mapMod R ⋙ Mod.comap a.inv
  have : L.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : (L.mapMod R).Additive := ⟨fun {M N f g} ↦
    Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  have : PreservesColimitsOfShape ℕ (L.mapMod R) := by
    have : PreservesColimitsOfShape ℕ
        (L.mapMod R ⋙ Mod.forget (L.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape ℕ (Mod.forget R ⋙ L))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (L.obj R))
  let er : F.obj (Mod.regular R) ≅ Mod.regular A := completedMappedRegularIso L R A a
  let es : F.obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
    completedMappedRestrictedIso L φ a b ψ (schemeCoefficientIso_naturality ℓ E X)
  apply completedTransportRegularTelescope ℓ F (localizationCocone ℓ E)
    (isColimitOfPreserves F (localizationCoconeIsColimit.{u} ℓ E))
    er es (Mod.forget A) ψ
  change L.map (localizationLegHom ℓ E 0) ≫ b.hom = a.hom ≫ ψ
  have hz : localizationLegHom ℓ E 0 = φ := by
    ext T x
    apply ULift.ext
    ext t
    simp only [localizationLegHom, pow_zero, div_one]
    rfl
  rw [hz]
  exact schemeCoefficientIso_naturality ℓ E X

private theorem completedIntegralRegularTelescopeFor
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (O : Subring E) (hO : O = continuousIntegers ℓ E) (X : Scheme.{u}) :
    ∃ c : Cocone (Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
        (condensedRingObj (Profinite.continuousMapRingObj O) X)))),
      Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (Profinite.continuousMapRingSheafMap O.subtype continuous_subtype_val))) X)).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E) X)),
        (c.ι.app 0 ≫ e.hom).hom = coefficientMap
          (((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (Profinite.continuousMapRingSheafMap O.subtype continuous_subtype_val))) X := by
  subst O
  exact completedIntegralRegularTelescope ℓ E X

private theorem completedScalarIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) : IsIso (ℓ • 𝟙 (condensedRingObj
      (Profinite.continuousMapRingObj.{u} E) X)) := by
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hm : IsIso ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      (ℓ • 𝟙 (Profinite.continuousMapRingObj E))) := by
    change IsIso (ℓ • 𝟙 (Profinite.continuousMapRingObj.{u} E).obj)
    rw [NatTrans.isIso_iff_isIso_app]
    intro S
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : ULift.{u + 1} C(S.unop, E) ↦ ℓ • x)
    simp only [nsmul_eq_mul]
    have h : IsUnit (ℓ : ULift.{u + 1} C(S.unop, E)) := by
      simpa only [map_natCast] using
        (((isUnit_iff_ne_zero.mpr hp).map
          (ContinuousMap.C : E →+* C(S.unop, E))).map ULift.ringEquiv.symm.toRingHom)
    exact IsUnit.isUnit_iff_mulLeft_bijective.mp h
  have : IsIso (ℓ • 𝟙 (Profinite.continuousMapRingObj.{u} E)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  have : (upperStarFromPoint X).Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have hi := (upperStarFromPoint X).map_isIso
    (ℓ • 𝟙 (Profinite.continuousMapRingObj.{u} E))
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] at hi
  exact hi

end CondensedRing

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

private theorem completedRationalOfTelescope (l : ℕ)
    (R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) (φ : R ⟶ S)
    (h : ∀ X : Scheme.{u}, ∃ c : Cocone (Functor.ofSequence (fun _ ↦ l • 𝟙
        (Mod.regular (completedCoefficient X R).X))), Nonempty (IsColimit c) ∧
      ∃ e : c.pt ≅ (Mod.comap (completedCoefficientMap X φ).hom).obj
        (Mod.regular (completedCoefficient X S).X),
          (c.ι.app 0 ≫ e.hom).hom = (completedCoefficientMap X φ).hom)
    (hi : ∀ X : Scheme.{u}, IsIso (l • 𝟙 (completedCoefficient X S).X)) :
    ∃ j : ∀ X : Scheme.{u}, ℕ →
      (Mod.regular (completedCoefficient X R).X ⟶
        ((Mod.comap (completedCoefficientMap X φ).hom).obj
        (Mod.regular (completedCoefficient X S).X))),
      (∀ X : Scheme.{u},
        IsIso (l • 𝟙 (completedCoefficient X S).X) ∧
        (j X 0).hom = (completedCoefficientMap X
          φ).hom ∧
        (∀ n, l • j X (n + 1) = j X n) ∧
        (∀ (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (completedCoefficient X R).X)
          (b : ℕ → (Mod.regular
            (completedCoefficient X R).X ⟶ B)),
          (∀ n, l • b (n + 1) = b n) →
          ∃! a : ((Mod.comap (completedCoefficientMap X φ).hom).obj
        (Mod.regular (completedCoefficient X S).X)) ⟶ B, ∀ n, j X n ≫ a = b n)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
        ((f)^*[Ab.{u + 1}]).map (j Y n).hom ≫
            ((coefficientPullbackIso f
              (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S))).hom).hom =
          ((coefficientPullbackIso f
              (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
                (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))).hom).hom ≫ (j X n).hom) := by
  classical
  choose c hc e he using h
  have hs (X : Scheme.{u}) := completedSequenceUniversal l (c X) (hc X).some (e X)
  choose j hj hrec huni using hs
  refine ⟨j, ?_, ?_⟩
  · intro X
    refine ⟨hi X, ?_, hrec X, huni X⟩
    rw [hj X]
    exact he X
  · intro X Y f n
    have : IsIso (l • 𝟙
        (completedCoefficient X S).X) :=
      hi X
    have hrec' (Z : Scheme.{u}) (m : ℕ) :
        l • (j Z (m + 1)).hom = (j Z m).hom :=
      congrArg (fun g : Mod.regular
        (completedCoefficient Z R).X ⟶
          ((Mod.comap (completedCoefficientMap Z φ).hom).obj
          (Mod.regular (completedCoefficient Z S).X)) ↦ g.hom) (hrec Z m)
    have : IsIso (l • 𝟙
        (coefficientRing X (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S))).X) :=
      hi X
    refine completedSequenceNaturality l ((f)^*[Ab.{u + 1}])
      (((coefficientPullbackIso f (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))).hom).hom)
      (((coefficientPullbackIso f (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S))).hom).hom)
      (fun m ↦ (j Y m).hom) (fun m ↦ (j X m).hom) (hrec' Y) (hrec' X) ?_ n
    have hz (Z : Scheme.{u}) : (j Z 0).hom =
        (completedCoefficientMap Z
          φ).hom := by
      rw [hj Z]
      exact he Z
    rw [hz X, hz Y]
    exact completedRingComparisonNaturality (upperStarFromPoint Y)
      ((f)^*[Ab.{u + 1}]) (upperStarFromPoint X) (upperStarFromPointComp f)
      (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R))
      (Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj S))
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        φ)

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
  classical
  let := PadicAlgCl.normedFieldOfAlgebra l E.1
  let : NormedAlgebra ℚ_[l] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl l) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact completedRationalOfTelescope l
    (Profinite.padicIntegersCondensedRing l E)
    (Profinite.padicSubfieldCondensedRing l E)
    (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E)
    (fun X ↦ CondensedRing.completedIntegralRegularTelescope l E.1 X)
    (fun X ↦ CondensedRing.completedScalarIso l E.1 X)

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
  classical
  have hnat := completedRingComparisonNaturality (upperStarFromPoint Y)
    ((f)^*[Ab.{u + 1}]) (upperStarFromPoint X) (upperStarFromPointComp f)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h := hnat
      (Mon.mk (Profinite.padicIntegersRingObj l E))
      (Mon.mk (Profinite.continuousMapRingObj (completedResidue l E π n)))
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (completedReduction l E π n))
    exact h
  · have h := hnat
      (Mon.mk (Profinite.padicIntegersRingObj l E))
      (Mon.mk (Profinite.continuousMapRingObj E))
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing l E))
    exact h
  · have h := hnat
      (Mon.mk (Profinite.continuousMapRingObj E))
      (Mon.mk (Profinite.padicAlgClRingObj l))
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicSubfieldCondensedRingToPadicAlgCl l E))
    exact h
  · have hCY := (completedCondensedIntegral.{u} Y l E π hπ).1
    have hCX := (completedCondensedIntegral.{u} X l E π hπ).1
    let cY := hCY.choose
    let eY := hCY.choose_spec.choose
    have hY := hCY.choose_spec.choose_spec.1
    let hcY := hCY.choose_spec.choose_spec.2.some
    let cX := hCX.choose
    let eX := hCX.choose_spec.choose
    have hX := hCX.choose_spec.choose_spec.1
    let hcX := hCX.choose_spec.choose_spec.2.some
    let P := (upperStarFromPoint Y).mapMon
    let Q := (upperStarFromPoint X).mapMon
    let H := ((f)^*[Ab.{u + 1}]).mapMon
    let e : P ⋙ H ≅ Q :=
      (Functor.mapMonCompIso (F := upperStarFromPoint Y)
        (G := (f)^*[Ab.{u + 1}])).symm ≪≫
        Functor.mapMonNatIso (upperStarFromPointComp f)
    let A := Mon.mk (Profinite.padicIntegersRingObj.{u} l E)
    let T (n : ℕ) := Mon.mk (Profinite.continuousMapRingObj.{u}
      (completedResidue l E π n))
    let t (n : ℕ) : T (n + 1) ⟶ T n :=
      Mon.Hom.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (completedResidueTransition l E π n))
    let r (n : ℕ) : A ⟶ T n :=
      Mon.Hom.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (completedReduction l E π n))
    have hp : Nonempty (IsLimit (H.mapCone cY)) :=
      completedLimitTransport P Q H e T t r cY cX eY eX hY hX hcX
    exact ⟨cY, eY, hY, ⟨hcY⟩, hp⟩
  · have : IsSifted (PadicAlgCl.FiniteIntermediateField l) := IsFiltered.isSifted
    refine ⟨siftedRingCoconeIsColimit _ ?_⟩
    change IsColimit (((f)^*[Ab.{u + 1}]).mapCocone (padicAlgClRingObjCocone Y l))
    exact isColimitOfPreserves ((f)^*[Ab.{u + 1}])
      (isColimitPadicAlgClRingObjCocone Y l)

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
  have hO : PadicInt.subring l = CondensedRing.continuousIntegers l ℚ_[l] := by
    ext x
    change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
    exact_mod_cast (Iff.rfl : ‖x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
  refine completedRationalOfTelescope l
    (Profinite.padicIntCondensedRing l) (Profinite.padicCondensedRing l)
    (Profinite.padicIntCondensedRingToPadicCondensedRing l) ?_ ?_
  · intro X
    exact CondensedRing.completedIntegralRegularTelescopeFor l ℚ_[l]
      (PadicInt.subring l) hO X
  · intro X
    exact CondensedRing.completedScalarIso l ℚ_[l] X

end AlgebraicGeometry.ProEtale
