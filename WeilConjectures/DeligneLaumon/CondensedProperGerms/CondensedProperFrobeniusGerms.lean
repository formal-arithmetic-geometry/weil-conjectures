/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.DeligneLaumon.CondensedGlobalProper.CondensedGlobalProperFrobenius
public import WeilConjectures.DeligneLaumon.FrobeniusCohomologyTransportIso
public import WeilConjectures.DeligneLaumon.ProperSemilinearGerms.ProperSectionsSemilinearGerms
public import WeilConjectures.DeligneLaumon.CondensedProperSingle.CondensedProperSingleNormalization
import WeilConjectures.DeligneLaumon.CondensedModule.CondensedProperGermTransportComposition

/-! # Proper condensed sections and geometric Frobenius germs

Source: latest blueprint, sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
lem-a1-finite-boundary-weights.proof.md, opening evaluation and local stability
(blueprint: lem-a1-condensed-proper-frobenius-germs).

All sections and fibres use actual condensed modules. Positive exponents are indexed by n+1.
The scalar lift is the same canonical lift used by CondensedModule.fibre and pointSections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedProperGerms

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [IsProper Y₀.hom]

/-- Properness of the geometric fibre is the base change of properness of Y₀.
Source: proper morphisms are stable under base change.
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
instance geometricFiber_isProper : IsProper (D.geometricFiber Y₀).hom := by
  change IsProper (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

/-- The point and geometric Frobenius arrows are the homs of their specified isomorphisms.
Source: the definitions of frobeniusPointIso and geometricFrobenius.
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
instance point_frobenius_isIso : IsIso (frobeniusPointIso D).hom :=
  ⟨⟨(frobeniusPointIso D).inv, (frobeniusPointIso D).hom_inv_id,
    (frobeniusPointIso D).inv_hom_id⟩⟩

instance geometric_frobenius_isIso : IsIso (D.geometricFrobenius Y₀).hom :=
  ⟨⟨(D.geometricFrobenius Y₀).inv, (D.geometricFrobenius Y₀).hom_inv_id,
    (D.geometricFrobenius Y₀).inv_hom_id⟩⟩

/-- Exact pullback of the degree-zero module gives its derived Weil isomorphism.
Source: the node's actual-module hypothesis and exactness in proof step 1
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def singleWeil
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) :=
  CondensedProperOrdinaryZero.weilStructure
    (Y := (D.geometricFiber Y₀).left) l (D.geometricFrobenius Y₀).hom M

/-- Degree-zero compact cohomology, with exact geometric evaluation after homology.
This is H^0(Fib_s(Ra_! M[0])) since pointSections is exact.
Source: def-weil-ordinary-compact-cohomology, displayed H_c formula
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
abbrev sections :=
  CondensedProperSingle.sections (Y := (D.geometricFiber Y₀).left) l D.k (D.geometricFiber Y₀).hom

/-- Canonical proper/augmentation comparison with ordinary sections of a_*M.
Source: proof steps 2--3, H^0(Ra_*M[0])=a_*M and identity compactification
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def sectionsComparison (M : CondensedModule.Modules l (D.geometricFiber Y₀).left) :
    (sections l D Y₀).obj M ≅
      (CondensedRing.pointSections l D.k).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (D.geometricFiber Y₀).hom).obj M) :=
  CondensedProperSingle.sectionsComparison
    (Y := (D.geometricFiber Y₀).left) l D.k (D.geometricFiber Y₀).hom M

set_option maxHeartbeats 1000000 in
-- Allow the geometric-fibre category conversions to finish.
/-- The canonical germ: proper comparison, degree-zero augmentation, identity pullback,
then the actual pullback-composition/counit restriction.
Source: proof step 7 and the opening evaluation sentence
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
def evaluation (M : CondensedModule.Modules l (D.geometricFiber Y₀).left)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (sections l D Y₀).obj M ⟶ CondensedModule.fibre l D M z :=
  CondensedProperSingle.finiteEvaluation (T := (D.geometricFiber Y₀).left)
    l D (D.geometricFiber Y₀).hom M z hz

/-- The specified r-fold Weil and point-comparison map, at r=n+1.
Source: proof steps 8--10, the ordered Weil iterate and its canonical compositors
(blueprint: lem-a1-condensed-proper-frobenius-germs). -/
@[irreducible] def transport
    (M : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :=
  CondensedModule.transport l D (D.geometricFrobenius Y₀).hom M.carrier M.str z
    (ProperSemilinearGerms.movingPoint D Y₀ z n) n
    (ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).2.symm

-- Proof-local aliases must reduce when the simplifier checks categorical types.
-- This follows the local-attribute pattern in AutomorphismInverseComparisonDescent.
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut CategoryTheory.Endofunctor.IsoAlgebra
  WeilConjectures.CondensedModule.fibre
set_option allowUnsafeReducibility true in
attribute [local reducible] localPositivePower

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem evaluateStep_naturality {C : Type*} [Category C]
    (F G H : C ⥤ C) (c : H ≅ G ⋙ F) {M N : C}
    (θ : G.obj M ≅ M) (ψ : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ ψ.hom = θ.hom ≫ f) :
    H.map f ≫ (CondensedModule.evaluateStep F G H c N ψ).hom =
      (CondensedModule.evaluateStep F G H c M θ).hom ≫ F.map f := by
  simp only [CondensedModule.evaluateStep, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, c.hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← F.map_comp, hf, F.map_comp]

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem isoChain_naturality {C : Type*} [Category C]
    (P Q : ℕ → C) (M N : C) (f : M ⟶ N) (fs : ∀ n, P n ⟶ Q n)
    (iM : P 0 ≅ M) (iN : Q 0 ≅ N)
    (sM : ∀ n, P (n + 1) ≅ P n) (sN : ∀ n, Q (n + 1) ≅ Q n)
    (hi : fs 0 ≫ iN.hom = iM.hom ≫ f)
    (hs : ∀ n, fs (n + 1) ≫ (sN n).hom = (sM n).hom ≫ fs n) (n : ℕ) :
    fs n ≫ (CondensedModule.isoChain Q N iN sN n).hom =
      (CondensedModule.isoChain P M iM sM n).hom ≫ f := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    dsimp only [CondensedModule.isoChain] at ih
    change fs (n + 1) ≫ ((sN n).hom ≫ _) = ((sM n).hom ≫ _) ≫ f
    rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]

private theorem functorChain_naturality {C : Type*} [Category C]
    (Fs : ℕ → C ⥤ C) (G : C ⥤ C) (c0 : Fs 0 ≅ G)
    (cs : ∀ n, Fs (n + 1) ≅ G ⋙ Fs n)
    (M N : C) (f : M ⟶ N) (θ : G.obj M ≅ M) (ψ : G.obj N ≅ N)
    (hf : G.map f ≫ ψ.hom = θ.hom ≫ f) (n : ℕ) :
    (Fs n).map f ≫
        (CondensedModule.isoChain (fun n ↦ (Fs n).obj N) N
          (CondensedModule.evaluateInitial (Fs 0) G c0 N ψ)
          (fun n ↦ CondensedModule.evaluateStep (Fs n) G (Fs (n + 1)) (cs n) N ψ) n).hom =
      (CondensedModule.isoChain (fun n ↦ (Fs n).obj M) M
          (CondensedModule.evaluateInitial (Fs 0) G c0 M θ)
          (fun n ↦ CondensedModule.evaluateStep (Fs n) G (Fs (n + 1)) (cs n) M θ) n).hom ≫ f := by
  apply isoChain_naturality (fs := fun n ↦ (Fs n).map f)
  · have hc := c0.hom.naturality f
    simp only [CondensedModule.evaluateInitial, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, hc, Category.assoc, hf, Category.assoc]
  · intro n
    exact evaluateStep_naturality _ _ _ _ θ ψ f hf

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem iterate_naturality {T : Scheme.{u}} (a : T ⟶ T)
    (M N : condensedWeilModules (Profinite.padicAlgClRingObj l) a) (f : M ⟶ N) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).map f.hom.f ≫
        (CondensedModule.iterate l a N.carrier N.str n).hom =
      (CondensedModule.iterate l a M.carrier M.str n).hom ≫ f.hom.f := by
  have he : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f.hom.f ≫
      N.str.hom = M.str.hom ≫ f.hom.f := by
    simpa only [CategoryTheory.Endofunctor.IsoAlgebra.str_hom] using f.hom.h
  unfold CondensedModule.iterate CondensedModule.iterateStep
  exact functorChain_naturality
    (fun n ↦ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) (Eq.refl a))
    (fun n ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l)
      (localPositivePower a n) a) M.carrier N.carrier f.hom.f M.str N.str he n

private theorem mappedTransport_naturality
    {C B E : Type*} [Category C] [Category B] [Category E]
    (P : B ⥤ E) (G : C ⥤ B) (H : C ⥤ C) (F : C ⥤ B)
    (α : G ⋙ 𝟭 B ≅ H ⋙ F) {M N : C} (f : M ⟶ N)
    (iM : H.obj M ≅ M) (iN : H.obj N ≅ N)
    (h : H.map f ≫ iN.hom = iM.hom ≫ f) :
    P.map (G.map f) ≫ (P.mapIso (α.app N ≪≫ F.mapIso iN)).hom =
      (P.mapIso (α.app M ≪≫ F.mapIso iM)).hom ≫ P.map (F.map f) := by
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom]
  rw [← P.map_comp, ← P.map_comp]
  congr 1
  have hα := α.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hα
  rw [← Category.assoc, hα]
  simp only [Category.assoc]
  rw [← F.map_comp, h, F.map_comp]

set_option maxHeartbeats 1000000 in
-- The specialization checks concrete module-valued pullback functors.
private theorem nativeTransport_naturality {T : Scheme.{u}} (a : T ⟶ T)
    (M N : condensedWeilModules (Profinite.padicAlgClRingObj l) a) (f : M ⟶ N)
    (z z' : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z') :
    (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').map f.hom.f) ≫
        (CondensedModule.transport l D a N.carrier N.str z z' n h).hom =
      (CondensedModule.transport l D a M.carrier M.str z z' n h).hom ≫
        (CondensedRing.pointSections l D.k).map
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f.hom.f) := by
  unfold CondensedModule.transport
  exact mappedTransport_naturality _ _ _ _ _ f.hom.f _ _
    (iterate_naturality l a M N f n)

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem transport_naturality
    (M N : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) (f : M ⟶ N)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ) :
    (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (ProperSemilinearGerms.movingPoint D Y₀ z n)).map f.hom.f) ≫
        (transport l D Y₀ N z hz n).hom =
      (transport l D Y₀ M z hz n).hom ≫ (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f.hom.f) := by
  unfold transport
  exact nativeTransport_naturality l D _ M N f _ _ n _

section ClosedPointGeometry

set_option allowUnsafeReducibility true in
attribute [local reducible] FiniteFieldDatum.geometricFiber CategoryTheory.Over.pullback

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem closedPoint_lift
    (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hx : (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).base
        (IsLocalRing.closedPoint D.k) = x.val) :
    ∃ (ι : Y₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
      localClosedPoint D Y₀ x ι hι = z := by
  change z ≫ pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _ at hz
  let z₀ := z ≫ pullback.fst Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let e := Scheme.SpecToEquivOfField D.k Y₀.left
  have hy : (e z₀).1 = x.val := hx
  let i : Y₀.left.residueField x.val ⟶ CommRingCat.of D.k :=
    (Y₀.left.residueFieldCongr hy.symm).hom ≫ (e z₀).2
  have hpair : e z₀ = ⟨x.val, i⟩ := by
    apply Scheme.SpecToEquivOfField_eq_iff.mpr
    refine ⟨hy, ?_⟩
    simp [i]
  have ha : Spec.map i ≫ Y₀.left.fromSpecResidueField x.val = z₀ := by
    have h := e.symm_apply_apply z₀
    rw [hpair] at h
    exact h
  have hbase : z₀ ≫ Y₀.hom =
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    dsimp [z₀]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp]
  have hι : i.hom.comp (Y₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k := by
    rw [← ha, Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
      ← Spec.map_comp] at hbase
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hbase)
  refine ⟨i.hom, hι, ?_⟩
  apply pullback.hom_ext
  · simpa only [localClosedPoint, pullback.lift_fst, CommRingCat.ofHom_hom, z₀] using ha
  · simpa only [localClosedPoint, pullback.lift_snd] using hz.symm

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem closedPoint_return
    (x : {x : Y₀.left // x ∈ closedPoints Y₀.left})
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hx : (z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).base
        (IsLocalRing.closedPoint D.k) = x.val) :
    z ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        (localClosedPointDegree D Y₀ x - 1) =
      localPositivePower (frobeniusPointIso D).hom
        (localClosedPointDegree D Y₀ x - 1) ≫ z := by
  obtain ⟨ι, hι, rfl⟩ := closedPoint_lift D Y₀ x z hz hx
  exact localClosedPoint_return D Y₀ x ι hι

end ClosedPointGeometry

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem positivePower_isIso {X : Scheme.{u}}
    (g : X ⟶ X) [IsIso g] (n : ℕ) : IsIso (localPositivePower g n) := by
  induction n with
  | zero => exact inferInstanceAs (IsIso g)
  | succ n ih =>
    let := ih
    change IsIso (localPositivePower g n ≫ g)
    exact IsIso.comp_isIso' ih (inferInstanceAs (IsIso g))

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem movingPoint_return
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (hr : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    ProperSemilinearGerms.movingPoint D Y₀ z n = z := by
  have := positivePower_isIso (frobeniusPointIso D).hom n
  exact (cancel_epi (localPositivePower (frobeniusPointIso D).hom n)).mp
    ((ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n).2.trans hr)

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem transport_eq_operator {T : Scheme.{u}} (a : T ⟶ T)
    (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z')
    (hr : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (ret : z' = z) :
    eqToHom (congrArg (CondensedModule.fibre l D M) ret.symm) ≫
        (CondensedModule.transport l D a M θ z z' n h).hom =
      CondensedModule.operator l D a M θ z n hr := by
  subst z'
  simp only [eqToHom_refl, Category.id_comp, CondensedModule.operator]

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem evaluation_naturality
    {M N : CondensedModule.Modules l (D.geometricFiber Y₀).left} (f : M ⟶ N)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    (sections l D Y₀).map f ≫ evaluation l D Y₀ N z hz =
      evaluation l D Y₀ M z hz ≫ (CondensedProperSingle.scalarSections l D.k).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f) := by
  exact CondensedProperSingle.finiteEvaluation_naturality
    (T := (D.geometricFiber Y₀).left) l D (D.geometricFiber Y₀).hom f z hz

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem ordinary_naturality
    (M N : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom) (f : M ⟶ N) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of D.k)))).map
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
          (D.geometricFiber Y₀).hom).map f.hom.f) ≫
      CondensedProperOrdinaryZero.ordinary
        (Y := (D.geometricFiber Y₀).left) l D.k (D.geometricFiber Y₀).hom
        (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
        (D.galoisMap_projections Y₀.hom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _)).2 N =
      CondensedProperOrdinaryZero.ordinary
        (Y := (D.geometricFiber Y₀).left) l D.k (D.geometricFiber Y₀).hom
        (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
        (D.galoisMap_projections Y₀.hom
          (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
            (Fintype.ofFinite D.k₀) _ _ _)).2 M ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (𝟙 (Spec (.of D.k)))).map
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l)
            (D.geometricFiber Y₀).hom).map f.hom.f) := by
  exact CondensedProperOrdinaryZero.ordinary_naturality
    (Y := (D.geometricFiber Y₀).left) l D.k (D.geometricFiber Y₀).hom
    (D.geometricFrobenius Y₀).hom (frobeniusPointIso D).hom
    (D.galoisMap_projections Y₀.hom
      (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
        (Fintype.ofFinite D.k₀) _ _ _)).2 M N f

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem mapped_commutation {B E : Type*} [Category B] [Category E]
    (P : B ⥤ E) {X Y : B} (f : X ⟶ Y) (oX : X ⟶ X) (oY : Y ⟶ Y)
    (h : f ≫ oY = oX ≫ f) :
    P.map f ≫ P.map oY = P.map oX ≫ P.map f := by
  rw [← P.map_comp, h, P.map_comp]

private theorem intertwining_naturality {E : Type*} [Category E]
    {X Y X' Y' : E} (f : X ⟶ Y) (g : X' ⟶ Y')
    (cX : X ≅ X') (cY : Y ≅ Y')
    (F : X ⟶ X) (G : Y ⟶ Y) (F' : X' ⟶ X') (G' : Y' ⟶ Y')
    (hc : f ≫ cY.hom = cX.hom ≫ g)
    (hX : F ≫ cX.hom = cX.hom ≫ F')
    (hY : G ≫ cY.hom = cY.hom ≫ G') (ho : g ≫ G' = F' ≫ g) :
    f ≫ G = F ≫ f := by
  apply (cancel_mono cY.hom).mp
  rw [Category.assoc, hY, ← Category.assoc, hc, Category.assoc, ho,
    ← Category.assoc, ← hX, Category.assoc, ← hc, ← Category.assoc]

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
private theorem evaluation_iterate (hl : l ≠ D.p)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom)
    (z z' : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (hz : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _)
    (hz' : z' ≫ (D.geometricFiber Y₀).hom = 𝟙 _) (n : ℕ)
    (ht : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z') :
    ((frobenius l D Y₀ hl M) ^ (n + 1)).asHom ≫
        evaluation l D Y₀ M.obj.carrier z hz =
      evaluation l D Y₀ M.obj.carrier z' hz' ≫
        (CondensedModule.transport l D (D.geometricFrobenius Y₀).hom
          M.obj.carrier M.obj.str z z' n ht).hom := by
  induction n generalizing z' with
  | zero => simpa only [Nat.zero_add, pow_one] using evaluation_one l D Y₀ hl M z z' hz hz' ht
  | succ n ih =>
    let t := ProperSemilinearGerms.movingPoint D Y₀ z n
    have ht₀ := ProperSemilinearGerms.movingPoint_properties D Y₀ z hz n
    have ht₁ : t ≫ (D.geometricFrobenius Y₀).hom = (frobeniusPointIso D).hom ≫ z' := by
      let := positivePower_isIso (frobeniusPointIso D).hom n
      apply (cancel_epi (localPositivePower (frobeniusPointIso D).hom n)).mp
      calc
        localPositivePower (frobeniusPointIso D).hom n ≫
            (t ≫ (D.geometricFrobenius Y₀).hom) =
            (z ≫ localPositivePower (D.geometricFrobenius Y₀).hom n) ≫
              (D.geometricFrobenius Y₀).hom := by rw [← Category.assoc, ht₀.2]
        _ = _ := by simpa only [localPositivePower, Category.assoc] using ht
    rw [pow_succ, End.mul_def, Category.assoc, ih t ht₀.1 ht₀.2.symm,
      ← Category.assoc, evaluation_one l D Y₀ hl M t z' ht₀.1 hz' ht₁,
      Category.assoc, CondensedModule.properGerm_transport_comp l D
        (D.geometricFrobenius Y₀).hom M.obj.carrier M.obj.str z t z' n
          ht₀.2.symm ht₁ ht]

private theorem map_twice_isIso {B C E : Type*} [Category B] [Category C] [Category E]
    (F : B ⥤ C) (G : C ⥤ E) {X Y : B} (f : X ⟶ Y) (hf : IsIso f) :
    IsIso (G.map (F.map f)) := by
  let : IsIso f := hf
  infer_instance

set_option maxHeartbeats 1000000 in
-- The concrete sheaf-module interfaces make definitional equality checks expensive.
set_option maxHeartbeats 1000000 in
-- Combining the native geometric-fibre statements needs substantial conversion work.
end WeilConjectures.CondensedProperGerms
