/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.LocallyConstant.Algebra
import WeilConjectures.AlgebraicGeometry.EtaleConstantSheafPullbackUnitContinuousMap

/-!
# Constant étale sections on relative affine space

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1, the clopen locus containing
zero and every connected fibre. (blueprint: lem-pur-affine-constant-section-zero-detection)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

noncomputable section

/-- Global sections of the ordinary small étale constant abelian sheaf, evaluated
at the terminal étale object. This is an abbreviation of the recorded constant-sheaf
and site definitions, with the standard `u + 1` coefficient convention.
Source: Stacks 03P5; blueprint vector-bundle orientation proof, Step 1.
(blueprint: lem-pur-affine-constant-section-zero-detection) -/
abbrev affineConstantSections (T : Scheme.{u}) (E : Type (u + 1)) [AddCommGroup E] :
    AddCommGrpCat.{u + 1} :=
  ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of E)).obj.obj (op (⊤_ T.Etale))

/-- Actual pullback on constant-sheaf sections: the inverse-image adjunction unit,
followed by the canonical constant-sheaf comparison and the terminal-object
pushforward comparison. No choice of a function-space model is used here.
Source: Stacks 03Q1 and 0A5G; blueprint vector-bundle orientation proof, Step 1.
(blueprint: lem-pur-affine-constant-section-zero-detection) -/
def affineConstantSectionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Type (u + 1)) [AddCommGroup E] :
    affineConstantSections Y E ⟶ affineConstantSections X E :=
  (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of E))).hom.app (op (⊤_ Y.Etale))) ≫
    (((lowerStar AddCommGrpCat.{u + 1} f).map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
        (AddCommGrpCat.of E))).hom.app (op (⊤_ Y.Etale))) ≫
    (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).hom.app
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of E))

private noncomputable def terminalSchemeIso (T : Scheme.{u}) :
    (⊤_ T.Etale).left ≅ T :=
  (Scheme.Etale.forget T ⋙ Over.forget T).mapIso
    (terminalIsTerminal.uniqueUpToIso (Scheme.Etale.isTerminalMkId T))

private theorem terminalSchemeIso_hom (T : Scheme.{u}) :
    (terminalSchemeIso T).hom = (⊤_ T.Etale).hom := by
  change (terminalIsTerminal.uniqueUpToIso (Scheme.Etale.isTerminalMkId T)).hom.left = _
  have h := MorphismProperty.Over.w
    (terminalIsTerminal.uniqueUpToIso (Scheme.Etale.isTerminalMkId T)).hom
  change _ ≫ 𝟙 T = _ at h
  simpa only [Category.comp_id] using h

private noncomputable def sectionContinuousIso (T : Scheme.{u})
    (E : Type (u + 1)) [AddCommGroup E] [TopologicalSpace E] [DiscreteTopology E] :
    affineConstantSections T E ≃+ C(T, E) :=
  let i : affineConstantSections T E ≃+ C((⊤_ T.Etale).left, E) :=
    (((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op (⊤_ T.Etale))).mapIso
    (Scheme.Etale.constantSheafIsoContinuousMapSheaf T E)).addCommGroupIsoToAddEquiv
  i.trans
    { toFun := fun b ↦ b.comp (terminalSchemeIso T).inv.base.hom
      invFun := fun b ↦ b.comp (terminalSchemeIso T).hom.base.hom
      left_inv := fun b ↦ ContinuousMap.ext fun x ↦ by
        change b (((terminalSchemeIso T).hom ≫ (terminalSchemeIso T).inv) x) = b x
        rw [Iso.hom_inv_id]; rfl
      right_inv := fun b ↦ ContinuousMap.ext fun x ↦ by
        change b (((terminalSchemeIso T).inv ≫ (terminalSchemeIso T).hom) x) = b x
        rw [Iso.inv_hom_id]; rfl
      map_add' := fun _ _ ↦ rfl }

private theorem sectionContinuous_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Type (u + 1)) [AddCommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    (s : affineConstantSections Y E) (x : X) :
    sectionContinuousIso X E (affineConstantSectionPullback f E s) x =
      sectionContinuousIso Y E s (f x) := by
  let c := Scheme.Etale.constantSheafIsoContinuousMapSheaf X E
  let k := (PreservesTerminal.iso f.Etale).inv
  have hk' : k.left ≫ pullback.snd (⊤_ Y.Etale).hom f = (⊤_ X.Etale).hom :=
    MorphismProperty.Over.w k
  have hk : (terminalSchemeIso X).inv ≫ k.left ≫
      pullback.fst (⊤_ Y.Etale).hom f = f ≫ (terminalSchemeIso Y).inv := by
    apply (cancel_mono (terminalSchemeIso Y).hom).mp
    rw [Category.assoc, Category.assoc, terminalSchemeIso_hom, pullback.condition,
      ← Category.assoc k.left, hk']
    rw [← terminalSchemeIso_hom X, ← terminalSchemeIso_hom Y]
    simp
  have hn := ConcreteCategory.congr_hom
    (c.hom.hom.naturality (PreservesTerminal.iso f.Etale).op.inv)
    (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
      (AddCommGrpCat.of E)).hom.hom.app (op (f.Etale.obj (⊤_ Y.Etale)))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of E))).hom.app (op (⊤_ Y.Etale)) s))
  have h := constant_pullback_unit_continuousMap f E (⊤_ Y.Etale) s
  change (show C((⊤_ X.Etale).left, E) from c.hom.hom.app (op (⊤_ X.Etale))
    (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of E)).obj.map k.op _)) ((terminalSchemeIso X).inv x) = _
  simp only [ConcreteCategory.comp_apply] at hn
  erw [hn, h]
  exact congrArg (fun z ↦
    (show C((⊤_ Y.Etale).left, E) from
      (Scheme.Etale.constantSheafIsoContinuousMapSheaf Y E).hom.hom.app
        (op (⊤_ Y.Etale)) s) z) (congrArg (fun g ↦ g x) hk)

private theorem section_ext (T : Scheme.{u}) (E : Type (u + 1)) [AddCommGroup E]
    [TopologicalSpace E] [DiscreteTopology E] {a b : affineConstantSections T E}
    (h : ∀ x, sectionContinuousIso T E a x = sectionContinuousIso T E b x) :
    a = b := by
  apply (sectionContinuousIso T E).injective
  exact ContinuousMap.ext h

private theorem locallyConstant_zero {V : Type*} (S : Scheme.{u}) (d : ℕ)
    (b : LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) V)
    (x : AffineSpace (ULift.{u} (Fin d)) S) :
    b x = b ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
      ((AffineSpace (ULift.{u} (Fin d)) S ↘ S) x)) := by
  let p := AffineSpace (ULift.{u} (Fin d)) S ↘ S
  have hc := p.isIrreducible_preimage (AffineSpace.isOpenMap_over S)
    (isIrreducible_singleton (x := p x))
  apply b.apply_eq_of_isPreconnected hc.isPreirreducible.isPreconnected (by rfl)
  change (AffineSpace.zeroSection (ULift.{u} (Fin d)) S ≫ p) (p x) = p x
  rw [AffineSpace.zeroSection_comp_over]
  rfl

/-- Projection and zero-section pullback on ordinary étale constant sections are
inverse additive isomorphisms, natural in an arbitrary base change. Equivalently,
every locally constant function on affine space is its zero-section restriction
pulled back along the projection. A unit whose zero-section value is one is one.
Source: blueprint vector-bundle orientation proof, Step 1, clopen-locus argument.
(blueprint: lem-pur-affine-constant-section-zero-detection)

Proof:
1. By lem-weil-pbc-constant-sheaf-sections-locally-constant (Stacks 03P5), sections
   are Zariski-locally constant functions. By
   lem-weil-pbc-constant-pullback-unit-continuous-map, actual pullback is
   precomposition. Both comparisons arise from the same constant-function map
   by the universal property of sheafification, so their identifications agree.
2. By lem-pur-affine-projection-connected-fibres, the fibre over p(x) is connected.
   Both x and e(p(x)) lie in it, since the zero section composed with p is identity.
3. Within this fibre, the locus where b equals b(e(p(x))) is clopen and contains
   e(p(x)); connectedness makes it the entire fibre. Thus b(x) = b(e(p(x))).
4. The reverse composite is identity because p composed with e is identity.
   Precomposition preserves addition, giving the stated additive equivalence.
   Apply the same equality to the locally constant ring-valued function of a unit;
   restriction equal to one forces that function, and hence the unit, to be one.
5. For every g : S' ⟶ S, the affine-space map commutes with projections and zero
   sections: both equations follow on affine charts from their coefficient maps
   and coordinate values. Precomposition gives both naturality squares. The proof
   works for empty or disconnected S, d = 0, and arbitrary, possibly infinite E. -/
theorem affine_constant_section_zero_detection
    (S : Scheme.{u}) (d : ℕ) (E : Type (u + 1)) [AddCommGroup E] :
    (∃ φ : affineConstantSections S E ≃+
        affineConstantSections (AffineSpace (ULift.{u} (Fin d)) S) E,
      φ.toAddMonoidHom =
        (affineConstantSectionPullback (AffineSpace (ULift.{u} (Fin d)) S ↘ S) E).hom ∧
      φ.symm.toAddMonoidHom =
        (affineConstantSectionPullback
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) E).hom) ∧
    (∀ b : LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) E,
      ∀ x : AffineSpace (ULift.{u} (Fin d)) S,
        b x = b ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          ((AffineSpace (ULift.{u} (Fin d)) S ↘ S) x))) ∧
    (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      (affineConstantSectionPullback (AffineSpace (ULift.{u} (Fin d)) S ↘ S) E) ≫
        (affineConstantSectionPullback (AffineSpace.map (ULift.{u} (Fin d)) g) E) =
      (affineConstantSectionPullback g E) ≫
        (affineConstantSectionPullback (AffineSpace (ULift.{u} (Fin d)) S' ↘ S') E) ∧
      (affineConstantSectionPullback (AffineSpace.map (ULift.{u} (Fin d)) g) E) ≫
        (affineConstantSectionPullback
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S') E) =
      (affineConstantSectionPullback
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) E) ≫
          (affineConstantSectionPullback g E)) ∧
    (∀ (A : Type (u + 1)) [CommRing A]
      (b : (LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) A)ˣ),
      (∀ s : S, (b : LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) A)
        ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s) = 1) → b = 1) := by
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  let p := AffineSpace (ULift.{u} (Fin d)) S ↘ S
  let e := AffineSpace.zeroSection (ULift.{u} (Fin d)) S
  let P := affineConstantSectionPullback p E
  let Q := affineConstantSectionPullback e E
  have hleft (a : affineConstantSections S E) : Q (P a) = a := by
    apply section_ext S E
    intro x
    rw [sectionContinuous_pullback, sectionContinuous_pullback]
    change sectionContinuousIso S E a ((e ≫ p) x) = _
    rw [AffineSpace.zeroSection_comp_over]
    rfl
  have hright (b : affineConstantSections (AffineSpace (ULift.{u} (Fin d)) S) E) :
      P (Q b) = b := by
    apply section_ext _ E
    intro x
    rw [sectionContinuous_pullback, sectionContinuous_pullback]
    let b' : LocallyConstant (AffineSpace (ULift.{u} (Fin d)) S) E :=
      ⟨sectionContinuousIso _ E b,
        (IsLocallyConstant.iff_continuous _).2 (sectionContinuousIso _ E b).continuous⟩
    exact (locallyConstant_zero S d b' x).symm
  refine ⟨?_, locallyConstant_zero S d, ?_, ?_⟩
  · let φ : affineConstantSections S E ≃+
        affineConstantSections (AffineSpace (ULift.{u} (Fin d)) S) E :=
      { toFun := P
        invFun := Q
        left_inv := hleft
        right_inv := hright
        map_add' := fun a b ↦ map_add P.hom a b }
    exact ⟨φ, rfl, rfl⟩
  · intro S' g
    constructor
    · ext a
      apply section_ext _ E
      intro x
      simp only [ConcreteCategory.comp_apply, sectionContinuous_pullback]
      change sectionContinuousIso S E a
        ((AffineSpace.map (ULift.{u} (Fin d)) g ≫ p) x) =
          sectionContinuousIso S E a
            (((AffineSpace (ULift.{u} (Fin d)) S' ↘ S') ≫ g) x)
      rw [AffineSpace.map_over]
    · ext b
      apply section_ext _ E
      intro x
      simp only [ConcreteCategory.comp_apply, sectionContinuous_pullback]
      change sectionContinuousIso _ E b
        ((AffineSpace.zeroSection (ULift.{u} (Fin d)) S' ≫
          AffineSpace.map (ULift.{u} (Fin d)) g) x) =
        sectionContinuousIso _ E b ((g ≫ e) x)
      rw [AffineSpace.zeroSection_comp_map]
  · intro A _ b hb
    apply Units.ext
    apply LocallyConstant.ext
    intro x
    change (b : LocallyConstant _ A) x = 1
    rw [locallyConstant_zero S d (b : LocallyConstant _ A) x]
    exact hb _

end

end AlgebraicGeometry.Etale
