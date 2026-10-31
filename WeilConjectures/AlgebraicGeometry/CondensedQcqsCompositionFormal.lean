/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQcqsCompositionDefs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Formal exact and Weil compatibility from normalized composition coherence

Source: latest blueprint, lem-zl-shriek-composition.proof and
sk-thm-sf-comp-composition, composition--exchange equation.
(blueprint: lem-zl-qcqs-composition-formal-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Shift and triangle compatibility of the constructed compositor and exchanges.
Source: source proof, Steps 2 and 5
(blueprint: lem-zl-qcqs-composition-formal-compatibility). -/
def ShiftCompatibility {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    [(bc ℓ X).IsTriangulated] [(bc ℓ Z).IsTriangulated] [(bc ℓ Y).IsTriangulated]
    (A : Comparisons ℓ h g) : Prop :=
  (∀ (c : Compactification h) (d : Compactification g) (e : Compactification (h ≫ g)),
    CondensedOpenProper.ShiftTriangleCompatibility (A.alpha c d e).hom) ∧
  (∀ (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom),
    (∀ c : Compactification h,
      CondensedOpenProper.ShiftTriangleCompatibility
        ((A.exchange a b v shsq sgsq).1.iso c).hom) ∧
    (∀ d : Compactification g,
      CondensedOpenProper.ShiftTriangleCompatibility
        ((A.exchange a b v shsq sgsq).2.1.iso d).hom) ∧
    (∀ e : Compactification (h ≫ g),
      CondensedOpenProper.ShiftTriangleCompatibility
        ((A.exchange a b v shsq sgsq).2.2.iso e).hom))


private theorem pullExact {X : Scheme.{u}} [(bc ℓ X).IsTriangulated]
    (a : X ≅ X) :
    (pull ℓ a).IsEquivalence ∧ (pull ℓ a).IsTriangulated ∧
      ∀ (K : C ℓ X) (n : ℤ),
        IsZero ((DerivedCategory.homologyFunctor _ n).obj (((pull ℓ a).obj K).obj)) ↔
          IsZero ((DerivedCategory.homologyFunctor _ n).obj K.obj) := by
  obtain ⟨⟨η⟩, ⟨ε⟩⟩ := StrictWeil.action_inverse (Profinite.padicAlgClRingObj ℓ) a
  let η' : pull ℓ a ⋙ pull ℓ a.symm ≅ 𝟭 (C ℓ X) :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (η.app K.obj))
      (fun t ↦ ObjectProperty.hom_ext _ (η.hom.naturality t.hom))
  let ε' : pull ℓ a.symm ⋙ pull ℓ a ≅ 𝟭 (C ℓ X) :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (ε.app K.obj))
      (fun t ↦ ObjectProperty.hom_ext _ (ε.hom.naturality t.hom))
  refine ⟨Functor.IsEquivalence.mk' (pull ℓ a.symm) η'.symm ε', inferInstance, ?_⟩
  intro K n
  exact ⟨(upperStar (Profinite.padicAlgClRingObj ℓ) a.hom)
    |>.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj,
    (upperStar (Profinite.padicAlgClRingObj ℓ) a.hom)
      |>.isZero_homologyFunctor_mapDerivedCategory_obj⟩

private theorem weilMaps {X Y : Scheme.{u}} {f : X ⟶ Y} {S : System ℓ f}
    {a : X ≅ X} {b : Y ≅ Y} {sq : IsPullback a.hom f f b.hom}
    (E : Exchange ℓ S a b sq) : WeilMaps ℓ E := by
  intro c K L φ ψ t ht
  have he := (E.iso c).hom.naturality t
  change (pull ℓ b).map ((System.support ℓ S c).map t) ≫
    (E.iso c).hom.app L = (E.iso c).hom.app K ≫
      (System.support ℓ S c).map ((pull ℓ a).map t) at he
  rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, ht, Functor.map_comp]

private theorem weilCompatibility {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    (H : Comparisons ℓ h g) (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
    (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom) :
    WeilCompatibility ℓ H a b v shsq sgsq := by
  refine ⟨weilMaps ℓ _, weilMaps ℓ _, weilMaps ℓ _, ?_⟩
  intro c d e K φ
  rw [← Category.assoc, H.comp_exchange a b v shsq sgsq]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦
      ((H.exchange a b v shsq sgsq).2.1.iso d).hom.app ((H.sh.support ℓ c).obj K) ≫
        (H.sg.support ℓ d).map
          (((H.exchange a b v shsq sgsq).1.iso c).hom.app K) ≫ t)
      ((H.alpha c d e).hom.naturality φ.hom).symm

set_option maxHeartbeats 2000000 in
-- Elaborating the native derived-functor composites needs this allowance.
/-- Normalized composition--exchange coherence and shift compatibility imply exactness,
t-exactness of automorphism pullbacks, and transport of all strict Weil structures and maps.
Source: latest blueprint, lem-zl-shriek-composition.proof, and the stacked-square equation
of sk-thm-sf-comp-composition
(blueprint: lem-zl-qcqs-composition-formal-compatibility).

Proof: inverse automorphisms give inverse exact derived pullbacks. Their restrictions are
inverse equivalences of the bounded full subcategories. The canonical exact derived functor
is triangulated; homology commutes with it, and faithfulness reflects zero homology.
Naturality of exchange transports the equation defining an equivariant map. Applying the
composition--exchange equation and then naturality of the compositor proves its compatibility
with every input Weil isomorphism. Combine these equations with the supplied shift and triangle
compatibility; no coherence or map is chosen in this step. -/
theorem formalCompatibility {X Z Y : Scheme.{u}} {h : X ⟶ Z} {g : Z ⟶ Y}
    [(bc ℓ X).IsTriangulated] [(bc ℓ Z).IsTriangulated] [(bc ℓ Y).IsTriangulated]
    (A : Comparisons ℓ h g) (hs : ShiftCompatibility ℓ A) :
    ExactCompatibility ℓ A ∧
      ∀ (a : X ≅ X) (b : Z ≅ Z) (v : Y ≅ Y)
        (shsq : IsPullback a.hom h h b.hom) (sgsq : IsPullback b.hom g g v.hom),
        WeilCompatibility ℓ A a b v shsq sgsq := by
  refine ⟨?_, weilCompatibility ℓ A⟩
  refine ⟨hs.1, pullExact ℓ, pullExact ℓ, pullExact ℓ, ?_⟩
  intro a b v shsq sgsq
  obtain ⟨hh, hg, hhg⟩ := hs.2 a b v shsq sgsq
  exact ⟨hh, hg, hhg, weilCompatibility ℓ A a b v shsq sgsq⟩

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
