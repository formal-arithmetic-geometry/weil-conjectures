/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all Sheaf.AlgebraicGeometry.CoherentFormalModule
import all Sheaf.AlgebraicGeometry.ThickeningSystemPushforwardAdic
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import Sheaf.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # Adjacent maps between second-ideal algebraizations

Source: Stacks Project, Tag 088A, the maps G_(e+1) to G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Completion restricted to coherent modules killed by the closed ideal. -/
private noncomputable abbrev supportedCompletion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : X.IdealSheafData) :=
  ObjectProperty.ι (fun F : CoherentModules X ↦ CoherentModuleSupportedOn F i) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙ formalCompletionFunctor I

/-- Transport full faithfulness across the closed coherent equivalence and its
natural completion comparison. -/
private theorem supportedCompletion_fullyFaithful {X Z : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] (I : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType i)
      (I.comap i)).IsEquivalence) :
    (supportedCompletion i I).Full ∧ (supportedCompletion i I).Faithful := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  let := he
  let P := Scheme.Modules.pushforward i
  have hbij := (closedImmersion_pushforward_fullyFaithful i).2
  let : P.Full := ⟨fun {G H} ↦ (hbij G H).2⟩
  let : P.Faithful := ⟨fun {G H} ↦ (hbij G H).1⟩
  obtain ⟨E, ⟨α⟩⟩ := closedImmersion_coherent_equivalence i
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence i I).2
  let D := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙ P ⋙
    formalCompletionFunctor I
  let R := completion Z (I.comap i) ⋙ ObjectProperty.ι (IsCoherentFormalModule
    (I.comap i)) ⋙ (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj P
  have hθ : D ≅ R := θ
  let : D.Full := Functor.Full.of_iso hθ.symm
  let : D.Faithful := Functor.Faithful.of_iso hθ.symm
  let C := supportedCompletion i I
  have hα : E.functor ⋙ C ≅ D := Functor.isoWhiskerRight α (formalCompletionFunctor I)
  let : (E.functor ⋙ C).Full := Functor.Full.of_iso hα.symm
  let : (E.functor ⋙ C).Faithful := Functor.Faithful.of_iso hα.symm
  have hε : E.inverse ⋙ (E.functor ⋙ C) ≅ C :=
    Functor.isoWhiskerRight E.counitIso C ≪≫ Functor.leftUnitor C
  exact ⟨Functor.Full.of_iso hε, Functor.Faithful.of_iso hε⟩

/-- Identify the recursive multiplication-image power with the subscheme ideal. -/
private theorem powerSupported_iff {X : Scheme.{u}} (K : X.IdealSheafData)
    (r : ℕ) (hr : 0 < r) (F : CoherentModules X) :
    CoherentModuleSupportedOn F (K ^ r).subschemeι ↔
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι r).2 F.obj) := by
  obtain ⟨a, ha⟩ := power_inclusion_iso K r hr
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ a ha F.obj
  change IsZero (Scheme.idealModuleProduct (K ^ r).subschemeι.ker.toModulesι F.obj) ↔ _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨fun h ↦ h.of_iso d, fun h ↦ h.of_iso d.symm⟩

/-- The closed ideal kills pushforward; compare the two ideal-power inclusions. -/
private theorem pushforward_power_zero {X : Scheme.{u}} [IsNoetherian X]
    (K : X.IdealSheafData) (e : ℕ) (G : CoherentModules (K ^ (e + 1)).subscheme) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (e + 1)).2
      ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj G.obj)) := by
  let i := (K ^ (e + 1)).subschemeι
  let : IsNoetherian (K ^ (e + 1)).subscheme := isNoetherian_of_locallyOfFiniteType i
  have : G.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp G.property).1
  obtain ⟨a, ha⟩ := power_inclusion_iso K (e + 1) (Nat.succ_pos e)
  obtain ⟨d, _⟩ := product_inclusion_iso _ _ a ha
    ((Scheme.Modules.pushforward i).obj G.obj)
  apply IsZero.of_iso _ d
  apply (product_zero_iff (K ^ (e + 1)) _).mpr
  intro V a ha s
  have hk : i.ker = K ^ (e + 1) := Scheme.IdealSheafData.ker_subschemeι _
  exact ((Scheme.Modules.closedImmersion_pushforward_annihilated i).1 G.obj).2
    V a (hk.symm ▸ ha) s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Adjacent quotient transitions lift to maps inducing the smaller K-quotient.
Source: Stacks Project, Tag 088A, construction of the transitions of G_e.
(blueprint: lem-weil-pbc-formal-second-ideal-algebraization-transitions).

Proof: Write F_e for the pushforward of G_e from V(K^(e+1)). It is annihilated
by K^(e+1): on each affine open the action factors through the quotient ring, and
the section image of the recursively defined power is the corresponding ideal
power. Both F_(e+1) and F_e are annihilated by K^(e+2). Closed pushforward and
completion on V(K^(e+2)) therefore identify maps between them with maps between
their I-completions. Lift the adjacent transition of the double quotient system,
conjugated by the supplied comparison isomorphisms, to obtain t. Its completion
square is the displayed equation by construction. The map factors through the
K^(e+1)-quotient since the target is annihilated by that power. Completion of this
factor is an isomorphism: the iterated K-quotient equals the smaller K-quotient,
naturally in the I-level. Both modules in the factor lie on V(K^(e+1)), where
completion is an equivalence and reflects isomorphisms. Thus the factor is the
required q, and its composite with the quotient projection is t. -/
theorem formalSecondIdealAlgebraization_transitions
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (G : ∀ e : ℕ, CoherentModules (K ^ (e + 1)).subscheme)
    (β : ∀ e : ℕ,
      formalCompletionSystem I
          ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj) ≅
        (M.obj ⋙ formalCompletionFunctor K).flip.obj (op e)) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (e + 1)).2
        ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj)) ∧
      ∃ t : (Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj ⟶
          (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
        (∃ q : formalModuleQuotient K (e + 1)
            ((Scheme.Modules.pushforward (K ^ (e + 2)).subschemeι).obj (G (e + 1)).obj) ≅
            (Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G e).obj,
          formalModuleQuotientπ K (e + 1) _ ≫ q.hom = t) ∧
        formalCompletionMap I t ≫ (β e).hom =
          (β (e + 1)).hom ≫
            (M.obj ⋙ formalCompletionFunctor K).flip.map (homOfLE (Nat.le_succ e)).op := by
  sorry

end AlgebraicGeometry
