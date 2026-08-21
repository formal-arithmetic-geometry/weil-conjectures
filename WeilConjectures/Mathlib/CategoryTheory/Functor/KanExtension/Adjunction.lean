/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Left Kan extension along a left adjoint

If `L : C ⥤ D` admits a right adjoint `R`, the left Kan extension functor `L.lan` is
precomposition with `R` (`CategoryTheory.Functor.lanIsoWhiskeringLeft`): both are left
adjoint to precomposition with `L`. Consequently `L.lan` preserves every limit that exists
in the target category (`CategoryTheory.Functor.preservesLimitsOfShape_lan`), since limits
in functor categories are computed pointwise.

This is complementary to `CategoryTheory.lan_preservesFiniteLimits_of_flat`, which holds for
an arbitrary representably flat `L` but computes `L.lan` as a filtered colimit and therefore
assumes the source and target sites to be small and the coefficient category to be concrete
with filtered colimits commuting with finite limits. Along a left adjoint no such hypothesis
is needed, because the colimit is over a category with a terminal object.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe vC uC vD uD vH uH w₁ w₂

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {H : Type uH} [Category.{vH} H] {L : C ⥤ D} {R : D ⥤ C}

section Adjunction

variable [∀ F : C ⥤ H, L.HasLeftKanExtension F]

/-- If `adj : L ⊣ R`, then the left Kan extension along `L` is precomposition with `R`:
both are left adjoint to precomposition with `L`. -/
noncomputable def lanIsoWhiskeringLeft (adj : L ⊣ R) :
    (L.lan : (C ⥤ H) ⥤ D ⥤ H) ≅ (whiskeringLeft D C H).obj R :=
  (L.lanAdjunction H).leftAdjointUniq (Adjunction.whiskerLeft H adj)

/-- Left Kan extension along a left adjoint preserves limits of any shape that exists in the
target category. -/
lemma preservesLimitsOfShape_lan_of_adjunction (adj : L ⊣ R) (E : Type w₁) [Category.{w₂} E]
    [HasLimitsOfShape E H] : PreservesLimitsOfShape E (L.lan : (C ⥤ H) ⥤ D ⥤ H) :=
  preservesLimitsOfShape_of_natIso (lanIsoWhiskeringLeft (H := H) adj).symm

end Adjunction

section IsLeftAdjoint

variable (L) [L.IsLeftAdjoint] [∀ F : C ⥤ H, L.HasLeftKanExtension F]

/-- Left Kan extension along a left adjoint preserves limits of any shape that exists in the
target category. -/
instance preservesLimitsOfShape_lan (E : Type w₁) [Category.{w₂} E] [HasLimitsOfShape E H] :
    PreservesLimitsOfShape E (L.lan : (C ⥤ H) ⥤ D ⥤ H) :=
  preservesLimitsOfShape_lan_of_adjunction (Adjunction.ofIsLeftAdjoint L) E

/-- Left Kan extension along a left adjoint is left exact. -/
instance preservesFiniteLimits_lan [HasFiniteLimits H] :
    PreservesFiniteLimits (L.lan : (C ⥤ H) ⥤ D ⥤ H) where
  preservesFiniteLimits _ := inferInstance

end IsLeftAdjoint

end CategoryTheory.Functor
