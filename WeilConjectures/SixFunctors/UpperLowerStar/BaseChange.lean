module

public import WeilConjectures.SixFunctors.UpperLowerStar.Etale
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

section Components

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h : T ⟶ R) (hh : h = h₁ ≫ h₂)

lemma lowerStarComp_hom_app_hom_app
    (M : Sheaf (T.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ R) :
    (((lowerStarComp A P Q hQP h₁ h₂ h hh).hom.app M).hom).app (op b) =
      M.obj.map ((MorphismProperty.Over.pullbackComp (P := P) (Q := ⊤) h₁ h₂ h hh).hom.app b).op := by
  simp [lowerStarComp]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStar_obj_obj_map {W U : Scheme.{u}} (g : W ⟶ U)
    (M : Sheaf (W.smallGrothendieckTopology Q (Q := P)) A) {b b' : P.Over ⊤ U} (φ : b ⟶ b') :
    ((lowerStar A P Q hQP g).obj M).obj.map φ.op =
      M.obj.map ((MorphismProperty.Over.pullback P ⊤ g).map φ).op :=
  rfl

/-- The pushforward along the identity is the identity functor. -/
noncomputable def lowerStarId (U : Scheme.{u}) :
    lowerStar A P Q hQP (𝟙 U) ≅ 𝟭 (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  have := isContinuous_overPullback P Q hQP (𝟙 U)
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := P) (Q := ⊤) U) A
    (U.smallGrothendieckTopology Q (Q := P))

lemma lowerStarId_hom_app_hom_app (U : Scheme.{u})
    (M : Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) (b : P.Over ⊤ U) :
    (((lowerStarId A P Q hQP U).hom.app M).hom).app (op b) =
      M.obj.map ((MorphismProperty.Over.pullbackId (P := P) (Q := ⊤) U).inv.app b).op := by
  simp [lowerStarId]

end Components

section Coherence

variable {R S T V : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h₃ : R ⟶ V)

/-- Associativity coherence of the composition isomorphism of pushforwards. -/
lemma lowerStarComp_assoc (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (h : T ⟶ V) (e : h = h₁₂ ≫ h₃) (e' : h = h₁ ≫ h₂₃) :
    Functor.whiskerRight (lowerStarComp A P Q hQP h₁ h₂ h₁₂ e₁₂).hom
          (lowerStar A P Q hQP h₃) ≫
        (lowerStarComp A P Q hQP h₁₂ h₃ h e).hom =
      (Functor.associator (lowerStar A P Q hQP h₁) (lowerStar A P Q hQP h₂)
            (lowerStar A P Q hQP h₃)).hom ≫
        Functor.whiskerLeft (lowerStar A P Q hQP h₁)
            (lowerStarComp A P Q hQP h₂ h₃ h₂₃ e₂₃).hom ≫
          (lowerStarComp A P Q hQP h₁ h₂₃ h e').hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStar_map_hom_app, lowerStar_obj_obj_map,
    ← Functor.map_comp, ← op_comp]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_hom_assoc (P := P) (Q := ⊤)
    h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ h e e') b

/-- Unit coherence of the composition isomorphism of pushforwards: composing with the
identity on the target. -/
lemma lowerStarComp_id_right {W U : Scheme.{u}} (g : W ⟶ U) (e : g = g ≫ 𝟙 U) :
    (lowerStarComp A P Q hQP g (𝟙 U) g e).hom =
      Functor.whiskerLeft (lowerStar A P Q hQP g) (lowerStarId A P Q hQP U).hom ≫
        (lowerStar A P Q hQP g).rightUnitor.hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_obj_obj_map]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_id_right (P := P) (Q := ⊤) g) b

/-- Unit coherence of the composition isomorphism of pushforwards: composing with the
identity on the source. -/
lemma lowerStarComp_id_left {W U : Scheme.{u}} (g : W ⟶ U) (e : g = 𝟙 W ≫ g) :
    (lowerStarComp A P Q hQP (𝟙 W) g g e).hom =
      Functor.whiskerRight (lowerStarId A P Q hQP W).hom (lowerStar A P Q hQP g) ≫
        (lowerStar A P Q hQP g).leftUnitor.hom := by
  ext M b
  obtain ⟨b⟩ := b
  simp [lowerStarComp_hom_app_hom_app, lowerStarId_hom_app_hom_app, lowerStar_map_hom_app]
  congr 2
  simpa using congr_app (MorphismProperty.Over.pullbackComp_id_left (P := P) (Q := ⊤) g) b

end Coherence

section UpperStarCoherence

/-- The pullback along the identity is the identity functor. -/
noncomputable def upperStarId (U : Scheme.{u}) :
    upperStar A P Q (𝟙 U) ≅ 𝟭 (Sheaf (U.smallGrothendieckTopology Q (Q := P)) A) :=
  ((conjugateIsoEquiv (upperStarLowerStarAdjunction A P Q hQP (𝟙 U)) Adjunction.id).symm
    (lowerStarId A P Q hQP U)).symm

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) (h : T ⟶ R) (hh : h = h₁ ≫ h₂)

lemma conjugateEquiv_upperStarComp_hom :
    conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
          (upperStarLowerStarAdjunction A P Q hQP h₁))
        (upperStarLowerStarAdjunction A P Q hQP h)
        (upperStarComp A P Q hQP h₁ h₂ h hh).hom =
      (lowerStarComp A P Q hQP h₁ h₂ h hh).hom := by
  simp [upperStarComp]

lemma conjugateEquiv_upperStarId_inv (U : Scheme.{u}) :
    conjugateEquiv (upperStarLowerStarAdjunction A P Q hQP (𝟙 U)) Adjunction.id
        (upperStarId A P Q hQP U).inv =
      (lowerStarId A P Q hQP U).hom := by
  simp [upperStarId]

variable {V : Scheme.{u}} (h₃ : R ⟶ V)

lemma upperStarComp_assoc (h₁₂ : T ⟶ R) (e₁₂ : h₁₂ = h₁ ≫ h₂) (h₂₃ : S ⟶ V)
    (e₂₃ : h₂₃ = h₂ ≫ h₃) (hh' : T ⟶ V) (e : hh' = h₁₂ ≫ h₃) (e' : hh' = h₁ ≫ h₂₃) :
    (upperStarComp A P Q hQP h₁₂ h₃ hh' e).hom ≫
        Functor.whiskerLeft (upperStar A P Q h₃) (upperStarComp A P Q hQP h₁ h₂ h₁₂ e₁₂).hom =
      (upperStarComp A P Q hQP h₁ h₂₃ hh' e').hom ≫
        Functor.whiskerRight (upperStarComp A P Q hQP h₂ h₃ h₂₃ e₂₃).hom (upperStar A P Q h₁) ≫
          (Functor.associator (upperStar A P Q h₃) (upperStar A P Q h₂)
            (upperStar A P Q h₁)).hom := by
  apply (conjugateEquiv
    ((upperStarLowerStarAdjunction A P Q hQP h₃).comp
      ((upperStarLowerStarAdjunction A P Q hQP h₂).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)))
    (upperStarLowerStarAdjunction A P Q hQP hh')).injective
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP h₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁₂)) _,
      ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP h₂₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)) _,
      ← conjugateEquiv_comp _ (((upperStarLowerStarAdjunction A P Q hQP h₃).comp
        (upperStarLowerStarAdjunction A P Q hQP h₂)).comp
        (upperStarLowerStarAdjunction A P Q hQP h₁)) _,
      conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_associator_hom,
      conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarComp_hom,
      conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarComp_hom]
  simpa using lowerStarComp_assoc A P Q hQP h₁ h₂ h₃ h₁₂ e₁₂ h₂₃ e₂₃ hh' e e'

lemma upperStarComp_id_right {W U : Scheme.{u}} (g : W ⟶ U) (e : g = g ≫ 𝟙 U) :
    (upperStarComp A P Q hQP g (𝟙 U) g e).hom =
      (upperStar A P Q g).leftUnitor.inv ≫
        Functor.whiskerRight (upperStarId A P Q hQP U).inv (upperStar A P Q g) := by
  apply (conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP (𝟙 U)).comp
    (upperStarLowerStarAdjunction A P Q hQP g))
    (upperStarLowerStarAdjunction A P Q hQP g)).injective
  rw [← conjugateEquiv_comp _ (Adjunction.id.comp (upperStarLowerStarAdjunction A P Q hQP g)) _,
    conjugateEquiv_whiskerRight, conjugateEquiv_leftUnitor_inv,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarId_inv]
  exact lowerStarComp_id_right A P Q hQP g e

lemma upperStarComp_id_left {W U : Scheme.{u}} (g : W ⟶ U) (e : g = 𝟙 W ≫ g) :
    (upperStarComp A P Q hQP (𝟙 W) g g e).hom =
      (upperStar A P Q g).rightUnitor.inv ≫
        Functor.whiskerLeft (upperStar A P Q g) (upperStarId A P Q hQP W).inv := by
  apply (conjugateEquiv ((upperStarLowerStarAdjunction A P Q hQP g).comp
    (upperStarLowerStarAdjunction A P Q hQP (𝟙 W)))
    (upperStarLowerStarAdjunction A P Q hQP g)).injective
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A P Q hQP g).comp Adjunction.id) _,
    conjugateEquiv_whiskerLeft, conjugateEquiv_rightUnitor_inv,
    conjugateEquiv_upperStarComp_hom, conjugateEquiv_upperStarId_inv]
  exact lowerStarComp_id_left A P Q hQP g e


end UpperStarCoherence

end CategoryTheory.GrothendieckTopology
