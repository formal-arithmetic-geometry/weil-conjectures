module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transport of lax structures and adjunction mates along monoidal equivalences

Source: Stacks Project, Categories, Tag 001J (definition-equivalence-categories), and
Mathlib.CategoryTheory.Monoidal.Functor, `Adjunction.leftAdjointOplaxMonoidal`.
(blueprint: lem-pd-monoidal-adjunction-equivalence-transport)
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory

open MonoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- Lift the unit and tensorator through a fully faithful strong monoidal functor.
Faithfulness reduces coherence to the given composite lax structure. -/
@[instance_reducible]
private noncomputable def liftLax
    {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
    {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
    (E : A ⥤ A') [E.Full] [E.Faithful] [E.Monoidal]
    (R : B ⥤ A) [(R ⋙ E).LaxMonoidal] : R.LaxMonoidal where
  ε := E.preimage (η E ≫ ε (R ⋙ E))
  μ X Y := E.preimage (δ E (R.obj X) (R.obj Y) ≫ μ (R ⋙ E) X Y)
  μ_natural_left {X Y} g Z := by
    apply E.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, map_whiskerRight,
      Category.assoc, μ_δ_assoc]
    exact congrArg (δ E (R.obj X) (R.obj Z) ≫ ·) (μ_natural_left (R ⋙ E) g Z)
  μ_natural_right {X Y} Z g := by
    apply E.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, map_whiskerLeft,
      Category.assoc, μ_δ_assoc]
    exact congrArg (δ E (R.obj Z) (R.obj X) ≫ ·) (μ_natural_right (R ⋙ E) Z g)
  associativity X Y Z := by
    apply E.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, map_whiskerLeft,
      map_whiskerRight, Category.assoc, comp_whiskerRight,
      MonoidalCategory.whiskerLeft_comp, μ_δ_assoc]
    rw [← Functor.OplaxMonoidal.associativity_assoc]
    exact congrArg
      (δ E (R.obj X ⊗ R.obj Y) (R.obj Z) ≫
        δ E (R.obj X) (R.obj Y) ▷ E.obj (R.obj Z) ≫ ·)
      (Functor.LaxMonoidal.associativity (R ⋙ E) X Y Z)
  left_unitality X := by
    apply E.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, map_whiskerRight,
      map_leftUnitor, Category.assoc, comp_whiskerRight, μ_δ_assoc]
    exact congrArg (δ E (𝟙_ A) (R.obj X) ≫ η E ▷ E.obj (R.obj X) ≫ ·)
      (Functor.LaxMonoidal.left_unitality (R ⋙ E) X)
  right_unitality X := by
    apply E.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, map_whiskerLeft,
      map_rightUnitor, Category.assoc, MonoidalCategory.whiskerLeft_comp, μ_δ_assoc]
    exact congrArg (δ E (R.obj X) (𝟙_ A) ≫ E.obj (R.obj X) ◁ η E ≫ ·)
      (Functor.LaxMonoidal.right_unitality (R ⋙ E) X)

/-- Transport of a lax right-adjoint structure, including uniqueness and the exact tensor
and unit identities for its left-adjoint oplax mate.

Source: Stacks Project, Categories, Tag 001J (definition-equivalence-categories), for the
fully faithful equivalence setting; the mate conventions are those of
`Adjunction.leftAdjointOplaxMonoidal` in Mathlib.CategoryTheory.Monoidal.Functor.
(blueprint: lem-pd-monoidal-adjunction-equivalence-transport)

Proof: First equip `F ⋙ R'` with the composite lax structure: its tensor map is the
lax tensor map of `R'` followed by `R'.map` of the tensorator of `F`, and its unit is
similarly the unit of `R'` followed by `R'.map` of the unit of `F`. Naturality follows
from the naturality of these maps. Expand associativity and use the associativity
axioms of `F` and `R'`; expand the two unit equations and use their unit axioms.
Conjugate this structure by `β` to obtain a lax structure on `R ⋙ E`. Naturality and
all three coherence equations follow by postcomposing with `β` and cancelling its
invertible components. Lift the resulting tensor and unit maps uniquely through
fully faithful `E`, after precomposition with the inverses of its strong structure
maps. Naturality follows by applying `E`, precomposing with its tensorator, and
cancelling. For associativity precompose with the iterated tensorator of `E`;
for each unit equation precompose with its unit and tensorator. Its coherence
axioms reduce these equations to those already proved for `R ⋙ E`. Faithfulness
then gives the equations before applying `E`. The defining lifts are precisely
the two displayed monoidality equations. Conversely, these equations force the
images of every tensor and unit map, so faithfulness gives uniqueness.

Apply `lem-sfb-adjunction-oplax-mate`, namely `Adjunction.leftAdjointOplaxMonoidal`,
to both adjunctions. Applying `hcompat` to the identity of `L.obj X` compares their
units. Substitute this unit comparison into the tensor-mate transpose formula,
and use the monoidality equation and naturality of the primed lax tensorator.
Naturality of the primed Hom bijection identifies the resulting transpose with
that of the displayed transported tensor mate. Injectivity gives the tensor
identity. The unit monoidality equation, the unit-mate formula and `hcompat`
similarly give the displayed unit identity by injectivity of the Hom bijection.
Finally, if the primed mate maps are invertible, all factors in both transported
formulas are invertible. Thus their images under `F` are invertible. Lift each
inverse by fullness of `F` and check both inverse identities by faithfulness.
The mate convention agrees with `CategoryTheory.mateEquiv` from
`def-weil-pbc-adjunction-mate`. -/
theorem exists_unique_laxMonoidal_adjunction_equivalence_transport
    {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
    {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
    {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
    {B' : Type u₄} [Category.{v₄} B'] [MonoidalCategory B']
    (E : A ⥤ A') [E.Full] [E.Faithful] [E.EssSurj] (e : E.CoreMonoidal)
    (F : B ⥤ B') [F.Full] [F.Faithful] [F.EssSurj] (f : F.CoreMonoidal)
    (L : A ⥤ B) (R : B ⥤ A) (adj : L ⊣ R)
    (L' : A' ⥤ B') (R' : B' ⥤ A') (adj' : L' ⊣ R')
    (β : R ⋙ E ≅ F ⋙ R') (γ : L ⋙ F ≅ E ⋙ L')
    (hcompat : ∀ (X : A) (Y : B) (h : L.obj X ⟶ Y),
      E.map (adj.homEquiv X Y h) ≫ β.hom.app Y =
        adj'.homEquiv (E.obj X) (F.obj Y) (γ.inv.app X ≫ F.map h))
    [R'.LaxMonoidal] :
    ∃ r : R.LaxMonoidal,
      (e.εIso.hom ≫ E.map (@Functor.LaxMonoidal.ε B _ _ A _ _ R r) ≫
          β.hom.app (𝟙_ B) =
        Functor.LaxMonoidal.ε R' ≫ R'.map f.εIso.hom) ∧
      (∀ Y Z : B,
        (e.μIso (R.obj Y) (R.obj Z)).hom ≫
            E.map (@Functor.LaxMonoidal.μ B _ _ A _ _ R r Y Z) ≫ β.hom.app (Y ⊗ Z) =
          (β.hom.app Y ⊗ₘ β.hom.app Z) ≫
            Functor.LaxMonoidal.μ R' (F.obj Y) (F.obj Z) ≫ R'.map (f.μIso Y Z).hom) ∧
      (∀ s : R.LaxMonoidal,
        (e.εIso.hom ≫ E.map (@Functor.LaxMonoidal.ε B _ _ A _ _ R s) ≫
            β.hom.app (𝟙_ B) =
          Functor.LaxMonoidal.ε R' ≫ R'.map f.εIso.hom) →
        (∀ Y Z : B,
          (e.μIso (R.obj Y) (R.obj Z)).hom ≫
              E.map (@Functor.LaxMonoidal.μ B _ _ A _ _ R s Y Z) ≫ β.hom.app (Y ⊗ Z) =
            (β.hom.app Y ⊗ₘ β.hom.app Z) ≫
              Functor.LaxMonoidal.μ R' (F.obj Y) (F.obj Z) ≫ R'.map (f.μIso Y Z).hom) →
        s = r) ∧
      (∀ X Y : A,
        F.map ((@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).δ X Y) =
          γ.hom.app (X ⊗ Y) ≫ L'.map (e.μIso X Y).inv ≫
            adj'.leftAdjointOplaxMonoidal.δ (E.obj X) (E.obj Y) ≫
            (γ.inv.app X ⊗ₘ γ.inv.app Y) ≫ (f.μIso (L.obj X) (L.obj Y)).hom) ∧
      (F.map (@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).η =
        γ.hom.app (𝟙_ A) ≫ L'.map e.εIso.inv ≫
          adj'.leftAdjointOplaxMonoidal.η ≫ f.εIso.hom) ∧
      (((∀ U V : A', IsIso (adj'.leftAdjointOplaxMonoidal.δ U V)) ∧
          IsIso adj'.leftAdjointOplaxMonoidal.η) →
        (∀ X Y : A,
          IsIso ((@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).δ X Y)) ∧
        IsIso (@Adjunction.leftAdjointOplaxMonoidal A _ _ B _ _ L R adj r).η) := by
  let := e.toMonoidal
  let := f.toMonoidal
  let h : (R ⋙ E).LaxMonoidal := Functor.LaxMonoidal.transport β.symm
  let r : R.LaxMonoidal := liftLax E R
  have hε : e.εIso.hom ≫ E.map (ε R) ≫ β.hom.app (𝟙_ B) =
      ε R' ≫ R'.map f.εIso.hom := by
    change ε E ≫ E.map (E.preimage (η E ≫ ε (R ⋙ E))) ≫ _ = _
    simp [h, Functor.LaxMonoidal.transport_ε, comp_ε]
    rfl
  have hμ (Y Z : B) : (e.μIso (R.obj Y) (R.obj Z)).hom ≫ E.map (μ R Y Z) ≫
      β.hom.app (Y ⊗ Z) = (β.hom.app Y ⊗ₘ β.hom.app Z) ≫
        μ R' (F.obj Y) (F.obj Z) ≫ R'.map (f.μIso Y Z).hom := by
    change μ E _ _ ≫ E.map (E.preimage (δ E _ _ ≫ μ (R ⋙ E) Y Z)) ≫ _ = _
    simp [h, Functor.LaxMonoidal.transport_μ, comp_μ]
    rfl
  have hu (X : A) : E.map (adj.unit.app X) ≫ β.hom.app (L.obj X) =
      adj'.unit.app (E.obj X) ≫ R'.map (γ.inv.app X) := by
    simpa [Adjunction.homEquiv_unit] using hcompat X (L.obj X) (𝟙 _)
  have ht (X Y : A) : F.map (adj.leftAdjointOplaxMonoidal.δ X Y) =
      γ.hom.app (X ⊗ Y) ≫ L'.map (e.μIso X Y).inv ≫
        adj'.leftAdjointOplaxMonoidal.δ (E.obj X) (E.obj Y) ≫
          (γ.inv.app X ⊗ₘ γ.inv.app Y) ≫ (f.μIso (L.obj X) (L.obj Y)).hom := by
    apply (cancel_epi (γ.inv.app (X ⊗ Y))).mp
    simp only [Iso.inv_hom_id_app_assoc]
    apply (adj'.homEquiv _ _).injective
    rw [← hcompat]
    simp only [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.apply_symm_apply]
    rw [adj'.homEquiv_naturality_left, adj'.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [Functor.map_comp, map_tensor]
    simp only [Functor.map_comp, Category.assoc]
    change δ E X Y ≫ (E.map (adj.unit.app X) ⊗ₘ E.map (adj.unit.app Y)) ≫
      (e.μIso _ _).hom ≫ E.map (μ R _ _) ≫ _ = _
    dsimp only [Functor.comp_obj]
    rw [hμ (L.obj X) (L.obj Y), tensorHom_comp_tensorHom_assoc, hu, hu]
    rw [← tensorHom_comp_tensorHom_assoc]
    have hn := μ_natural R' (γ.inv.app X) (γ.inv.app Y)
    dsimp only [Functor.comp_obj] at hn
    rw [reassoc_of% hn]
    rfl
  have hη : F.map adj.leftAdjointOplaxMonoidal.η =
      γ.hom.app (𝟙_ A) ≫ L'.map e.εIso.inv ≫
        adj'.leftAdjointOplaxMonoidal.η ≫ f.εIso.hom := by
    apply (cancel_epi (γ.inv.app (𝟙_ A))).mp
    simp only [Iso.inv_hom_id_app_assoc]
    apply (adj'.homEquiv _ _).injective
    rw [← hcompat]
    simp only [Adjunction.leftAdjointOplaxMonoidal_η, Equiv.apply_symm_apply]
    rw [adj'.homEquiv_naturality_left, adj'.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [← cancel_epi e.εIso.hom]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hε
  refine ⟨r, hε, hμ, ?_, ?_, ?_, ?_⟩
  · intro s hsε hsμ
    apply Functor.LaxMonoidal.ext
    · apply E.map_injective
      apply (cancel_epi e.εIso.hom).mp
      apply (cancel_mono (β.hom.app (𝟙_ B))).mp
      simpa only [Category.assoc] using hsε.trans hε.symm
    · funext Y Z
      apply E.map_injective
      apply (cancel_epi (e.μIso (R.obj Y) (R.obj Z)).hom).mp
      apply (cancel_mono (β.hom.app (Y ⊗ Z))).mp
      simpa only [Category.assoc] using (hsμ Y Z).trans (hμ Y Z).symm
  · exact ht
  · exact hη
  · rintro ⟨hδ, hη'⟩
    constructor
    · intro X Y
      have := hδ (E.obj X) (E.obj Y)
      have : IsIso (F.map (adj.leftAdjointOplaxMonoidal.δ X Y)) := by
        rw [ht]
        infer_instance
      exact isIso_of_fully_faithful F _
    · have := hη'
      have : IsIso (F.map adj.leftAdjointOplaxMonoidal.η) := by
        rw [hη]
        infer_instance
      exact isIso_of_fully_faithful F _

end CategoryTheory
