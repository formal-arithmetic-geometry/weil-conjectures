module

public import Sheaf.Paper.AmbientPullbackTensorData

/-! Ordinary pullback associativity and unit laws.

Source: Stacks 03CB, 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-composition-laws).

This is the ordinary part of the ambient pullback coherence argument.  The
section-normalized direct-image comparison is pasted over the canonical
fibre-product comparisons; adjunction mates then give the three displayed
identities.  The proof is split from the derived localization step so that the
ordinary and derived calculations can be completed independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Ordinary associativity and unit laws for the ambient pullback comparisons.
Source: Stacks 03CB, 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-composition-laws).
Proof: paste the section-normalized direct-image comparisons over the canonical
fibre-product associativity and identity comparisons, then take their specified
adjunction mates.  The three component equations are exactly the associativity,
right-unit and left-unit clauses below. -/
theorem ordinary_pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    (∀ {W X Y Z : Scheme.{t}} (w : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
      (aW : W ⟶ K) (aX : X ⟶ K) (aY : Y ⟶ K) (aZ : Z ⟶ K)
      [LocallyOfFiniteType aW] [QuasiCompact aW] [LocallyOfFiniteType aX]
      [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [LocallyOfFiniteType aZ] [QuasiCompact aZ]
      (_hw : w ≫ aX = aW) (_hf : f ≫ aY = aX) (_hg : g ≫ aZ = aY)
      (M : Modules ell E Z s),
      (pull ell E w s).map ((comp ell E f g s).hom.app M) ≫
          (comp ell E w (f ≫ g) s).hom.app M =
        (comp ell E w f s).hom.app ((pull ell E g s).obj M) ≫
          (comp ell E (w ≫ f) g s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.assoc w f g))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (pull ell E f s).map ((identity ell E Y s).hom.app M) =
        (comp ell E f (𝟙 Y) s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.comp_id f))) ∧
    (∀ {X Y : Scheme.{t}} (f : X ⟶ Y) (aX : X ⟶ K) (aY : Y ⟶ K)
      [LocallyOfFiniteType aX] [QuasiCompact aX]
      [LocallyOfFiniteType aY] [QuasiCompact aY]
      (_hf : f ≫ aY = aX) (M : Modules ell E Y s),
      (identity ell E X s).hom.app ((pull ell E f s).obj M) =
        (comp ell E (𝟙 X) f s).hom.app M ≫
          eqToHom (congrArg (fun a ↦ (pull ell E a s).obj M)
            (Category.id_comp f))) := by
  sorry

end WeilConjectures.AmbientPullbackTensor
