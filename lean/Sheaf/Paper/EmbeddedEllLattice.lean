module

public import Sheaf.Paper.LatticeSheafBasic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-! # Embedded lattices defined by local denominators

Source: Bhatt--Scholze, Section 6.8, especially Proposition 6.8.4(6).
(blueprint: def-sfb-embedded-ell-lattice).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Opposite
namespace SheafOfModules

/-- An embedded ell-lattice is a locally finite free subsheaf containing, locally,
a power of ell times each ambient section. For an ambient module on which ell is
invertible, this says its localization is the ambient module. The covering-sieve
condition allows different denominators on different members of a cover.
Source: Bhatt--Scholze, Definition 6.8.3 and Proposition 6.8.4(6).
(blueprint: def-sfb-embedded-ell-lattice). -/
structure EmbeddedEllLattice {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [∀ T : C, HasWeakSheafify (J.over T) AddCommGrpCat.{w}]
    [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (ell : ℕ) (L : SheafOfModules.{w} R) where
  submodule : L.val.Submodule
  isSheaf : Presheaf.IsSheaf J submodule.toPresheafOfModules.presheaf
  locallyFree : (⟨submodule.toPresheafOfModules, isSheaf⟩ :
    SheafOfModules.{w} R).IsFiniteLocallyFree
  full : ∀ (T : C) (x : L.val.obj (op T)),
    ∃ s : Sieve T, s ∈ J T ∧ ∀ (V : C) (f : V ⟶ T), s f →
      ∃ n : ℕ, ell ^ n • L.val.map f.op x ∈ submodule.obj (op V)

end SheafOfModules
