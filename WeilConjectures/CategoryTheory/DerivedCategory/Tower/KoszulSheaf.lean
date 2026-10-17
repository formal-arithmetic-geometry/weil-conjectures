/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.KoszulReduction
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# Koszul completion and adic completion of sheaves of modules

Let `(C, J)` be an essentially small site (for instance the pro-étale site of a scheme), `Λ` a
commutative ring and `f = (f₁, …, f_r)` a sequence in `Λ`, `I = (f₁, …, f_r)`. This file
specializes the constructions of `WeilConjectures.CategoryTheory.DerivedCategory.Tower.Koszul`
and `…KoszulReduction` to `D(J, Λ) = D(Sheaf J (ModuleCat Λ))`, with the constant sheaf functor
`Λ-Mod ⥤ Sheaf J (ModuleCat Λ)` (exact, `Λ`-linear, monoidal, sending finite free modules to flat
sheaves):

* `DerivedCategory.sheafKoszulCompletion`: the intrinsic Koszul completion
  `K^{∧,Kos} = R lim_m (K ⊗ᴸ K(Λ; f^m))` with its map `κ_K`
  (Blueprint `def-weil-pbc-intrinsic-koszul-completion`);
* `DerivedCategory.sheafAdicCompletion`: `R lim_n (K ⊗ᴸ Λ ⧸ Iⁿ)` with the completion map
  `comp_K` (Blueprint `def-weil-pbc-completion-map`);
* `DerivedCategory.sheafKoszulToAdicCompletionIso`, for `Λ` Noetherian: the functorial
  isomorphism `c_K : K^{∧,Kos} ≅ R lim_n Kₙ` with `c_K ∘ κ_K = comp_K`
  (Blueprint `lemma-weil-pbc-koszul-quotient-limit`);
* `DerivedCategory.sheafAdicCompletionReductionIso`, for `Λ` Noetherian and `Λ ⧸ Iᵃ` perfect
  (dualizable in `D(J, Λ)`): the functorial isomorphism `(R lim_n Kₙ) ⊗ᴸ Pₐ ≅ Kₐ` induced by the
  projection to level `a` (Blueprint `lemma-weil-pbc-adic-completion-reduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {Λ : Type (u + 1)} [CommRing Λ] {r : ℕ} (f : Fin r → Λ)

instance : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} Λ)) :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} Λ)) :=
  comp_preservesFiniteColimits _ _

/-- The unit `𝟙 ≅ Λ` of the constant sheaf functor. -/
noncomputable abbrev sheafUnit :
    𝟙_ (Sheaf J (ModuleCat.{u + 1} Λ)) ⟶
      (constantSheaf J (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) :=
  Functor.LaxMonoidal.ε (constantSheaf J (ModuleCat.{u + 1} Λ))

instance : IsIso (sheafUnit J (Λ := Λ)) :=
  inferInstanceAs (IsIso (Functor.Monoidal.εIso _).hom)

/-- The constant sheaf on a finite free `Λ`-module is flat. -/
lemma flat_constantSheaf_obj (X : ModuleCat.{u + 1} Λ) [Module.Free Λ X] [Module.Finite Λ X] :
    ObjectProperty.flat ((constantSheaf J (ModuleCat.{u + 1} Λ)).obj X) :=
  GrothendieckTopology.flat_presheafToSheaf_obj _ J _ fun _ ↦
    (ObjectProperty.flat_iff_flat X).2 inferInstance

/-- **Blueprint `def-weil-pbc-intrinsic-koszul-completion`** (sheaves of `Λ`-modules). The
intrinsic Koszul completion `K^{∧,Kos} = R lim_m (K ⊗ᴸ K(Λ; f₁ᵐ, …, f_rᵐ))` on `D(J, Λ)`. -/
noncomputable abbrev sheafKoszulCompletion :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ)) ⥤ DerivedCategory (Sheaf J (ModuleCat Λ)) :=
  koszulCompletion (constantSheaf J (ModuleCat.{u + 1} Λ)) f

/-- **Blueprint `def-weil-pbc-intrinsic-koszul-completion`** (the map `κ_K`, sheaves of
`Λ`-modules). -/
noncomputable abbrev sheafKoszulCompletionMap :
    𝟭 _ ⟶ sheafKoszulCompletion J f :=
  koszulCompletionMap (constantSheaf J (ModuleCat.{u + 1} Λ)) (sheafUnit J) f

/-- The derived limit `R lim_n (K ⊗ᴸ Λ ⧸ Iⁿ)` on `D(J, Λ)`. -/
noncomputable abbrev sheafAdicCompletion (I : Ideal Λ) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} Λ)) ⥤ DerivedCategory (Sheaf J (ModuleCat Λ)) :=
  adicCompletion (constantSheaf J (ModuleCat.{u + 1} Λ)) I

/-- **Blueprint `def-weil-pbc-completion-map`** (sheaves of `Λ`-modules). The completion map
`comp_K : K ⟶ R lim_n (K ⊗ᴸ Λ ⧸ Iⁿ)`. -/
noncomputable abbrev sheafAdicCompletionMap (I : Ideal Λ) : 𝟭 _ ⟶ sheafAdicCompletion J I :=
  adicCompletionMap (constantSheaf J (ModuleCat.{u + 1} Λ)) (sheafUnit J) I

/-- **Blueprint `lemma-weil-pbc-koszul-quotient-limit`** (sheaves of `Λ`-modules, the
triangle): `c_K ∘ κ_K = comp_K`. -/
lemma sheafKoszulCompletionMap_comp_koszulToAdicCompletion :
    sheafKoszulCompletionMap J f ≫ koszulToAdicCompletion _ f =
      sheafAdicCompletionMap J (Ideal.span (Set.range f)) :=
  koszulCompletionMap_comp_koszulToAdicCompletion _ _ f

variable [IsNoetherianRing Λ]

/-- **Blueprint `lemma-weil-pbc-koszul-quotient-limit`** (sheaves of `Λ`-modules). For `Λ`
Noetherian, the functorial isomorphism `c_K : K^{∧,Kos} ≅ R lim_n (K ⊗ᴸ Λ ⧸ Iⁿ)`, with
`c_K ∘ κ_K = comp_K` (`DerivedCategory.sheafKoszulCompletionMap_comp_koszulToAdicCompletion`). -/
noncomputable def sheafKoszulToAdicCompletionIso :
    sheafKoszulCompletion J f ≅ sheafAdicCompletion J (Ideal.span (Set.range f)) :=
  koszulToAdicCompletionIso _ f

variable (a : ℕ)
  [HasLeftDual (Q.obj (quotComplex (constantSheaf J (ModuleCat.{u + 1} Λ)) f a))]

/-- **Blueprint `lemma-weil-pbc-adic-completion-reduction`** (sheaves of `Λ`-modules). For `Λ`
Noetherian and `Pₐ = Λ ⧸ Iᵃ` perfect (dualizable in `D(J, Λ)`), projection to level `a` induces a
functorial isomorphism `(R lim_n Kₙ) ⊗ᴸ Pₐ ≅ Kₐ = K ⊗ᴸ Pₐ`. -/
noncomputable def sheafAdicCompletionReductionIso :
    sheafAdicCompletion J (Ideal.span (Set.range f)) ⋙
        (curriedTensor _).flip.obj
          (Q.obj (quotComplex (constantSheaf J (ModuleCat.{u + 1} Λ)) f a)) ≅
      (curriedTensor _).flip.obj
        (Q.obj (quotComplex (constantSheaf J (ModuleCat.{u + 1} Λ)) f a)) :=
  adicCompletionReductionIso _ (sheafUnit J) f a (flat_constantSheaf_obj J)

end DerivedCategory
