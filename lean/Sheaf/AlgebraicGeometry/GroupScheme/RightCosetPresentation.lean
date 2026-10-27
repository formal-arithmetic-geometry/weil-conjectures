/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # RightCosetPresentation

Source: Kaneda, On the Frobenius morphism of flag schemes (1994), Section 2.3,
printed pp.320--321; Milne, Algebraic Groups (2017), Sections 4a and 5f.
(blueprint: def-sfb-right-coset-sheaf-presentation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj TensorProduct
namespace AlgebraicGeometry.FrobeniusBorelInduction

/-- The right-coset sheafification presentation, allowing a quotient scheme which is
not a group. Local surjectivity and the torsor isomorphism retain the quotient map;
the last clause is the actual universal property among all fppf sheaves of sets.
This uses the usual presheaf coequalizer, not a quotient of field-valued points.
Source: Kaneda, Section 2.3, p.320 and Section 2.5, p.322; Milne, 5.24--5.28.
(blueprint: def-sfb-right-coset-sheaf-presentation) -/
def IsRightCosetPresentation {F : Type u} [Field F]
    {G H : Grp (Over (Spec (.of F)))} (i : H ⟶ G)
    {Q : Over (Spec (.of F))} (π : G.X ⟶ Q) : Prop :=
  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.map π) ∧
  Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q) ∧
  (∃ e : G.X ⊗ H.X ≅ pullback π π,
    e.hom ≫ pullback.fst _ _ = fst G.X H.X ∧
    e.hom ≫ pullback.snd _ _ = fst G.X H.X * (snd G.X H.X ≫ i.hom.hom)) ∧
  ∃ ηπ : coequalizer (yoneda.map (fst G.X H.X))
      (yoneda.map (fst G.X H.X * (snd G.X H.X ≫ i.hom.hom))) ⟶ yoneda.obj Q,
    coequalizer.π _ _ ≫ ηπ = yoneda.map π ∧
    ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηπ ≫ f)

end AlgebraicGeometry.FrobeniusBorelInduction
