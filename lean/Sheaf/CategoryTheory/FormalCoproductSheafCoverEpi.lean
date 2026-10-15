/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.FormalCoproductSheafRealization
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Componentwise covers give epimorphisms of realized formal families

Source: Stacks Project, Hypercoverings, Tags 01G3 and 0DB1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FormalCoproduct

private theorem yoneda_hom_ext_of_cover {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.toGrothendieck.Subcanonical]
    {X : C} {Z : Sheaf J.toGrothendieck (Type u)}
    (g h : J.toGrothendieck.yoneda.obj X ⟶ Z)
    {I : Type u} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Presieve.ofArrows U f ∈ J X)
    (heq : ∀ i, J.toGrothendieck.yoneda.map (f i) ≫ g =
      J.toGrothendieck.yoneda.map (f i) ≫ h) : g = h := by
  apply J.toGrothendieck.yonedaEquiv.injective
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp Z.property
    |>.isSheafFor_of_mem_precoverage hf).isSeparatedFor.ext
  rintro V k ⟨i⟩
  simpa only [J.toGrothendieck.yonedaEquiv_naturality] using
    congrArg J.toGrothendieck.yonedaEquiv (heq i)

/-- Componentwise covering morphisms induce epimorphisms after sheaf realization.
Source: Stacks Project, Hypercoverings, Tags 01G3 and 0DB1.

Proof: test cancellation on each representable summand of the target. The covering
hypothesis and separatedness of the testing sheaf reduce equality there to equality on
all summands mapping to that component. These equalities follow by precomposing the
assumed equality with the corresponding source coproduct inclusions. Empty covering
families are allowed: separatedness gives the same conclusion in this case.
(blueprint: lem-weil-pbc-formal-coproduct-sheaf-cover-epi). -/
theorem sheafRealization_map_epi {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.toGrothendieck.Subcanonical] {T : C}
    {X Y : FormalCoproduct.{u} (Over T)} (f : X ⟶ Y)
    (hf : ∀ j : Y.I,
      Presieve.ofArrows
        (fun i : {i : X.I // f.f i = j} ↦ (X.obj i.val).left)
        (fun i ↦ (f.φ i.val ≫ eqToHom (congrArg Y.obj i.property)).left) ∈
          J (Y.obj j).left) :
    Epi ((sheafRealization J.toGrothendieck T).map f) := by
  constructor
  intro Z g h hgh
  apply Sigma.hom_ext
  intro j
  apply (Over.forget (J.toGrothendieck.yoneda.obj T)).map_injective
  apply yoneda_hom_ext_of_cover J _ _ _ _ (hf j)
  intro i
  obtain ⟨i, hi⟩ := i
  dsimp at hi ⊢
  subst j
  have hh := congrArg (fun k ↦
    Sigma.ι (fun i : X.I ↦ (Over.post J.toGrothendieck.yoneda).obj (X.obj i)) i ≫ k) hgh
  have hh' := congrArg (fun k ↦ (Over.forget _).map k) hh
  simpa [sheafRealization, eval, Category.assoc, ← Functor.map_comp,
    Function.comp_def, Over.post] using hh'

end CategoryTheory.Limits.FormalCoproduct
