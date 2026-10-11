module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.CategoryTheory.SiteCechComplex

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-! # Injective modules are Čech-acyclic on open covers

Source: literature/stacks-project/cohomology.tex, Lemma 01EP.
(blueprint: lem-weil-pbc-module-injective-open-cover-cech-acyclic)
-/

/-- An injective sheaf of `𝒪_X`-modules has vanishing positive Čech cohomology for
any open covering of any open subscheme.

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EP.
(blueprint: lem-weil-pbc-module-injective-open-cover-cech-acyclic)
-/
theorem module_injective_open_cover_cech_acyclic {X : Scheme.{u}}
    (I : X.Modules) [Injective I] (U : X.Opens) (ι : Type w)
    (V : ι → X.Opens) (hV : ∀ i, V i ≤ U) (hcover : ⨆ i, V i = U)
    (S : CategoryTheory.SiteCechComplex V (fun i => homOfLE (hV i))) :
    ∀ p : ℕ, 0 < p →
      IsZero ((S.cohomologyFunctor p).obj
        (((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
            isTerminalTop.op).obj
          ((SheafOfModules.forget X.ringCatSheaf).obj I)) ⋙
            (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
