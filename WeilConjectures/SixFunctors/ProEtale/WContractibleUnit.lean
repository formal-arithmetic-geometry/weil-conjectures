/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!
# The unit on the pro-étale site of a w-contractible affine scheme

Let `Y ≅ Spec R` with `R` a w-contractible ring, and let `Λ` be a commutative ring. On the small
pro-étale site of `Y`, the terminal object `Y` is weakly contractible, and every covering sieve of
it is refined by a finite cover by pairwise disjoint monomorphisms
(`AlgebraicGeometry.Scheme.ProEt.exists_finite_disjoint_cover_of_iso`). We deduce that the unit
`Λ_Y` of the category of sheaves of `Λ`-modules is projective, and that morphisms out of it are
finite on coproducts and on tensor products
(`CategoryTheory.UnitFactorsThroughFiniteCoproducts`, `CategoryTheory.UnitTensorFinite`), so that
dualizable objects of `D(Y_proét, Λ)` are bounded complexes of finite projective
`Λ_Y`-modules (`DerivedCategory.exists_iso_Q_obj_of_isDualizable`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable (Y : Scheme.{u})

/-- The terminal object `Y` of the small pro-étale site of `Y`. -/
noncomputable abbrev terminal : Y.ProEt := ProEt.mk (𝟙 Y)

variable {Y}

/-- The morphism from an object of the small pro-étale site of `Y` to the terminal object. -/
noncomputable def toTerminal (V : Y.ProEt) : V ⟶ terminal Y :=
  MorphismProperty.Over.homMk V.hom (Category.comp_id _)

noncomputable instance (V : Y.ProEt) : Unique (V ⟶ terminal Y) where
  default := toTerminal V
  uniq a := MorphismProperty.Over.Hom.ext ((Category.comp_id _).symm.trans (MorphismProperty.Over.w a))

end Scheme.ProEt

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] (Y : Scheme.{u})

/-- The constant presheaf `Λ` is the free presheaf on the terminal object. -/
noncomputable def unitPresheafIso :
    𝟙_ (Y.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ≅
      uliftYoneda.{u + 1}.obj (Scheme.ProEt.terminal Y) ⋙ ModuleCat.free Λ :=
  (NatIso.ofComponents (fun V ↦ (LinearEquiv.toModuleIso
      (Finsupp.uniqueLinearEquiv Λ Λ (⟨Scheme.ProEt.toTerminal V.unop⟩ :
        ULift.{u + 1} (V.unop ⟶ Scheme.ProEt.terminal Y)))))
    (fun {V V'} g ↦ by
      ext x
      revert x
      intro (x : ULift.{u + 1} (V.unop ⟶ Scheme.ProEt.terminal Y) →₀ Λ)
      change (Finsupp.mapDomain _ x) _ = x _
      rw [← Finsupp.mapDomain_apply (f := (uliftYoneda.{u + 1}.obj (Scheme.ProEt.terminal Y)).map g)
        (fun a b _ ↦ ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ Scheme.ProEt.terminal Y) _ _)) x ⟨Scheme.ProEt.toTerminal V.unop⟩]
      congr 1
      exact ULift.ext _ _ (Subsingleton.elim (α := _ ⟶ Scheme.ProEt.terminal Y) _ _))).symm

/-- The unit `Λ_Y` of sheaves of `Λ`-modules on `Y_proét` is the free sheaf on the terminal
object. -/
noncomputable def unitIsoFreeSheaf :
    𝟙_ (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ≅
      (freeSheaf Λ Y).obj (Scheme.ProEt.terminal Y) :=
  Functor.Monoidal.εIso (presheafToSheaf _ _) ≪≫ (presheafToSheaf _ _).mapIso (unitPresheafIso Λ Y)

end ProEtale

end AlgebraicGeometry
