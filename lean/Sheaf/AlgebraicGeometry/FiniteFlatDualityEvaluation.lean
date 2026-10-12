/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AffineDerivedConcentration
import Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeDerivedHom
import Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree

/-! # Finite flat duality with an invertible target

Source: Stacks Project, Duality for Schemes, Tag 0AX2, Remark 0AX3, and
Discriminants and Differents, Tags 0BVI and 0FKW
(blueprint: lem-sc-finite-flat-duality-evaluation).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Finite flat duality identifies the right-adjoint image of an invertible module with
an internal Hom sheaf.  The counit is evaluation at the unit, and the resulting
module action satisfies the displayed evaluation formula. The adjunction is on
`D_QCoh`, as in the source; `R` and `comparison` specify the restriction of `Rf_*`.
`K` and `eL` represent `L` in that full subcategory. All claimed sheaves, isomorphisms,
and evaluation identities are conclusions. The derived comparison `c` is pinned to
the right-derived unit, so the counit cannot be changed by an arbitrary comparison.
The action uses actual sections of `O_X` on inverse-image opens, with actual `1`.
Linearity and evaluation at `1` determine the Hom isomorphism uniquely once `e₀`
is fixed: its value at `a` must be `ε(a • ω)`.

Source: Stacks Project, Tags 0AX2, 0AX3, 0BVI and 0FKW
(blueprint: lem-sc-finite-flat-duality-evaluation).

Proof:
1. Finite duality identifies the right adjoint image after pushforward with derived
internal Hom, compatibly with the `f_* O_X`-module structure and the counit
(lem-sc-finite-duality-derived-hom, Tags 0AX2 and 0AX3).
2. Finite flatness makes `f_* O_X` finite locally free, so the derived internal Hom
is concentrated in degree zero and is the ordinary internal Hom sheaf. Use
lem-weil-pbc-finite-type-noetherian-finite-presentation for finite presentation,
lem-sc-finite-pushforward-locally-free for local freeness, and
lem-sc-finite-locally-free-derived-hom for the degree-zero identification.
3. Affineness of a finite morphism identifies the right-adjoint object itself with
its degree-zero sheaf (lem-sc-affine-derived-concentration). This sheaf is
quasi-coherent, so affine pushforward has no higher cohomology; its canonical
right-derived unit gives `c`. The counit becomes evaluation at `1`.
4. For the precomposition action, `(a • Phi(omega))(1) = Phi(omega)(a * 1)`.
Linearity identifies the left side with `Phi(a • omega)(1)`, while `a * 1 = a`.
This gives `Phi(omega)(a) = Phi(a omega)(1)` on every open.
-/
theorem finiteFlatDualityEvaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [IsFinite f] [Flat f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : Y.Modules) [L.IsInvertible]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (K : schemeDerivedQCohCategory Y)
    (eL : K.obj ≅ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) :
    ∃ (M : X.Modules),
    ∃ (e₀ : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M ≅ (a.obj K).obj),
    ∃ (c : (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward f).obj M) ≅
      (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)),
      c.hom = DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).inv.app M) ≫
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ∧
    ∃ (e : (Scheme.Modules.pushforward f).obj M ≅
      SheafOfModules.homObj (R := Y.toRingedSpace.sheaf)
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) L),
    ∃ (ε : (Scheme.Modules.pushforward f).obj M ⟶ L),
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map ε =
        c.hom ≫ (schemeDerivedDirectImage f).map e₀.hom ≫
          comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom ≫ eL.hom ∧
      (∀ (U : Y.Opens)
        (ω : ((Scheme.Modules.pushforward f).obj M).presheaf.obj (Opposite.op U)),
        ε.app U ω =
          (PresheafOfModules.homObjEvalId
            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
            L.val U ((Scheme.Modules.Hom.app e.hom U) ω))
              (1 : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))) ∧
      (∀ (U : Y.Opens) (a₁ b : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))
        (ω : M.val.obj (Opposite.op (f ⁻¹ᵁ U))),
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) (a₁ • ω))) b =
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) ω)) (a₁ * b)) ∧
      (∀ (U : Y.Opens) (a₁ : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))
        (ω : M.val.obj (Opposite.op (f ⁻¹ᵁ U))),
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) ω)) a₁ =
        (PresheafOfModules.homObjEvalId
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
          L.val U ((Scheme.Modules.Hom.app e.hom U) (a₁ • ω)))
            (1 : X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)))) := by
  sorry

end AlgebraicGeometry
