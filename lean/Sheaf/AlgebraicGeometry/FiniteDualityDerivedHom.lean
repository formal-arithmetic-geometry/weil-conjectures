module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence
import Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint

/-!
# Finite Grothendieck duality as derived internal Hom

Source: literature/stacks-project/duality.tex, Tags 0AX2 and 0AX3
(blueprint: lem-sc-finite-duality-derived-hom).
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: literature/stacks-project/duality.tex, Tags 0AX2 and 0AX3
(blueprint: lem-sc-finite-duality-derived-hom).

Let `f : X ⟶ Y` be finite with `X`, `Y` Noetherian, `A = f_* O_X`, and `K ∈ D^+_QCoh(Y)`.
The right adjoint `f^! = a` of `Rf_*` on `D_QCoh` is given as in
`finiteTwistedInverse_boundedBelow` (`R`, `comparison`, `a`, `adj`). Restriction of scalars
`ρ : D(A) ⥤ D(O_Y)` along `O_Y → A` has the specified right adjoint `ρR` (`adjA`).

The conclusion: there are the identification `ι : R𝓗om(O_Y, -) ≅ 𝟭` (natural; any two
choices differ by an automorphism of `𝟭`, absorbed by `φ` and `d`), the identification
`c : ρ ∘ Rg_* ≅ Rf_*` for `g : (X, O_X) → (Y, A)`, an isomorphism `φ : Rg_* (f^! K) ≅ ρR K`
in `D(A)` (the `A`-linear structure) and `d : ρ (ρR K) ≅ R𝓗om_{O_Y}(A, K)` such that
1. the counit of `ρ ⊣ ρR` at `K` is, through `d`, evaluation at the unit section
   `1 ∈ A` (`R𝓗om(O_Y → A, K)` followed by `ι`), and
2. through `c` and `ρ φ`, the counit of `ρ ⊣ ρR` is the counit of `Rf_* ⊣ f^!` at `K`.
So `c⁻¹ ≫ ρ φ ≫ d : Rf_* f^! K ≅ R𝓗om_{O_Y}(A, K)` is `A`-linear and carries the counit of
`Rf_* ⊣ f^!` to evaluation at `1`.

Proof sketch: finite affine duality (`lem-sc-finite-sheafhom-affine-adjoint`), the
equivalence `D_QCoh(X) ≃ D_QCoh(A)` (`lem-sc-finite-affine-derived-equivalence`),
bounded-below preservation (`lem-sc-finite-pushforward-derived-hom-qcoherent`) and
uniqueness of right adjoints.
-/
theorem finite_duality_derived_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : R ⊣ a)
    (ρR : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
    (adjA : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace f))
      ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ ρR)
    (K : schemeDerivedQCohCategory Y) (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ ι : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
    ∃ c : RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ≅
        schemeDerivedDirectImage f,
    ∃ φ : (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)).obj
        (a.obj K).obj ≅ ρR.obj K.obj,
    ∃ d : (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.obj
          (ρR.obj K.obj) ≅
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
            K.obj),
    d.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op, 𝟙 K.obj) ≫
        ι.hom.app K.obj = adjA.counit.app K.obj ∧
      (c.app (a.obj K).obj).inv ≫
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor.map
            φ.hom ≫ adjA.counit.app K.obj =
        comparison.inv.app (a.obj K) ≫ (adj.counit.app K).hom := by
  sorry

end AlgebraicGeometry
