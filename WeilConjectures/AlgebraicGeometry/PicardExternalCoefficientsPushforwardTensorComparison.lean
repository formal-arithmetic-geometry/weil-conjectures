/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.ExternalConstantSectionsTensorMap
import WeilConjectures.AlgebraicGeometry.ExternalSectionsOpenComparison
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsTensorAffineRight
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine comparison with the constant global-sections tensor presheaf

## References

* Stacks Project, Varieties, Tag 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false

/-- Without choosing a basis, the external direct image is isomorphic, on affine opens, to the
tensor presheaf of the global sections of `F` with `G` (Stacks, Tag 0BED). -/
theorem exists_external_constant_sections_tensor_comparison
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Nonempty ((PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj).obj
        (picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G) ≅
      (PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj).obj
        ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
          (externalCupCoefficients f g F G)).val)  := by
  classical
  let φ := externalConstantSectionsTensorMap k X Y f g F G
  have hφ := externalConstantSectionsTensorMap_app_bijective_iff k X Y f g F G
  let A := (PresheafOfModules.pushforward₀
    (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj)
  have hb (V : Y.Opens) (hV : IsAffineOpen V) :
      Function.Bijective (externalSectionsComponent f g F G V) := by
    let : IsAffine V.toScheme := hV
    let : (G.restrict V.ι).IsQuasicoherent := isQuasicoherent_restrictFunctor V.ι G
    obtain ⟨eS, eT, he⟩ := externalSectionsComponent_openComparison f g F G V
    have ht := externalGlobalSectionsTensor_bijective_of_isAffine_right
      k X V.toScheme f (V.ι ≫ g) F (G.restrict V.ι)
    have hh : Function.Bijective (externalSectionsComponent f g F G V ≫ eT.hom) := by
      rw [he]
      exact ht.comp eS.toLinearEquiv.bijective
    exact (eT.toLinearEquiv.bijective.of_comp_iff'
      (externalSectionsComponent f g F G V)).mp hh
  have hi (V : (ObjectProperty.FullSubcategory
      (fun V : Y.Opens ↦ IsAffineOpen V))ᵒᵖ) :
      IsIso ((A.map φ).app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (hφ V.unop.obj).mpr (hb V.unop.obj V.unop.property)
  let := hi
  exact ⟨PresheafOfModules.isoMk (fun V ↦ asIso ((A.map φ).app V))
    (by intro U V i; exact (A.map φ).naturality i)⟩

end AlgebraicGeometry.Scheme.Modules
