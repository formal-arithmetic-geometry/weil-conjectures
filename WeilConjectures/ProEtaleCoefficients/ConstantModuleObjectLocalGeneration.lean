/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

public import WeilConjectures.ProEtaleCoefficients.LocalGenerationDefinitions
import WeilConjectures.ProEtaleCoefficients.LocalGenerationTransportEpi
import WeilConjectures.ProEtaleCoefficients.LocalGenerationSectionsOfEpi

/-! # Local generators from an internal constant-module epimorphism

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/prop-sfb-bounded-constructible-triangulated.proof.md,
Kernels paragraph, lines 41--50.
(blueprint: lem-sfb-constant-module-object-local-generation)

The hypothesis is a finite-free epimorphism in the category of internal modules over
the twice-pulled-back constant ring object. The conclusion concerns the restriction
of the sectionwise constant module sheaf to the slice over the composite pro-etale object.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite-free epimorphism onto the twice-pulled-back internal constant module produces
n sections of the sectionwise constant module over W whose induced free-sheaf map is epi.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/prop-sfb-bounded-constructible-triangulated.proof.md,
Kernels paragraph, lines 41--50.
(blueprint: lem-sfb-constant-module-object-local-generation)

Proof:
1. The monoidal pullback-composition comparison identifies f^* g^* with (f ≫ g)^*.
The pro-etale-object localization comparison identifies this inverse image with restriction
to Y_proet/W, compatibly with tensor, units, regular modules and finite biproducts.
2. The internal constant ring and module are sheafifications of the constant presheaf
multiplication and scalar action. The internal-to-sectionwise module equivalence therefore
identifies them with the constant ring sheaf and siteConstantModuleFunctorGeneral, preserving
underlying sections and restriction maps. Apply these identifications after step 1.
3. Equivalences preserve epimorphisms. Thus p gives an epimorphism from the rank-n free
sectionwise module sheaf to localGenerationRestrictedModule. Its basis images give a family
of global sections of the slice. Evaluation at its terminal object is evaluation at W → Y.
4. The freeHomEquiv universal property identifies the map determined by those global sections
with the transported epimorphism. Hence it is epi, and their values at the terminal object
are the required n sections over W. For n = 0 the free object is zero, so the same conclusion
asserts an epimorphism from zero, as required.
-/
theorem constantModuleObjectLocalGeneration
    {Y Z W : Scheme.{u}} (g : Z ⟶ Y) (f : W ⟶ Z)
    [WeaklyEtale f] [WeaklyEtale (f ≫ g)]
    (B : Type (u + 1)) [CommRing B]
    (P : Type (u + 1)) [AddCommGroup P] [Module B P]
    (n : ℕ)
    (p : Mod.finiteFree
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))) n ⟶
      ((upperStar AddCommGrpCat.{u + 1} f).mapMod
        ((upperStar AddCommGrpCat.{u + 1} g).obj
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B))).obj
        (((upperStar AddCommGrpCat.{u + 1} g).mapMod
          (Sheaf.constRingSheaf (Scheme.ProEt.topology Y) B)).obj
            (localGenerationConstantModule Y B P))) [Epi p] :
    ∃ s : Fin n →
        ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology Y) B).obj
          (ModuleCat.of B P)).val.obj (op (Scheme.ProEt.mk (f ≫ g))),
      ∃ t : ULift.{u + 1} (Fin n) →
          (localGenerationRestrictedModule Y (Scheme.ProEt.mk (f ≫ g)) B P).sections,
        Epi ((SheafOfModules.freeHomEquiv
          (localGenerationRestrictedModule Y (Scheme.ProEt.mk (f ≫ g)) B P)).symm t) ∧
        ∀ i : Fin n,
          (t (ULift.up i)).val (op (Over.mk (𝟙 (Scheme.ProEt.mk (f ≫ g))))) = s i  := by
  obtain ⟨q, hq⟩ := localGenerationTransportEpi g f B P n p
  have : Epi q := hq
  obtain ⟨t, ht⟩ := localGenerationSectionsOfEpi
    (Y := Y) (Scheme.ProEt.mk (f ≫ g)) B P n q
  refine ⟨fun i ↦ (t (ULift.up i)).val
      (op (Over.mk (𝟙 (Scheme.ProEt.mk (f ≫ g))))), t, ht, ?_⟩
  intro i
  rfl

end AlgebraicGeometry.ProEtale
