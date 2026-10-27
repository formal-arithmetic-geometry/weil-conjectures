/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q93
-/
module

public import Sheaf.AlgebraicGeometry.AdicPrincipalChartData
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.RingTheory.FiniteModuleComplete
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Coherent modules on a Noetherian formal affine

Source: Stacks Project, Tag 0AHY; EGA I, 10.10.2 and 10.10.5, recalled in
EGA III.1, Proposition 4.8.8 and Scholie 5.1.7.
(blueprint: lem-per-noetherian-formal-affine-coherent-modules)

The equivalence is specified by limiting residue cones on the principal basis, including
restriction and morphism compatibility. Thus its forward functor is the completed associated
sheaf, not an unspecified equivalence with the same source and target. No object is chosen
from this existence theorem. All auxiliary constructions below use existing module quotients,
the associated-sheaf functor, and evaluation or restriction of scalars.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Forget an O-module on Spf to a sheaf of R-modules via the canonical map on global sections.
Source: Stacks Tag 0AHY (blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicFormalModulesToSheaf (R : CommRingCat.{u}) (K : Ideal R) :
    SheafOfModules.{u} (moduleRings (adicFormalSpec R K)) ⥤
      TopCat.Sheaf (ModuleCat.{u} R) (adicFormalSpec R K) :=
  SheafOfModules.forgetToSheafModuleCat (moduleRings (adicFormalSpec R K)) (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
      sheafCompose _ (ModuleCat.restrictScalars (adicFormalGlobalSection R K))

/-- Sections on a formal open, with the canonical R-action.
Source: Stacks Tag 0AHY (blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicFormalModuleSections (R : CommRingCat.{u}) (K : Ideal R)
    (U : Opens (adicFormalSpec R K)) :
    SheafOfModules.{u} (moduleRings (adicFormalSpec R K)) ⥤ ModuleCat.{u} R :=
  adicFormalModulesToSheaf R K ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op U)

/-- Ordinary module pullback along the canonical map from Spf to Spec. For finite modules,
its value on tilde M is the completed associated sheaf, by finite presentations.
Source: EGA I, 10.10.2 (blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicFormalModulePullback (R : CommRingCat.{u}) (K : Ideal R) :
    (Spec R).Modules ⥤ SheafOfModules.{u} (moduleRings (adicFormalSpec R K)) :=
  SheafOfModules.pullback (F := Opens.map (adicFormalSpecToSpec R K).hom.base)
    (R := moduleRings (adicFormalSpec R K)) (S := (Spec R).ringCatSheaf)
    ⟨Functor.whiskerRight (adicFormalSpecToSpec R K).hom.c (forget₂ CommRingCat RingCat)⟩

/-- The positive quotient tower: index n denotes M/K^(n+1)M, with quotient transitions.
Source: Stacks Tag 0AHY (blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicModuleQuotientTower (R : CommRingCat.{u}) (K : Ideal R) (M : ModuleCat.{u} R) :
    ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  Functor.ofOpSequence
    (X := fun n ↦ ModuleCat.of R (M ⧸ (K ^ (n + 1) • (⊤ : Submodule R M))))
    (fun n ↦ ModuleCat.ofHom (AdicCompletion.transitionMap K M (Nat.le_succ (n + 1))))

/-- The quotient-associated sheaves, regarded on Spec R by their canonical closed pushforward.
Each is supported on V(K), so restriction to the common space gives the sheaves in the node.
Source: Stacks Tags 01HV and 0AHY
(blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicModuleQuotientSheaves (R : CommRingCat.{u}) (K : Ideal R) (M : ModuleCat.{u} R) :
    ℕᵒᵖ ⥤ TopCat.Sheaf (ModuleCat.{u} R) (Spec R) :=
  adicModuleQuotientTower R K M ⋙ tilde.functor R ⋙ modulesSpecToSheaf

/-- On D(s) this is the tower of localizations (M/K^(n+1)M)_s, by the tilde section theorem.
Source: Stacks Tags 01HV and 0AHY
(blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicModuleQuotientSections (R : CommRingCat.{u}) (K : Ideal R)
    (M : ModuleCat.{u} R) (s : R) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  adicModuleQuotientSheaves R K M ⋙ TopCat.Sheaf.forget _ _ ⋙
    (evaluation _ _).obj (op (PrimeSpectrum.basicOpen s))

/-- A section from an original module element, restricted from the global unit comparison.
Source: EGA I, 10.10.2 (blueprint: lem-per-noetherian-formal-affine-coherent-modules). -/
def adicFormalModuleUnitSection (R : CommRingCat.{u}) (K : Ideal R)
    (F : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ⥤
      SheafOfModules.{u} (moduleRings (adicFormalSpec R K)))
    (η : ObjectProperty.ι (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ≅
      F ⋙ adicFormalModuleSections R K ⊤)
    (M : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} R ↦ Module.Finite R M))
    (U : Opens (adicFormalSpec R K)) (m : M.obj) : (F.obj M).val.obj (op U) :=
  (F.obj M).val.map (homOfLE le_top).op (η.hom.app M m)

/-- Finite modules and coherent modules on a complete Noetherian formal affine correspond
exactly, with the completed-associated-sheaf functor and the global-section quasi-inverse.
Source: Stacks Tag 0AHY; EGA I, 10.10.2 and 10.10.5, as recalled in EGA III.1,
Proposition 4.8.8 and Scholie 5.1.7.
(blueprint: lem-per-noetherian-formal-affine-coherent-modules).

Proof (the eleven steps of the node):
1. Limits of sheaves are sectionwise (def-pur-sheaf-inverse-limit). On D(s) the tilde
   section theorem (lem-weil-pbc-spec-module-tilde-sections) identifies the quotient
   sections with localized quotients, compatibly with restrictions and module maps.
2. Localize a short exact sequence of finite modules: localization is flat, and preserves
   Noetherianity and finite generation. Exactness of finite-module completion gives
   exactness on the principal basis, hence exactness of the completed sheaves.
3. The principal-chart theorem identifies sections with C_s tensor_R M, where C_s is
   the completed localization. Completion/tensor comparison and the quotient projections
   identify its quotients with the localized quotients, including their transitions.
4. Apply exactness to K^n M -> M -> M/K^n M. Finite generators of K^n identify the image
   sheaf with K^n M-triangle. Its cokernel is the ordinary quotient-associated sheaf.
5. On each principal chart, a map from a finite free sheaf to O is a finite matrix over
   C_s. Its algebraic kernel is finite by Noetherianity. Step 2 identifies its associated
   sheaf with the sheaf kernel, proving coherence of O on all open neighbourhoods.
6. A finite module has a finite presentation. Steps 2 and 5 and closure of coherence under
   finite sums and cokernels prove coherence of its completed associated sheaf.
7. An arbitrary coherent sheaf has, locally on principal charts, a finite presentation.
   Its matrix is a matrix over C_s. Step 2 identifies its cokernel with P-triangle.
8. Step 4 identifies the successive quotients with coherent sheaves on Spec(R/K^n).
   Locally these are precisely the quotient-associated sheaves; their transitions agree.
9. Reconstruction from quotients (Stacks 087T) and the affine quotient-system equivalence
   (lem-weil-pbc-coherent-formal-modules-affine, 087W) give essential surjectivity, since
   the completed coefficient ring is R. The local residue comparisons glue.
10. Finite modules over complete Noetherian rings are complete. Thus the compatible-residue
    map M -> Gamma(M-triangle) is bijective. Maps are determined by these global generators;
    compatible quotient maps reconstruct them, proving full faithfulness and naturality.
11. Present M by finite free modules. Ordinary sheaf tensor preserves cokernels, and tensor
    of modules is right exact. The same matrix presents both sides of the tensor comparison.
    On pure tensors the map multiplies coefficients; this also proves the unit formula.

The first comparison η is the unit on underlying R-modules, as its displayed factorization
through E.unitIso and γ records. Each p is a limiting residue cone, so its target section
module is precisely the inverse limit of the localized quotient modules. The last two
clauses fix restriction and morphism maps on every residue coordinate. The tensor product
below is the existing sheafified sectionwise tensor, not an additional tensor construction. -/
theorem noetherianFormalAffine_coherentModules (R : CommRingCat.{u})
    [IsNoetherianRing R] (K : Ideal R) (_hK : K.FG) [IsAdicComplete K R] :
    ∃ E : ObjectProperty.FullSubcategory (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ≌
        ObjectProperty.FullSubcategory (RingedSpace.IsCoherent (adicFormalSpec R K)),
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
      Nonempty (E.functor ⋙ ObjectProperty.ι (RingedSpace.IsCoherent (adicFormalSpec R K)) ≅
        ObjectProperty.ι (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ⋙
          tilde.functor R ⋙ adicFormalModulePullback R K) ∧
      ∃ (η : ObjectProperty.ι (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ≅
          E.functor ⋙ ObjectProperty.ι (RingedSpace.IsCoherent (adicFormalSpec R K)) ⋙
            adicFormalModuleSections R K ⊤)
        (γ : E.inverse ⋙ ObjectProperty.ι (fun M : ModuleCat.{u} R ↦ Module.Finite R M) ≅
          ObjectProperty.ι (RingedSpace.IsCoherent (adicFormalSpec R K)) ⋙
            adicFormalModuleSections R K ⊤),
        (∀ M, η.hom.app M = (E.unitIso.hom.app M).hom ≫ γ.hom.app (E.functor.obj M)) ∧
        (∃ e : (E.functor.obj ⟨ModuleCat.of R R, inferInstance⟩).obj ≅
            SheafOfModules.unit (moduleRings (adicFormalSpec R K)),
          ∀ r : R, e.hom.val.app (op ⊤)
              (η.hom.app ⟨ModuleCat.of R R, inferInstance⟩ r) =
            adicFormalGlobalSection R K r) ∧
        (∀ (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N],
          ∃ μ : (SheafOfModules.siteSheafTensorRight
                (E.functor.obj ⟨N, inferInstance⟩).obj).obj
                  (E.functor.obj ⟨M, inferInstance⟩).obj ≅
              (E.functor.obj ⟨ModuleCat.of R (M ⊗[R] N), inferInstance⟩).obj,
            ∀ (U : Opens (adicFormalSpec R K)) (m : M) (n : N),
              μ.hom.val.app (op U)
                (SheafOfModules.siteSheafTensorTmul _ _ (op U)
                  (adicFormalModuleUnitSection R K
                  (E.functor ⋙ ObjectProperty.ι _) η ⟨M, inferInstance⟩ U m)
                  (adicFormalModuleUnitSection R K
                  (E.functor ⋙ ObjectProperty.ι _) η ⟨N, inferInstance⟩ U n)) =
                adicFormalModuleUnitSection R K
                  (E.functor ⋙ ObjectProperty.ι _) η
                  ⟨ModuleCat.of R (M ⊗[R] N), inferInstance⟩ U (m ⊗ₜ[R] n)) ∧
        ∃ p : ∀ (M : ObjectProperty.FullSubcategory
              (fun M : ModuleCat.{u} R ↦ Module.Finite R M)) (s : R),
            (Functor.const ℕᵒᵖ).obj
                ((adicFormalModuleSections R K (adicFormalPrincipalOpen R K s)).obj
                  (E.functor.obj M).obj) ⟶ adicModuleQuotientSections R K M.obj s,
          (∀ M s, Nonempty (IsLimit (Cone.mk _ (p M s)))) ∧
          (∀ M (s : R) (n : ℕ) (m : M.obj),
            (p M s).app (op n)
                (adicFormalModuleUnitSection R K
                  (E.functor ⋙ ObjectProperty.ι _) η M (adicFormalPrincipalOpen R K s) m) =
              tilde.toOpen ((adicModuleQuotientTower R K M.obj).obj (op n))
                (PrimeSpectrum.basicOpen s)
                ((K ^ (n + 1) • (⊤ : Submodule R M.obj)).mkQ m)) ∧
          (∀ M (s t : R)
              (h : adicFormalPrincipalOpen R K (s * t) ≤ adicFormalPrincipalOpen R K s)
              (n : ℕ)
              (x : (E.functor.obj M).obj.val.obj (op (adicFormalPrincipalOpen R K s))),
            (p M (s * t)).app (op n)
                ((E.functor.obj M).obj.val.map
                  (homOfLE h).op x) =
              ((adicModuleQuotientSheaves R K M.obj).obj (op n)).obj.map
                (homOfLE (PrimeSpectrum.basicOpen_mul_le_left s t)).op
                  ((p M s).app (op n) x)) ∧
          (∀ (M N : ObjectProperty.FullSubcategory
              (fun M : ModuleCat.{u} R ↦ Module.Finite R M)) (f : M ⟶ N)
              (s : R) (n : ℕ) (x : (E.functor.obj M).obj.val.obj
                (op (adicFormalPrincipalOpen R K s))),
            (p N s).app (op n) (((E.functor.map f).hom.val.app
                (op (adicFormalPrincipalOpen R K s))) x) =
              ((modulesSpecToSheaf.map ((tilde.functor R).map
                (ModuleCat.ofHom
                  ((f.hom.hom.reduceModIdeal (K ^ (n + 1))).restrictScalars R)))).hom.app
                    (op (PrimeSpectrum.basicOpen s))) ((p M s).app (op n) x)) := by
  sorry

end AlgebraicGeometry
