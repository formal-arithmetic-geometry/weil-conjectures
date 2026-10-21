/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-!
# A specified scalar presentation after extension to coefficient sheaves

Source: blueprint main-20261015, proper base change unbounded, pullback proof,
paragraph "Constructible complexes"; Stacks, Modules on Sites, Tags 03CY, 03CZ,
0GMW and Section 03EK (blueprint: lem-sfb-scalar-presentation-cokernel).

The coefficient functor and scalar matrix are the existing local-model constructions.
Matrix entries are maps from the integer tensor unit, equivalently elements of Λ(*).
Their first index is the source column and their second index is the target row.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A specified finite scalar presentation remains a cokernel diagram after taking
constant module sheaves and extending scalars to Λ_U. The free comparisons send
`1 ⊗ e_j` to `e_j`; the final cokernel comparison commutes with the specified quotient.
Source: blueprint proper-base-change-unbounded pullback proof, "Constructible complexes";
Stacks, Modules on Sites, Tags 03CY, 03CZ, 0GMW and Section 03EK
(blueprint: lem-sfb-scalar-presentation-cokernel).

Proof:
1. On the small pro-étale site, use the closed sheaf tensor structure
   [lem-weil-pbc-sheaf-tensor-closed], the internal/section-module equivalence
   [def-weil-pbc-internal-abelian-sheaf-module-equivalence] and its pure-tensor comparison
   [lem-pe-internal-section-tensor-comparison]. Commutativity identifies the coequalizer
   for extension [def-sfb-modobj-extension] with the relative tensor
   [def-sfb-modobj-relative-tensor], preserving the coefficient-ring action.
2. The constant presheaf diagram is a cokernel objectwise, with natural factorizations
   forced by uniqueness. Module sheafification [lem-cbc-sieve-module-sheafification]
   preserves this cokernel and finite free sums, being a left adjoint
   [lem-weil-pbc-left-adjoint-preserves-colimits]. It preserves standard basis sections.
3. Extension by the canonical scalar map is the tensor left adjoint of
   [lem-weil-pbc-ringed-topoi-module-adjunction]. It preserves that specified cokernel,
   zero maps and finite sums; no flatness assumption is required.
4. The free comparison sends s ⊗ (v_i) to (s φ(v_i)); its inverse sends (s_i) to
   ∑ s_i ⊗ e_i. Balancing and the bilinear universal property
   [lem-pc-sites-sheaf-tensor-bilinear-universal] prove the inverse identities, including
   the empty-sum case. This gives exactly the displayed basis normalization.
5. On each basis vector the transported matrix sends e_j to ∑ φ(a_ij)e_i.
   Thus it is the existing scalarMatrix of [det-def-sfb-constructible-local-model],
   with the original entries mapped by the canonical scalar map.
6. Transport the cokernel universal property along these free comparisons. Its
   factorization and uniqueness give the asserted IsColimit, and then the unique
   isomorphism to the chosen cokernel commuting with the quotient arrows
   [def-sfb-finitely-presented-module]. -/
theorem scalar_presentation_cokernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (U : Scheme.{u}) (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (q : Mod.finiteFree (scalarRingObj Λ) n ⟶ P)
    (hAq : (biproduct.matrix fun j i ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j i)) ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hAq)) :
    ∃ e : ∀ r : ℕ,
        (finiteConstantScalarExtension Λ U).obj (Mod.finiteFree (scalarRingObj Λ) r) ≅
          Mod.finiteFree (condensedRingObj Λ U) r,
      (∀ (r : ℕ) (j : Fin r),
        Functor.LaxMonoidal.ε (scalarConstant U) ≫
          (scalarConstant U).map
            ((MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
              (biproduct.ι (fun _ : Fin r ↦ Mod.regular (scalarRingObj Λ)) j).hom) ≫
          Mod.extendUnitHom (scalarCoefficientHom Λ U)
            (((scalarConstant U).mapMod (scalarRingObj Λ)).obj
              (Mod.finiteFree (scalarRingObj Λ) r)) ≫ (e r).hom.hom =
          (MonObj.one : 𝟙_ (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) ⟶
            condensedRingObj Λ U) ≫
              (biproduct.ι (fun _ : Fin r ↦ Mod.regular (condensedRingObj Λ U)) j).hom) ∧
      ((e m).inv ≫ (finiteConstantScalarExtension Λ U).map
          (biproduct.matrix fun j i ↦
            Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j i)) ≫ (e n).hom =
        scalarMatrix Λ U A) ∧
      ∃ h : scalarMatrix Λ U A ≫ (e n).inv ≫
          (finiteConstantScalarExtension Λ U).map q = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ
          ((e n).inv ≫ (finiteConstantScalarExtension Λ U).map q) h)) ∧
        ∃ c : (finiteConstantScalarExtension Λ U).obj P ≅ cokernel (scalarMatrix Λ U A),
          (e n).inv ≫ (finiteConstantScalarExtension Λ U).map q ≫ c.hom =
            cokernel.π (scalarMatrix Λ U A) := by
  sorry

end AlgebraicGeometry.ProEtale
