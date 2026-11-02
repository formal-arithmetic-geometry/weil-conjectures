/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Normalized exact scalar sections cup at a geometric point

Source: Stacks Project, Tags 0FPJ, 0B6C and 0FPK, sections cup and its naive
normalization (blueprint: lem-sf-exact-sections-derived-cup-map).

## Main definitions

* `pairingExactScalarPointCup`: the uniquely normalized exact scalar cup.
* `pairingExactScalarPointCup_unitIso`: its geometric-point unit identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Use the published site-size specialization, avoiding an unassigned max universe.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- The representative-normalized sections cup over the actual scalar ring Lambda(*).
The ordinary tensorator multiplies pure sections, its unit is the canonical scalar
map, and ExactSectionsDerivedCup imposes every total-complex summand and the native
localization square. Consequently the data used by the cup are uniquely determined.
Source: Stacks 0FPJ, 0B6C and 0FPK
(blueprint: lem-sf-exact-sections-derived-cup-map).
Proof: apply exists_internal to the reconstructed coefficient ring at the final
object of Spec k. Exactness is pairingPointScalarSections_exact. Restrict scalars
along CohomologyTransport.scalarMap and compose its ordinary unital lax tensorator
with that cup. Its chain components are the direct sums of the section pairings,
so the chain_summand and chainUnit_zero normalizations hold. Localization on K-flat
representatives gives the displayed derived tensorator and unit normalizations.
Pure tensors generate the ordinary tensor, total-tensor inclusions determine each
chain map, and every derived object is represented by a K-flat complex. Thus the
localization square determines each derived tensorator and the unit; all laws are
proof fields, proving uniqueness. No invertibility of the tensorator is asserted. -/
theorem pairingExactScalarPointCup_exists :
    ∃! d : CategoryTheory.ExactSectionsDerivedCup
        (CohomologyTransport.sections Λ (Spec (.of k))),
      (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (y : N.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
        (d.ordinary.μ M N).hom (x ⊗ₜ[condensedScalarRing Λ] y) =
          InternalAbelianSheafModule.comparison_internalTmul
            (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
            M N (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y) ∧
      (∀ a : condensedScalarRing Λ,
        d.ordinary.ε.hom a = CohomologyTransport.scalarMap Λ (Spec (.of k)) a) := by
  sorry

/-- The unique sectionwise-normalized cup, retaining its signed total-complex and
localization normalizations. This choice is from uniqueness, rather than from a
mere existence of an unconstrained tensor map.
Source: Stacks 0FPJ and 0FPK (blueprint: lem-sf-exact-sections-derived-cup-map). -/
def pairingExactScalarPointCup : CategoryTheory.ExactSectionsDerivedCup
    (CohomologyTransport.sections Λ (Spec (.of k))) :=
  (pairingExactScalarPointCup_exists Λ k).choose

/-- At the geometric point the normalized sections unit is the coefficient ring
identification, so its derived map is invertible.
Source: Stacks 03P2 and the point-coefficient identification
(blueprint: lem-sf-exact-sections-derived-cup-map).
Proof: the point coefficient theorem identifies evaluation of the pulled-back
coefficient on each profinite test object with Lambda. In particular the normalized
ordinary unit scalarMap on the terminal object is an isomorphism. The chain unit is
this map in degree zero by chainUnit_zero. The unit_normalization square identifies
the derived unit with its image under localization, hence it is invertible. -/
theorem pairingExactScalarPointCup_unit_isIso :
    IsIso (pairingExactScalarPointCup Λ k).derived.ε := by
  sorry

/-- The inverse unit comparison furnished by the actual point-coefficient map.
Source: point coefficients and exact sections (blueprint: lem-sf-exact-sections-derived-cup-map). -/
def pairingExactScalarPointCup_unitIso :
    𝟙_ (DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ))) ≅
      (CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory.obj (𝟙_ _) :=
  @asIso _ _ _ _ (pairingExactScalarPointCup Λ k).derived.ε
    (pairingExactScalarPointCup_unit_isIso Λ k)

end AlgebraicGeometry.ProEtale.CondensedRing
