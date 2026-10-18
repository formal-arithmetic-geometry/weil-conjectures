/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.Paper.ProEtaleSheafificationTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-!
# The field-module calculation for a principal residue quotient

Source: the residue test, proof step 3, and Stacks Project Tags 0GMW and 03EI.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
/-- Tensor cohomology vanishing passes from the constant principal residue quotient to
any sheaf annihilated by its generator. This concerns ordinary termwise tensor of an
arbitrary, possibly unbounded, complex, in one degree. No K-flatness or nilpotence
hypothesis is needed here.

Source: blueprint residue-test proof step 3; Stacks Project, Modules on Sites,
Tags 0GMW (tensor and sheafification) and 03EI (exact sheafification).
(blueprint: lem-sf-proetale-residue-module-tensor-homology).

Proof: Restrict sections along the constant-ring presheaf's sheafification unit.
The annihilation hypothesis gives every section of M a module structure over A/(r),
compatible with restrictions. Form the presheaf complex C = P tensor_A A/(r), with
its A/(r)-action. Sectionwise, tensor over the field A/(r) is exact: split each
short exact sequence of vector spaces. The existing
lem-exc-constant-field-sheaf-tensor-cohomology packages the resulting sheaf identity.
Its proof applies this to the cycles and boundaries of
C to identify H^i(C tensor M) with H^i(C) tensor M. The identification sends
[z] tensor m to [z tensor m], so commutes with restrictions independently of the
splittings. Tensor-sheafification comparison and exact sheafification transport
this equality to sheaves: the sheafification of presheaf homology vanishes,
without assuming sectionwise homology vanishes. The balanced maps
(p tensor t) tensor m -> p tensor tm
and p tensor m -> (p tensor 1) tensor m identify the iterated tensor complex with
P tensor_A M, commuting with restrictions and differentials. Its cohomology is
therefore zero when that of P tensor_A A/(r) is zero. No section ring of the
constant field sheaf is claimed to be a field; all vector-space calculations take
place over the original constant presheaf field. Empty schemes and the zero
complex or zero module are included. Maximality excludes the zero residue ring. -/
theorem proEtale_residue_module_tensor_homology
    (T : Scheme.{u}) (A : Type u) [CommRing A] (r : A)
    (hr : (Ideal.span {r}).IsMaximal)
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (M : proEtaleRingModules T (proEtaleConstantRing T A))
    (hM : ∀ (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U
          (ULift.up r) • x = 0)
    (i : ℤ) :
    letI := SheafOfModules.monoidalCategory (proEtaleConstantRing T A)
    let B := A ⧸ Ideal.span {r}
    let RB := proEtaleConstantRing T B
    let SB := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RB
    let α := (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk (Ideal.span {r})))))
    let N := (SheafOfModules.restrictScalars.{u + 1} α).obj (SheafOfModules.unit SB)
    IsZero ((((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).homology i) →
    IsZero ((((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i) := by
  sorry

end AlgebraicGeometry.Scheme
