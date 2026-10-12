/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-!
# Étale and Zariski cohomology of quasi-coherent modules on curves

Source: Stacks Project, Descent, Proposition 03DW, part (2), and Cohomology,
Proposition 02UZ (blueprint: lem-sc-ga-cohomology).

The associated étale sheaf of the structure module `Scheme.Modules.unit C` is `Gₐ`.
Étale cohomology uses `Sheaf.H`; Zariski module cohomology uses the recorded right
derived functors `RingedSpace.moduleCohomology`, with their underlying additive groups.
The comparison with the derived-global-sections encoding of étale cohomology is a
stage-3 bridge, as specified by `def-weil-pbc-etale-cohomology`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Étale and Zariski cohomology agree for each quasi-coherent module on a curve.
Source: Stacks Project, Descent, Proposition 03DW (2)
(blueprint: lem-sc-ga-cohomology).

Proof: Apply `lem-sc-etale-zariski-qcoh-comparison` to `C` and `F`. Invert its
canonical comparison from Zariski to étale cohomology in degree `q` to obtain the
stated additive equivalence. The associated sheaf is the one defined by
`def-sc-etale-qcoherent-module`, with sections `Γ(U,u^*F)` and pullback restrictions. -/
theorem etale_zariski_cohomology_agree {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : C.Modules) [F.IsQuasicoherent] (q : ℕ) :
    Nonempty (Sheaf.H (Scheme.Modules.etaleTensorSectionsSheaf F) q ≃+
      ((RingedSpace.moduleCohomology C.toRingedSpace q).obj F)) := by
  sorry

/-- The comparison specialized to `Gₐ = (𝒪_C)_et`.
Source: Stacks Project, Descent, Proposition 03DW (2), specialized to the structure
sheaf (blueprint: lem-sc-ga-cohomology).

Proof: In step 1, take `F = 𝒪_C`, which is quasi-coherent. By
`def-sc-etale-qcoherent-module`, its associated étale sheaf has sections
`Γ(U,u^*𝒪_C) = Γ(U,𝒪_U)` with addition and the usual pullback restrictions, so this
is precisely the additive étale sheaf `Gₐ`. This is step 3 of the node's proof. -/
theorem etale_ga_cohomology_agree {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] (q : ℕ) :
    Nonempty (Sheaf.H (@Scheme.Modules.etaleTensorSectionsSheaf C (Scheme.Modules.unit C)
        (SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf))) q ≃+
      ((RingedSpace.moduleCohomology C.toRingedSpace q).obj (Scheme.Modules.unit C))) := by
  sorry

/-- Both cohomology groups of `Gₐ` and `𝒪_C` vanish in degree at least two on a smooth
connected curve. Source: Stacks Project, Descent, Proposition 03DW (2), and Cohomology,
Proposition 02UZ (blueprint: lem-sc-ga-cohomology).

Proof:
1. As in step 1, use `lem-sc-etale-zariski-qcoh-comparison` for the structure module
   to identify the two additive groups.
2. By `def-sc-curves`, `C` is finite type over the field `k` and has dimension at most
   one. The spectrum of a field is Noetherian, so
   `lem-weil-pbc-finite-type-over-noetherian` makes `C` Noetherian. For `2 ≤ q`, we have
   `q > dim C`. Apply `lem-sc-noetherian-cohomology-above-dimension` to obtain zero
   Zariski cohomology. This is step 2 of the node's proof.
3. The associated structure module sheaf is `Gₐ` by
   `def-sc-etale-qcoherent-module`. Transport the vanishing across the comparison
   of step 1. This is step 3 of the node's proof. -/
theorem subsingleton_etale_ga_and_structure_cohomology {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H
      (@Scheme.Modules.etaleTensorSectionsSheaf C (Scheme.Modules.unit C)
        (SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf))) q) ∧
    Subsingleton ((RingedSpace.moduleCohomology C.toRingedSpace q).obj
      (Scheme.Modules.unit C)) := by
  sorry

end AlgebraicGeometry
