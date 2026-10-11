/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.SheafExt
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherence of sheaf Ext

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.11.5 (Tag 0D0C)
(blueprint: lem-sc-sheaf-ext-coherent).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme, sheaf Ext of coherent modules is coherent in every
integer degree. Source: Stacks Project, Derived Categories of Schemes, Lemma 36.11.5
(Tag 0D0C) (blueprint: lem-sc-sheaf-ext-coherent). 

Proof:
1. Work locally on an affine open `U = Spec A` with `A` Noetherian
   (`pqf-def-locnoeth`). Coherent modules are quasi-coherent of finite type
   (`pqf-lem-coherent-ft-locnoeth`). Thus their sections `M = F(U)` and `N = G(U)`
   are finite A-modules (`lem-weil-pbc-quasi-coherent-finite-type-affine`), and
   the affine counits identify their associated sheaves with the restrictions of F and G
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`).
2. Sheaf Ext is the cohomology sheaf of derived internal Hom
   (`def-weil-pbc-sheaf-ext`). Cohomology sheaves commute with open restriction,
   as does derived internal Hom (`lem-sc-derived-internal-hom-restrict-open`, Tag 08DL).
   The affine calculation (`lem-sc-affine-rhom-qcoherent`) identifies this restriction
   with zero for q < 0 and with the associated sheaf of Ext^q_A(M,N) for q >= 0.
3. For q >= 0, Ext^q_A(M,N) is finite (`lem-sc-ext-noetherian-finite`), so its
   associated sheaf is quasi-coherent and of finite type, by the affine adjunction
   (`lem-weil-pbc-affine-tilde-gamma-adjunction`) and the affine finite-type criterion
   (`lem-weil-pbc-quasi-coherent-finite-type-affine`). For q < 0 the zero sheaf is coherent.
   Quasi-coherence and finite type are local on X, hence all these sheaf Ext modules
   are coherent (`pqf-lem-coherent-ft-locnoeth`, Tag 01XZ).
-/
theorem sheafExt_isCoherent (X : Scheme.{u₁}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (F G : SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    ∀ q : ℤ, RingedSpace.IsCoherent X.toRingedSpace (moduleSheafExt X q F G) := by
  sorry

end AlgebraicGeometry
