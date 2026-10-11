/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.AffineModuleCorrespondence

/-! # Finite type under the affine module correspondence

Source: Stacks Project, Cohomology of Schemes, Tag 0897, proof; Morphisms, Tag 01SB;
Properties, Tag 01PB (blueprint: lem-weil-pbc-affine-module-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U X : Scheme.{u}} (f : U ⟶ X)

set_option hygiene false in
local notation "A" => (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
set_option hygiene false in
local notation "AR" => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "R" => SheafOfModules.pushforward.{u} (F := Opens.map f.base)
  (S := AR) (R := U.ringCatSheaf) (𝟙 AR)

/-- Finite type is preserved in both directions by the affine module correspondence.
The direct image carries its sectionwise action by `A = f_* O_U`, rather than merely
its restricted `O_X`-action. Source: Stacks Project, Tag 0897, proof (the omitted
finite-type detail), with Tags 01SB and 01PB
(blueprint: lem-weil-pbc-affine-module-finite-type).

Proof (the five steps of the node):
1. Transport finite generation through the given `A`-linear isomorphism, reducing to
   `M = f_* F` (`lem-weil-pbc-affine-module-correspondence`). An epimorphism from a
   finite free module means every section is locally a linear combination of its
   basis images (`def-weil-sheaf-of-modules-category`,
   `def-weil-pbc-module-finite-type-presentation`). Generation restricts to smaller
   opens. Affine opens form a basis, and their inverse images are affine.
2. On an affine open `V` of `X`, set `B = O_U(f⁻¹ V)`. A finite family generating
   `M|_V` over `A|_V` generates `F(f⁻¹ V)` over `B`: form the map from the finite
   free quasi-coherent module on `f⁻¹ V` and use the affine-sections image formula
   (`lem-weil-pbc-quasi-coherent-module-cokernel-image`), together with
   `lem-weil-pbc-module-restriction-open-immersion-colimits` and
   `lem-weil-pbc-spec-tilde-free-module`.
3. Conversely, sections generating `F|_(f⁻¹ V)` generate `M|_V`: cover any open
   inside `V` by affine opens. On their affine inverse images the same image formula
   supplies the coefficients, now read as sections of `A`.
4. If `M` is finite type, choose generators near `f(y)` and shrink to an affine
   neighbourhood. Step 2 gives a finite `B`-module of sections. Apply
   `lem-weil-pbc-quasi-coherent-finite-type-affine` to get finite type near `y`.
5. If `F` is finite type, that same affine criterion gives a finite `B`-module of
   sections on every affine inverse image. Its generators generate the sheaf by
   `lem-weil-pbc-affine-finite-type-generating-sections`. Step 3 gives generators
   over `A` near every point of `X`. These prove the asserted equivalence. -/
theorem affine_module_finite_type [IsAffineHom f]
    (M : SheafOfModules.{u} AR) (hM : M.IsQuasicoherent)
    (F : U.Modules) (hF : F.IsQuasicoherent) (e : (R).obj F ≅ M) :
    M.IsFiniteType ↔ F.IsFiniteType := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
