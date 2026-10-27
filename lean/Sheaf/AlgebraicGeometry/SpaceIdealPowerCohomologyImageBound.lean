/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealPowerQuotients
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.FiniteReesModuleGeneration

/-! # Uniform ideal-power image bounds for algebraic-space cohomology

Source: Stacks Project, Spaces Cohomology, Situation 08AV and Lemma 08AX(2),
lemma-cohomology-powers-ideal-application
(blueprint: lem-sfb-space-ideal-power-cohomology-image-bound).

The ideal-power submodule is the kernel of the already constructed sheaf quotient.
Restriction to the small affine model is the existing ringed equivalence. The derived
scalar-sections functor computes additive sheaf cohomology with its structural A-action
(Stacks 03FD). Finite presentation expresses coherence on the locally Noetherian space
provided by properness over the Noetherian base (Stacks 07UB).

## Main definitions

- `baseIdealPowerSmallModule`: the ideal-power subsheaf on the small ringed model.
- `baseIdealPowerSmallInclusion`: its canonical transition inclusion.
- `baseScalarCohomology`: the existing scalar-sections right derived functor, specialized
  to the given affine base.

## Main statements

- `space_ideal_power_cohomology_image_bound`: the uniform image estimate of 08AX(2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

variable {A : Type u} [CommRing A]

/-- The actual ideal-power submodule, on the equivalent small ringed model.
The full cokernel universal property of the existing quotient identifies this kernel
with (I O_X)^n F, including n = 0, when it is canonically F.
Source: Stacks, Situation 08AV
(blueprint: lem-sfb-space-ideal-power-cohomology-image-bound). -/
def baseIdealPowerSmallModule (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (F : X.Modules) (n : ℕ) : X.SmallModules :=
  kernel (X.smallModuleRestriction.map ((baseIdealQuotientTower X I F).projection n))

/-- The inclusion of ideal powers, induced by the normalized quotient transition.
Its composite with the kernel inclusion into F is the source kernel inclusion.
Source: Stacks, Situation 08AV and Lemma 08AX(2)
(blueprint: lem-sfb-space-ideal-power-cohomology-image-bound). -/
def baseIdealPowerSmallInclusion (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (I : Ideal A) (F : X.Modules) (r n : ℕ) (h : n ≤ r) :
    baseIdealPowerSmallModule X I F r ⟶ baseIdealPowerSmallModule X I F n :=
  kernel.map _ _ (𝟙 _) (X.smallModuleRestriction.map
    ((baseIdealQuotientTower X I F).transition r n h)) (by
      rw [Category.id_comp, ← Functor.map_comp]
      exact congrArg X.smallModuleRestriction.map
        ((baseIdealQuotientTower X I F).transition_projection r n h))

/-- Right derived global sections with the A-action pulled back from Spec A.
This derives in all module sheaves, rather than only quasi-coherent ones. Stacks 03FD
identifies the result naturally with cohomology of the underlying additive sheaf,
compatibly with every scalar endomorphism and with the degree-zero sections map.
Source: Stacks, Situation 08AV and Tag 03FD
(blueprint: lem-sfb-space-ideal-power-cohomology-image-bound). -/
def baseScalarCohomology (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (q : ℕ) :
    X.SmallModules ⥤ ModuleCat.{u} A :=
  (affineScalarSections A (Over.mk (𝟙 (Spec (CommRingCat.of A))))
    (Iso.refl _) X f).rightDerived q

/-- Uniform ideal-power decay of the inclusion-induced cohomology images.
No localness, completeness, flatness or schematicity is required.
Source: Stacks, Situation 08AV and Lemma 08AX(2)
(blueprint: lem-sfb-space-ideal-power-cohomology-image-bound).

Proof:
1. Apply lem-sfb-space-cohomology-powers-rees-finite to A, I, f, F and q. It gives
finite generation of the direct sum of M_r = H^q(X,J^r F) over Rees(I), the maps
L(k,r,a) from multiplication by a in I^k, their convolution action and the identity
L(0,r,a)(x) = a x. The module/additive comparison is natural in these sheaf maps.
2. Apply lem-weil-pbc-finite-rees-module-single-degree-generation. Choose its c0
as c. For every d >= c and k >= 0, M_(d+k) is the A-span of L(k,d,a)(x) for
all a in I^k and x in M_d.
3. For d >= n, multiplication followed by inclusion and inclusion followed by
multiplication have the same composite into F: both send a local section s to
f-sharp(a) s. Cancel the monic inclusion of J^n F. Functoriality of cohomology
and the degree-zero scalar identity give u_(d+k,n) L(k,d,a)(x) = a u_(d,n)(x).
The same sectionwise identity for degree-zero scalars proves A-linearity of u.
4. Given n >= 0 and m >= c, put d = max(n,c) and k = n+m-d. Then d >= n,c,
d+k = n+m and k >= m-c. The generators from step 2 map by step 3 into I^k M_n;
additivity and A-linearity give this for their finite A-linear combinations.
Finally I^k is contained in I^(m-c), so the whole image lies in I^(m-c) M_n.
The argument includes zero modules, the empty space, I = 0, I = A and n = 0. -/
theorem space_ideal_power_cohomology_image_bound
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (hf : MapIsProper f) (F : X.Modules) (hF : F.IsFinitePresentation) (q : ℕ) :
    ∃ c : ℕ, ∀ n m : ℕ, c ≤ m →
      LinearMap.range ((baseScalarCohomology X f q).map
        (baseIdealPowerSmallInclusion X I F (n + m) n (Nat.le_add_right n m))).hom ≤
      I ^ (m - c) • (⊤ : Submodule A
        ((baseScalarCohomology X f q).obj (baseIdealPowerSmallModule X I F n))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
