/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Sectionwise inverse image along a scheme isomorphism

Source: Stacks Project, Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).

This is the sectionwise model of the recorded inverse image under its canonical
comma-coprojection identification. Coefficients may have any universe containing
the small site's objects; the site's object and morphism universes stay distinct.
The original site equivalence, comparison, and constant-module results are reexported.

## Main definitions and statements

- `isoSectionwiseInverseImage`: the canonical sectionwise model, with arbitrary Hom size.
- `isoSectionwiseInverseImage_equivalence`: equivalence and preservation of limits/colimits.
- `isoSectionwiseConstantMap`: coefficient transport uniquely normalized on constants.
- `isoSectionwiseModuleInverseImage`: the module action transported through the ring map.
- `isoSectionwiseModuleInverseImage_exact`: additivity and exactness of that functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t r d v w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Postcomposition with an isomorphism preserves the topology.
Source: Stacks Tag 09A5 (blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: compose structure maps with g or its inverse. The underlying schemes,
arrows, and fpqc covering families do not change; the two operations are inverse.
Thus sheaves pull back by precomposition, in every coefficient universe. -/
@[instance] theorem proEtaleIsoPostcompose_isContinuous
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
  have := (proEtaleIsoPostcompose_equivalence g).1
  exact (Functor.isContinuous_iff_coverPreserving).2
    (proEtaleIsoPostcompose_equivalence g).2.2.2.1.some

/-- The specified coefficient map is invertible.
Source: Stacks Tags 09A5 and 00WX
(blueprint: lem-weil-proetale-isomorphism-inverse-image).
Proof: inverse site transport gives the inverse constant-section map. Both
composites are identities on constant sections and hence on their sheafifications. -/
@[instance] theorem isoSectionwiseConstantMap_isIso {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{max r (t + 1)}) :
    IsIso (isoSectionwiseConstantMap g A) := by
  let e := sectionwiseConstantCommIso g A
  let W := sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)
  have he : isoSectionwiseConstantMap g A = W.map e.hom := by
    apply (isoSectionwiseConstantMap_existsUnique g A).unique
    · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
    · intro U a
      exact congrArg (fun f ↦ (f.app (op U)) a)
        (sectionwiseConstantCommIso_normalization g A)
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
