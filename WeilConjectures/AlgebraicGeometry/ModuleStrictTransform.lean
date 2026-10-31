/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Strict transform of a quasi-coherent module

Source: Stacks Project, Divisors, Tag 080D (1), Definition `definition-strict-transform`
and the preceding notation (blueprint: def-trf-module-strict-transform).

For the blowup of the retained centre `I`, put `Y = X ×[S] I.blowup` and let `p` and `q`
be its projections. The open below is the complement of `q⁻¹ E`, where
`E = b⁻¹ V(I)`. Restriction to this open gives a map `p*F → j*j*(p*F)`.
Its kernel is the subsheaf `K` of sections supported on `q⁻¹ E`; the strict transform
is the quotient sheaf `p*F / K`, constructed as the cokernel of the kernel inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The complement of the inverse image of the exceptional divisor in `X ×[S] I.blowup`.
Here `I.support` is `V(I)`, so taking its complementary open and pulling back along
`q ≫ b` gives precisely the complement of `q⁻¹ E`.
Source: Stacks Project, Tag 080D, preceding notation
(blueprint: def-trf-module-strict-transform). -/
noncomputable def moduleStrictTransformOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) : (Limits.pullback f I.blowupMap).Opens :=
  (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ I.support.compl

/-- Restriction of `p*F` to the complement of `q⁻¹ E`, followed by open direct image.
The unit of Mathlib's restriction/direct-image adjunction is the actual restriction map:
on an open `V`, it restricts a section to `V ∩ (q⁻¹ E)ᶜ`.
Source: Stacks Project, Tag 080D (1)
(blueprint: def-trf-module-strict-transform). -/
noncomputable def moduleStrictTransformRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (F : X.Modules) :
    (tensorPullback (pullback.fst f I.blowupMap)).obj F ⟶
      (pushforward (moduleStrictTransformOpen f I).ι).obj
        ((restrictFunctor (moduleStrictTransformOpen f I).ι).obj
          ((tensorPullback (pullback.fst f I.blowupMap)).obj F)) :=
  (restrictAdjunction (moduleStrictTransformOpen f I).ι).unit.app
    ((tensorPullback (pullback.fst f I.blowupMap)).obj F)

/-- The subsheaf `K` of `p*F` whose sections vanish on the complement of `q⁻¹ E`.
It is the kernel of the canonical open-restriction map, so its sections on any open
are exactly the sections of `p*F` restricting to zero on that open's intersection with
`(q⁻¹ E)ᶜ`. No choice of a subobject or of a map is an input.
Source: Stacks Project, Tag 080D (1)
(blueprint: def-trf-module-strict-transform). -/
noncomputable def moduleStrictTransformKernel {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (F : X.Modules) : (Limits.pullback f I.blowupMap).Modules :=
  kernel (moduleStrictTransformRestriction f I F)

/-- The strict transform `Fᵇ = p*F / K` of the quasi-coherent module `F`, relative to the
finite-type quasi-coherent centre `I`. Quasi-coherent ideals are encoded by
`IdealSheafData`; finite type means that their associated ideal module is of finite type.
The quotient is the cokernel of the inclusion of the kernel defined above. The centre
`I` is retained as an argument, not replaced by an arbitrary blowup morphism.
Source: Stacks Project, Tag 080D (1), and its remark on dependence on the centre
(blueprint: def-trf-module-strict-transform). -/
noncomputable def moduleStrictTransform {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) [I.toModules.IsFiniteType] (F : X.Modules)
    [F.IsQuasicoherent] : (Limits.pullback f I.blowupMap).Modules :=
  cokernel (kernel.ι (moduleStrictTransformRestriction f I F))

end AlgebraicGeometry.Scheme.Modules
