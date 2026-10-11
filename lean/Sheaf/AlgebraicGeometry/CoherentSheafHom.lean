/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Sheaf Hom of coherent modules

Source: Stacks Project, Modules, Lemma 01CQ, the coherent case
(blueprint: lem-weil-pbc-coherent-sheaf-hom-coherent).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The internal sheaf Hom from a coherent module `G` to a coherent module `F` on any scheme
is coherent, with no Noetherian hypothesis.

Source: Stacks Project, Modules, Lemma 01CQ
(blueprint: lem-weil-pbc-coherent-sheaf-hom-coherent).

Proof:
1. By `pqf-def-coherent`, near each point choose a finite free surjection onto `G`.
   Its kernel is of finite type, so after shrinking there is a finite presentation of `G`
   (Stacks 01BW). Kernels are sectionwise (`def-weil-sheaf-of-modules-category`).
2. By `def-pur-sheaf-hom`, restricting the internal Hom to an open `V` gives the internal
   Hom of `G|_V` and `F|_V`: sections, restrictions and scalar actions agree on smaller opens.
3. Apply `lem-weil-pbc-sheaf-hom-finite-presentation-kernel` to the presentation on `V`.
   The internal Hom is the kernel of a map from a finite direct sum of `F|_V` to another
   finite direct sum of `F|_V` (Stacks 01CQ and 01CO).
4. Restriction preserves coherence by `lem-weil-pbc-coherent-module-local-on-open-cover`.
   By `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`, finite sums, kernels and
   isomorphic modules preserve coherence (Stacks 01BY). Thus the internal Hom on `V`
   is coherent.
5. These opens cover the scheme, so coherence of the internal Hom follows from
   `lem-weil-pbc-coherent-module-local-on-open-cover`. -/
theorem isCoherent_homObj (X : Scheme.{u}) (F G : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) :
    RingedSpace.IsCoherent X.toRingedSpace (SheafOfModules.homObj (R := X.sheaf) G F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
