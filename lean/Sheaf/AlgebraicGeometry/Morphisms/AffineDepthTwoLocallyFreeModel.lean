/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.RingTheory.Depth

import Sheaf.AlgebraicGeometry.ModuleFinitePresentationExtension
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # A coherent depth-two model of a finite locally free module on an affine open

Source: Stacks Project, Tags 0G41(2), 0EY6 proof of (1), and the kernel
calculation for double duals underlying Tags 0EBI and 0EBJ.
(blueprint: lem-sbc-affine-depth-two-locally-free-model)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

/-- Construct a coherent depth-two module before making any Hartogs comparison.

Source: Stacks Project, Tag 0G41(2), Tag 0EY6 proof of (1), and the
nonintegral double-dual kernel calculation in the parent node's proof, steps 2--3.
(blueprint: lem-sbc-affine-depth-two-locally-free-model)

Proof: The Noetherian affine scheme has a quasi-compact open W. Apply
exists_finitePresentation_extension with zero ambient module and zero map
(Tag 01PI, whose zero-map case is 0G41(2)) to extend P to a finitely presented
module. Use the affine equivalence to write the extension as the sheaf of a
finite A-module M. Form the actual module D = Hom_A(Hom_A(M,A),A), and set
H = tilde D. Noetherianity makes both duals finite. Finite presentations
ensure that Hom commutes with localization, and a finite locally free module
is its double dual; these give H restricted to W isomorphic to P.
A finite free presentation of Hom_A(M,A), dualized, expresses D as the
kernel of a map d between finite free modules. Localize this presentation
at a boundary point. Choose a regular pair x,y in the local base ring.
Multiplication by x is injective on the free modules and hence on the kernel.
If y*n = x*n' in the kernel, injectivity of y modulo x on the free source
writes n = x*m in that source. Then x*d(m) = d(n) = 0, and injectivity of
x on the free target gives d(m) = 0. Thus m is in the kernel, proving
injectivity of y modulo x on it. A nonzero finite kernel has proper quotient
by the maximal ideal by Nakayama, so this is a regular sequence of length two.
The zero kernel has infinite depth by definition. Localization of tilde
identifies these kernels with H's stalks. Quasi-coherence of tilde and
Noetherianity give finite sections on every affine open and finite stalks.
All witnesses are used only within this existence proof, never to define
an arbitrary module downstream. If W is empty, use the zero module. If
W is the entire spectrum there are no boundary conditions. The empty
spectrum and zero module are allowed. -/
theorem exists_affine_depth_two_locally_free_model
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (P : W.toScheme.Modules) [P.IsFiniteLocallyFree] :
    ∃ H : (Spec A).Modules,
      H.IsQuasicoherent ∧
      (∀ V : (Spec A).Opens, IsAffineOpen V →
        Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) ∧
      (∀ x : Spec A, x ∉ W →
        ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x),
          letI := hfinite
          (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)) ∧
      Nonempty (Modules.restrict H W.ι ≅ P) := by sorry

end AlgebraicGeometry.Scheme
