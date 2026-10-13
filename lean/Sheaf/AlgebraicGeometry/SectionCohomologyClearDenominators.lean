/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.AlgebraicGeometry.InvertSCOhomology

/-! # Denominator bounds for resolution cohomology classes

Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-section-cohomology-clear-denominators).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A raw resolution cohomology class on a principal open has a denominator bound.

Source: Stacks Project, Tag 09MR (lemma-invert-s-cohomology), surjectivity of the
canonical comparison specialized to the tensor unit; Tag 01E4 for its resolution model.
(blueprint: lem-pc-section-cohomology-clear-denominators).

Proof: Set Y = f⁻¹W and let b be the pullback of a to Y. Quasi-compactness of f
and affineness of W make Y quasi-compact; quasi-separatedness of f and W make Y
quasi-separated. The restriction G of F to Y is quasi-coherent. Restriction to
an open is exact and preserves injectives, so I restricted to Y and to D(b)
computes the corresponding module cohomology. Evaluating f_*I at W and D(a)
gives exactly the sections of I on f⁻¹W and f⁻¹D(a); exact evaluation commutes
with presheaf homology. The equality f⁻¹D(a) = D(b) thus identifies P's
restriction with cohomology restriction, and its scalar action with pullback.

Apply invertS_cohomology on Y with the tensor unit and section b. Canonical
unitors identify G tensor O_Y^{tensor n} with G. Under these identifications
multiplication by the tensor-power section is multiplication by b^n: evaluate
on sections, where tensor multiplication is scalar multiplication, and then
apply cohomology. The fraction relation is [i,x] = [i+k,b^k x]. Every element of
the fraction quotient is a finite sum of generators. Choose n at least all
indices in that sum; replace each [i,x] by [n,b^{n-i} x] and add the numerators.
Surjectivity of the canonical comparison therefore writes the given class as
the image of [n,t]. Its defining equation says b^n times that image equals the
restriction of t. Transport through the resolution identifications just
specified. Pullback and restriction commute with powers, giving the displayed
power of the restricted a. This is only the lifting assertion, not the kernel
criterion. If a = 0, D(a) is empty and its cohomology is zero; if a is a unit,
restriction is the identity after identifying D(a) with W. Empty W, zero F and
q = 0 satisfy the same argument. -/
theorem sectionCohomologyPresheaf_clearDenominators {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    ∀ s : P.obj (op (T.basicOpen a)), ∃ (n : ℕ) (t : P.obj (op W)),
      (P.map (homOfLE (T.basicOpen_le a)).op).hom t =
        (T.presheaf.map (homOfLE (T.basicOpen_le a)).op a) ^ n • s := by sorry

end AlgebraicGeometry.Scheme.Modules
