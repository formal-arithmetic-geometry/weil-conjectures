/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Topology.QuasiSeparated

/-! # Lifting a section into an ideal-power-torsion-free module

Source: Stacks Project, Properties, Tags 01PM and 01PQ, torsion-free case.
(blueprint: lem-pc-ideal-power-torsion-free-section-lifting)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- A section of an ideal-power-torsion-free module is evaluated by an ideal-power map.

Source: Stacks Project, Properties, Tags 01PM and 01PQ.
(blueprint: lem-pc-ideal-power-torsion-free-section-lifting)

Proof: Cover the quasi-compact scheme by finitely many affine opens. On each affine
write the finite-type ideal as (f_1,...,f_t). Express the section on D(f_i) with a
common positive denominator exponent k. After multiplying the numerators by further
powers, equality on overlaps gives f_j^k x_i = f_i^k x_j. For d=t*(k-1)+1 every
degree-d monomial contains f_i^k; send it to the remaining factor times x_i. Every
relation among these monomials maps to an element killed by every f_j^k, hence by
I^d. The torsion-free hypothesis kills this element, so the assignment descends
to an actual map I^d -> F, rather than a map into an annihilator quotient.
It evaluates to the given section. Increase degrees using r to a common degree
on the finite affine cover. On pairwise overlaps the differences vanish on U.
On each affine chart in a finite cover of an overlap, localization at every f_i
shows a power of f_i kills each image of a finite generating set of the power
ideal. A common ideal power therefore annihilates each such image, and htf makes
it zero. Thus the maps agree on overlaps and glue by sheaf descent. Their
values at one agree with the prescribed section locally and hence globally.
Quasi-separatedness gives the finite overlap covers. For the empty complement,
htf forces F=0 locally (a finitely generated ideal with empty D(I) is nilpotent),
so the zero map works. For the unit ideal use degree zero; on the empty scheme
all maps and sections are unique. No coherent carrier, Artin-Rees argument, or
comparison with ideal-sheaf-data powers is asserted by this lemma. -/
theorem ideal_power_torsionFree_section_lifting
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
    (r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1))
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (hone : ∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)))
    (hr : ∀ (n m : ℕ) (h : n ≤ m),
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2)
    (htf : ∀ (n : ℕ) (W : X.Opens) (x : F.val.obj (op W)),
      (∀ (V : X.Opens) (h : V ≤ W)
        (b : (idealSheafPower ι n).1.val.obj (op V)),
        ((idealSheafPower ι n).2.val.app (op V) b : Γ(X, V)) •
          F.val.map (homOfLE h).op x = 0) → x = 0) :
    ∀ s : Γ(F, U), ∃ (n : ℕ) (ψ : (idealSheafPower ι n).1 ⟶ F),
      ψ.app U (one n) = s := by sorry

end AlgebraicGeometry.Scheme
