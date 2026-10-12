/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Injectivity of one minus shift on a sequential coproduct

Source: Stacks Project, Derived Categories, Lemma 093W, used in Lemma 0949.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- One minus shift is monic on the coproduct of a sequential system of complexes
of sheaves of modules. Source: Stacks Project, Derived Categories, Lemma 093W,
proof, used in Lemma 0949 (blueprint: lem-pc-telescope-shift-mono).

Proof: Work in each cochain degree. The category of sheaves of modules is
Grothendieck abelian, so sequential colimits preserve monomorphisms and finite
sums exist. Put A_n = the sum of E_j over j < n, and B_n = the sum over j ≤ n.
Define u_n : A_n ⟶ B_n on summand j by inclusion in j minus the transition
map followed by inclusion in j+1. These maps commute with the usual inclusions
A_n ⟶ A_(n+1) and B_n ⟶ B_(n+1). Each u_n is split monic: project B_n onto
its first n summands. The resulting endomorphism of A_n is 1 minus the strictly
lower triangular shift. That shift has nth power zero, and its inverse is the
finite sum 1 + shift + ... + shift^(n-1); composing this inverse with the
projection gives a retraction of u_n (for n = 0 use the unique map to zero).
Taking the exact sequential colimit therefore gives a monomorphism. Both
colimits of finite initial sums identify with the countable coproduct, since
a compatible family of maps out of the initial sums is precisely a family of
maps out of all summands. Under these identifications, the colimit of u_n is
the displayed Sigma.desc map, as checked on every coproduct injection. Finally,
monicity in every degree implies monicity of the morphism of complexes.
No transition map is assumed monic. Zero diagrams and zero transition maps
satisfy the same finite triangular-matrix calculation. -/
theorem telescopeShift_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (E : ℕ ⥤ CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    Mono (Sigma.desc (fun n : ℕ ↦
      Sigma.ι (fun n : ℕ ↦ E.obj n) n -
        E.map (homOfLE (Nat.le_succ n)) ≫
          Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))) := by sorry

end CochainComplex
