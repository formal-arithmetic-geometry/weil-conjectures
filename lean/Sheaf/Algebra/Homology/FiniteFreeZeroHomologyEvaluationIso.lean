/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import Sheaf.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact


@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Invertibility of the cycle-compatible finite-free homology evaluation map.

Source: Stacks Project, Tag 0BQY, finite-free Hom calculation in Lemma 48.15.4;
Tag 0A8X, the product terms and differential of the Hom complex.
(blueprint: new-v4-finite-free-zero-homology-evaluation-iso).

Proof: The fixed projections identify the Hom complex with the product over p
of complexes having terms Hom(E.X p,K.X(p+n)). Their differentials have only the
K term, since the E differential vanishes. Remove the zero factors outside the
finite interval specified by hsupp, leaving a finite product. For each remaining
p, choose the given finite-free basis; internal Hom out of E.X p is thereby
naturally a finite product of copies of the identity. It is exact by
finiteFreeInternalHomExact, so its homology is Hom(E.X p,H^(p+n)(K)). Finite
products in an abelian category preserve kernels and cokernels, hence homology.
By hK all factors except p=-n are zero. The surviving projection thus induces
an isomorphism g from H^n(Hom(E,K)) to Hom(E.X(-n),H^0(K)). Since E has zero
differentials, both its cycle inclusion and class map are isomorphisms.
The equation hc identifies c with the kernel lift of this same projection;
the equation hf identifies f, after these E isomorphisms, with g. Cancel the
P class epimorphism to obtain that equality. Consequently f is an isomorphism.
If -n is outside the support all surviving objects are zero. Rank zero, a zero
ring, and empty site objects give the same calculation. This proves only
invertibility of a supplied compatible map, not existence or cycle descent. -/
theorem finiteFreeZero_homologyEvaluation_iso
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hK : ∀ k : ℤ, k ≠ 0 → IsZero (K.homology k))
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r))))
    (f : (homComplex (R := R) E K).homology n ⟶
      SheafOfModules.homObj (R := R) (E.homology (-n)) (K.homology 0))
    (c : (homComplex (R := R) E K).cycles n ⟶
      SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0))
    (hc : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
      (homComplex (R := R) E K).iCycles n ≫
        (Classical.choose (homComplex_projections_exists (R := R)))
          E K n (-n) 0 (by omega) ≫
        SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _))
    (hf : c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
      (homComplex (R := R) E K).homologyπ n ≫ f ≫
        SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _)) :
    IsIso f := by
  sorry

end CategoryTheory
