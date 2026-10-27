/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Algebra.Homology.SourceHyperExtModuleTarget
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite

/-! # Finite cohomology of derived Hom into a finite module

Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom,
the finite-module-target case of the algebra assertion in its proof.
(blueprint: lem-trf-finite-module-target-rhom).

The ordinary-module derived internal Hom is the recorded ordinary-module presentation
of the one-object site with only identity coverings.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedCategory

/-- Derived Hom from an upper-bounded complex with finite cohomology to a finite
module has finite cohomology and vanishes below the negative source upper bound.
Source: Stacks Project, perfect.tex, Tag 0D0C, lemma-coherent-internal-hom, proof;
injectives.tex, Tag 0G20; algebra.tex, Tag 08YR.
(blueprint: lem-trf-finite-module-target-rhom).

Proof:
1. Apply lem-trf-source-hyperext-module-target to A, K, N and b, presenting ordinary
   modules on its one-object identity-covering site. The resulting A-linear spectral
   sequence has E2^{i,j}=Ext_A^i(H^{-j}(K),N), support i>=0 and j>=-b,
   differentials of bidegree (s,1-s), and next-page kernel/image identifications.
   Its abutment H^t RHom_A(K,N[0]) has a finite exhaustive separated filtration
   with successive quotients E-infinity^{t-j,j}, for -b<=j<=t.
2. By lem-sc-ext-noetherian-finite, each E2 term with i>=0 is finite because both
   H^{-j}(K) and N are finite over the Noetherian ring A. Terms with i<0 are zero
   and therefore finite as well.
3. Apply lem-trf-noetherian-quadrant-abutment with quadrant bounds 0 and -b.
   Reindex the abutment filtration by p=t-j, so its graded pieces have
   0<=p<=t+b. Extend it constantly by the abutment to the left and by zero to
   the right; outside this interval the limiting terms vanish by the support.
   This gives finite generation of every abutment. If t<-b, the interval is
   empty and the source spectral-sequence statement already gives zero abutment;
   the zero filtration meets the same requirements. Thus vanishing holds exactly
   in the claimed range. -/
theorem finite_module_target_rhom
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (N : ModuleCat.{u} A)
    [Module.Finite A N] (b : ℤ)
    (hK : ∀ j : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hKb : ∀ j : ℤ, b < j → IsZero ((homologyFunctor (ModuleCat.{u} A) j).obj K)) :
    (∀ t : ℤ, Module.Finite A
      ((homologyFunctor (ModuleCat.{u} A) t).obj
        ((ordinaryModuleDerivedInternalHom A).obj
          (op K, (singleFunctor (ModuleCat.{u} A) 0).obj N)))) ∧
    (∀ t : ℤ, t < -b → IsZero
      ((homologyFunctor (ModuleCat.{u} A) t).obj
        ((ordinaryModuleDerivedInternalHom A).obj
          (op K, (singleFunctor (ModuleCat.{u} A) 0).obj N)))) := by
  sorry

end DerivedCategory
