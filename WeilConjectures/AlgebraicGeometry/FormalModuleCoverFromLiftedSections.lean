/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.FormalTwistedTransitionSections
import WeilConjectures.AlgebraicGeometry.CoherentCoverFromCompatibleTwistedSections
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # A completed cover from liftable generating sections

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A finite generating family at the first level, together with vanishing of first
cohomology of every twisted transition kernel, gives a map from a completed coherent
module whose first component is epi. No algebraization or full faithfulness is assumed.
(Stacks, Tag 0885.) -/
theorem formalModule_cover_from_lifted_sections
    {X : Scheme.{u}} [IsNoetherian X] (K : X.IdealSheafData)
    (F : CoherentFormalModule X K) (L : X.Modules) [L.IsInvertible] (d : ℕ)
    (hvan : ∀ k : ℕ,
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
        (Scheme.Modules.tensorObj (kernel (F.obj.map (homOfLE (Nat.le_succ k)).op))
          (L.tensorPow d))))
    (σ : (Scheme.Modules.tensorObj (F.obj.obj (op 0)) (L.tensorPow d)).GeneratingSections)
    (hσ : σ.IsFiniteType) :
    ∃ G : CoherentModules X, ∃ α : (completion X K).obj G ⟶ F,
      Epi (α.hom.app (op 0)) := by
  classical
  let T := MonoidalCategory.tensorRight (L.tensorPow d)
  have hsurj (n : ℕ) : Function.Surjective
      (SheafOfModules.sectionsMap (T.map (F.obj.map (homOfLE (Nat.le_succ n)).op))) :=
    formal_twisted_transition_sections_surjective K F L d n (hvan n)
  let lift (n : ℕ) (s : (T.obj (F.obj.obj (op n))).sections) :
      (T.obj (F.obj.obj (op (n + 1)))).sections := (hsurj n s).choose
  have hlift (n : ℕ) (s : (T.obj (F.obj.obj (op n))).sections) :
      SheafOfModules.sectionsMap (T.map (F.obj.map (homOfLE (Nat.le_succ n)).op))
        (lift n s) = s := (hsurj n s).choose_spec
  let s : ∀ n : ℕ, σ.I → (T.obj (F.obj.obj (op n))).sections :=
    fun n ↦ Nat.rec σ.s (fun n s i ↦ lift n (s i)) n
  have hs (n : ℕ) (i : σ.I) :
      SheafOfModules.sectionsMap (T.map (F.obj.map (homOfLE (Nat.le_succ n)).op))
        (s (n + 1) i) = s n i := hlift n (s n i)
  obtain ⟨G, g, hg, hepi⟩ :=
    coherent_cover_from_compatible_twisted_sections F.obj (L.tensorPow d) σ hσ s rfl hs
  have hz (n : ℕ) :
      Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (n + 1)).2 G.obj ≫
        g n = 0 := by
    obtain ⟨a, ha⟩ := formalModuleQuotient_factor K (g n) (Nat.le_refl (n + 1))
    rw [ha, (F.property.2.1 n).eq_zero_of_tgt a, zero_comp]
  let a (n : ℕ) : formalModuleQuotient K (n + 1) G.obj ⟶ F.obj.obj (op n) :=
    cokernel.desc _ (g n) (hz n)
  have ha (n : ℕ) : formalModuleQuotientπ K (n + 1) G.obj ≫ a n = g n :=
    cokernel.π_desc _ _ _
  have hn (n : ℕ) : (formalCompletionSystem K G.obj).map
      (homOfLE (Nat.le_succ n)).op ≫ a n =
        a (n + 1) ≫ F.obj.map (homOfLE (Nat.le_succ n)).op := by
    apply (cancel_epi (cokernel.π
      (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (n + 2)).2
        G.obj))).1
    change formalModuleQuotientπ K (n + 2) G.obj ≫ _ =
      formalModuleQuotientπ K (n + 2) G.obj ≫ _
    rw [← Category.assoc, ← Category.assoc, ha (n + 1), hg]
    simpa [formalCompletionSystem, formalModuleQuotientMap, formalModuleQuotientπ,
      Category.assoc] using ha n
  let α : (completion X K).obj G ⟶ F :=
    ⟨NatTrans.ofOpSequence a hn⟩
  have : Epi (g 0) := hepi
  have heq : formalModuleQuotientπ K 1 G.obj ≫ α.hom.app (op 0) = g 0 := ha 0
  have : Epi (formalModuleQuotientπ K 1 G.obj ≫ α.hom.app (op 0)) := heq.symm ▸ hepi
  exact ⟨G, α, epi_of_epi (formalModuleQuotientπ K 1 G.obj) (α.hom.app (op 0))⟩

end AlgebraicGeometry
