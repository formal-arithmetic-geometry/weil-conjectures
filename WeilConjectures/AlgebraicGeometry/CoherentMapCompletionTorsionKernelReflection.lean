/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimit
import WeilConjectures.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero
import WeilConjectures.AlgebraicGeometry.SupportedCoherentCompletionReflectsZero

/-! # Reflecting kernel torsion from completion on a closed thickening

Stacks Project, Tags 088A and 0888.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Reflect a componentwise torsion bound for the completion of a coherent map whose
source and target are annihilated by the ideal of a fixed closed thickening
(Stacks, Tags 088A and 0888). -/
theorem coherentMap_completion_torsion_kernel_reflection
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (hq : 1 ≤ q)
    (hcompletion : ∀ (hZ : IsNoetherian (K ^ q).subscheme),
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F G : CoherentModules X) (a : F ⟶ G)
    (hF : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 F.obj))
    (hG : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι q).2 G.obj))
    (s : ℕ) (hs : 1 ≤ s)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι s).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1)))))) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (kernel a.hom)) := by
  have _ := hG
  have ha := coherentFormalModule_annihilated_affine_limit X I K
    ((completion X I).obj F) ((completion X I).obj G) ((completion X I).map a) s hs h
  obtain ⟨hcoh, hzero⟩ := coherentKernel_idealProduct_completion_zero I K F G a (2 * s)
    (fun U ↦ (ha U).1)
  let H : CoherentModules X := ⟨_, hcoh⟩
  let j : H.obj ⟶ F.obj :=
    Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι (2 * s)).2
      (kernel a.hom) ≫ kernel.ι a.hom
  have : Mono j := by
    dsimp [j, Scheme.idealModuleProductι]
    infer_instance
  exact supportedCoherent_completion_reflects_zero I K q hq hcompletion F H j hF hzero

end AlgebraicGeometry
