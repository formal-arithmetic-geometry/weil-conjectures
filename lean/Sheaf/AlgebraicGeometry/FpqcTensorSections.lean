/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Descent
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# FPQC descent of sections of a tensor pullback

Source: Stacks Project, Descent, Tag 03DT, Lemma 35.8.1, using Tag 023T,
Proposition 35.5.2 (blueprint: lem-sc-etale-qcoherent-descent-fpqc-sections).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-- Compatible sections of a quasi-coherent pullback descend uniquely along an fpqc family.
The two sections on each fibre product are compared using the unit-normalized composition
isomorphisms and transport along the equality of the two morphisms to the base scheme.
Source: Stacks Project, Tag 03DT, Lemma 35.8.1, fpqc case
(blueprint: lem-sc-etale-qcoherent-descent-fpqc-sections).

Proof: (1) Put N = f^*F, quasi-coherent by
lem-weil-pbc-module-pullback-quasi-coherent. Use
lem-sc-etale-qcoherent-presheaf-functorial to identify g_i^*N with (g_i ≫ f)^*F.
A section s_i corresponds to the module map O_{T_i} → g_i^*N sending a to a s_i;
conversely evaluate a module map at 1. This correspondence commutes with pullback,
using lem-weil-pbc-module-pullback-structure-sheaf to identify the pulled-back source.
(2) On each fibre product, the pulled-back maps agree because their values at 1 agree
by the compatibility hypothesis. Thus they give a morphism of canonical descent data.
(3) Apply full faithfulness in lem-pc-fpqc-descent (Tag 023T) to O_T and N for the
fpqc family (def-weil-pbc-fpqc-covering). The maps descend to a unique map O_T → N.
Its value at 1 is the required section. Any other section defines a map with the same
pullbacks, hence the same map by faithfulness; evaluation at 1 proves uniqueness. -/
theorem existsUnique_tensorSections_of_fpqcCover {S T : Scheme.{u}} (f : T ⟶ S)
    (F : S.Modules) [F.IsQuasicoherent] {I : Type v} (Ti : I → Scheme.{u})
    (g : ∀ i : I, Ti i ⟶ T)
    (hg : Presieve.ofArrows Ti g ∈ Scheme.fpqcPrecoverage T)
    (s : ∀ i : I, Γ((tensorPullback (g i ≫ f)).obj F, ⊤))
    (hs : ∀ i j : I,
      ((tensorSectionsComp (pullback.fst (g i) (g j)) (g i ≫ f)).hom.app F).app ⊤
        (tensorSectionsUnit (pullback.fst (g i) (g j))
          ((tensorPullback (g i ≫ f)).obj F) (s i)) =
      (eqToHom (congrArg (fun k ↦ (tensorPullback k).obj F)
        (pullback.condition_assoc (f := g i) (g := g j) f).symm)).app ⊤
        (((tensorSectionsComp (pullback.snd (g i) (g j)) (g j ≫ f)).hom.app F).app ⊤
          (tensorSectionsUnit (pullback.snd (g i) (g j))
            ((tensorPullback (g j ≫ f)).obj F) (s j)))) :
    ∃! t : Γ((tensorPullback f).obj F, ⊤), ∀ i : I,
      ((tensorSectionsComp (g i) f).hom.app F).app ⊤
        (tensorSectionsUnit (g i) ((tensorPullback f).obj F) t) = s i := by
  sorry

end AlgebraicGeometry.Scheme.Modules
