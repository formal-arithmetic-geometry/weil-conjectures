/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A prescribed completed comparison lifts to a map on any common open.
Only a map is asserted: invertibility and all cocycle identities are consequences
of section separation, proved in the parent module.
Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness.
(blueprint: lem-weil-pbc-torsion-common-open-comparison-map).

Proof: Transfer Li and Lj through overEquiv and restrict Fi, Fj and H to W.
Coherence, kernels, cokernels and their ideal-power annihilation bounds restrict
along these open immersions. Use the normalized quotient restriction comparison
and beta_i, beta_j to identify their completions with N restricted to W.
The prescribed completed map is beta_i inverse followed by beta_j, with those
restriction comparisons. The equations hdelta show it commutes with the maps to
the completion of H: precompose each component with the quotient epimorphism
and use hqi and hbi. Apply torsionControlled_completion_hom_lift_exists on W.
Transfer the resulting map back through overEquiv. Its equation over H yields
the b equation on each V contained in W. Its completed equation, precomposed
with the source quotient projection and rewritten using hqi, yields the q
equations. This uses arbitrary open restrictions, not affine intersections.
For J=0 the completed comparison is the original map. For J=1 both arrows to
H are isomorphisms and the comparison is their composite. On an empty common
open the unique map suffices; the index type may also be empty.
-/
theorem torsion_common_open_comparison_map
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (hbound : ∀ i, ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel (ai i).hom)) ∧
      IsZero (Scheme.idealModuleProduct
        (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel (ai i).hom)))
    (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (hbi : (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom))
    (hqi : (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n))
    (hδ : (∀ (i : ι) (n : ℕᵒᵖ), qi i n ≫ (δ.hom.app n).over (U i) =
        bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)))
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    ∃ f : (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hi : W ⟶ U i)).obj (Li i) ⟶
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hj : W ⟶ U j)).obj (Li j),
      (∀ (V : X.Opens) (hV : V ≤ W),
        f.val.app (op (Over.mk (homOfLE hV))) ≫
          (bi j).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
            (bi i).val.app (op (Over.mk (homOfLE (hV.trans hi))))) ∧
      (∀ (n : ℕᵒᵖ) (V : X.Opens) (hV : V ≤ W),
        f.val.app (op (Over.mk (homOfLE hV))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE (hV.trans hj)))) =
            (qi i n).val.app (op (Over.mk (homOfLE (hV.trans hi))))) := by sorry

end AlgebraicGeometry
