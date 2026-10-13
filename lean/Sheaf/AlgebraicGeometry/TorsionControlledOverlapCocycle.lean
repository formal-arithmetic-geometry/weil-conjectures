/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentMapTorsionCompletionExt
import Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import Sheaf.AlgebraicGeometry.FormalSystemsPullback
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.TorsionControlledCompletionHomLiftExists
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The fixed local sources and normalized quotient maps admit compatible overlap isomorphisms.
All local objects and maps are supplied; only pairwise comparisons and their cocycle are built.

Source: Stacks Project, Tag 0889(1), uniqueness verification omitted at the end of the proof;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-overlap-cocycle).

Proof: On Ui intersect Uj transfer the supplied Li to the open subscheme and restrict
li, ai, and βi. Open restriction preserves coherence and actual kernels and cokernels.
Ideal powers and multiplication images restrict to those of the comapped ideal, so the
positive annihilation bounds remain valid on the intersection. Normalized quotient
comparison identifies the completed local sources with the same restriction of N.
Their induced maps to the restriction of H agree: compose the quotient projections
with these maps, use hδ, and cancel the quotient epimorphisms. Torsion-controlled
completion hom lifting gives a comparison and its inverse that respect the maps to H
and induce the prescribed completed comparison. Completion extensionality with the
map to H identifies both composites with identities. Transfer this isomorphism through
overEquiv to get θij. Its compatibility with bi is the lifting equation and its
compatibility with qi follows by precomposing the completion equation with quotientπ
and hqi. On every triple intersection both composite and direct comparisons induce
the same completed comparison and map to H. Extensionality makes them equal; evaluating
on every contained open gives the displayed cocycle. This argument applies to arbitrary
open intersections, without assuming they are affine. For J=0 completion is identity;
for J=1 the annihilation bounds make the arrows isomorphisms, so comparison is via H;
for the empty index type the conclusion is vacuous.
-/
theorem torsionControlled_overlap_cocycle
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
 :
    ∃ (θ : ∀ i j,
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Li i) ≅
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Li j)),
      (∀ (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
        (θ i k).hom.val.app (op (Over.mk (homOfLE (le_inf hi hk)))) =
          (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
            (θ j k).hom.val.app (op (Over.mk (homOfLE (le_inf hj hk))))) ∧
      (∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (bi j).val.app (op (Over.mk (homOfLE hj))) =
            (bi i).val.app (op (Over.mk (homOfLE hi)))) ∧
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE hj))) =
            (qi i n).val.app (op (Over.mk (homOfLE hi)))) := by sorry

end AlgebraicGeometry
