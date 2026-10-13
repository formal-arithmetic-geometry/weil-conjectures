/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedTensorHomCochains
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomPureTensorExt
import Sheaf.Algebra.Homology.HomTensorCurryZero

/-! # The pure-tensor component calculation for ordinary cochains

Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochain-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry

private lemma normalized_projection_eq {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (A B : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k i j : ℤ) (h : i + k = j) :
    normalizedHomProjection (R := R) A B k i j h =
      homTensorProjection R A B k i j h := by rfl

private lemma normalized_factor_eval {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (A B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (t : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      SheafOfModules.homObj (R := R) A B)
    (U : Cᵒᵖ) (x : A.val.obj U) :
    ((normalizedHomFactorEquiv A B t).val.app U).hom x =
      (((t.val.app U).hom (1 : R.obj.obj U)).app
        (op (Over.mk (𝟙 U.unop)))).hom x := by rfl

set_option maxHeartbeats 800000 in
-- Comparing chosen Hom projections and the total tensor uses more than the default heartbeats.
/-- Restricting the explicitly constructed degree-zero uncurrying comparison
 to a tensor summand gives the inverse sheaf tensor-Hom adjunction.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochain-components).

Proof: put s equal to the inverse normalized global comparison applied to c.
The global comparison component formula identifies c's p-component with the
morphism corresponding to s followed by the p-product projection. On the
output side, the same formula identifies the displayed component with the
morphism corresponding to s followed by homTensorDegreewiseMap and the
n-product projection. Apply homTensorDegreewiseMap_spec. Its localized
pure-tensor equation says that this latter morphism, restricted to the
(p,r) summand, evaluates x tensor y as c's p-component at x, projected onto
the r-factor, evaluated at y. Expanding tensorHomEquiv through the presheaf
adjunction and sheafification gives this very evaluation for the right side:
the symmetry interchanges x and y and the inverse adjunction evaluates at y.
Naturality under restriction gives equality on every localized site, not
only on global pure tensors. Linear maps from the presheaf tensor are
determined by pure tensors; the sheafification adjunction determines maps
from the sheaf tensor by their presheaf pullbacks. Thus the sheaf morphisms
are equal. Only the degreewise pure-tensor specification and the explicit
global projection formula are used, with no differential, cocycle, or
homotopy assertion. Zero factors give zero morphisms; there is no finiteness
assumption because only a single coproduct summand is tested. -/
theorem normalizedTensorHomCochains_component (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (c : Cochain P (homComplex (R := X.sheaf) L I) 0)
    (p r n : ℤ) (h : p + r = n) (h' : r + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := SheafOfModules.symmetricCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p r n h ≫
        (normalizedTensorHomCochains X P L I 0 c).v n n (add_zero n) =
      (β_ (P.X p) (L.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (L.X r) (P.X p) (I.X n)).symm
          (c.v p p (add_zero p) ≫ homTensorProjection X.sheaf L I p r n h') := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let H := homComplex (R := X.sheaf) L I
  let s := (normalizedHomGlobalCochains X.sheaf P H 0).symm c
  have hc : c.v p p (add_zero p) =
      normalizedHomFactorEquiv (P.X p) (H.X p)
        (s ≫ homTensorProjection X.sheaf P H 0 p p (add_zero p)) := by
    have he := congrArg (fun d ↦ d.v p p (add_zero p))
      ((normalizedHomGlobalCochains X.sheaf P H 0).apply_symm_apply c)
    rw [normalizedHomGlobalCochains_v, normalized_projection_eq] at he
    exact he.symm
  change _ ≫ (normalizedHomGlobalCochains X.sheaf (pullbackTensorTotal X P L) I 0
    (s ≫ homTensorDegreewiseMap X.sheaf P L I 0)).v n n _ = _
  rw [normalizedHomGlobalCochains_v, normalized_projection_eq]
  apply SheafOfModules.tensorHom_of_pureTensor X.sheaf (P.X p) (L.X r) (I.X n)
  intro U x y
  rw [hc]
  have he := homTensorCurryCondition_zero X.sheaf P L I
    (homTensorDegreewiseMap X.sheaf P L I 0)
    (homTensorDegreewiseMap_spec X.sheaf P L I 0).1 p r U
    ((s.val.app U).hom (1 : X.sheaf.obj.obj U)) (op (Over.mk (𝟙 U.unop))) x y
  subst n
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [normalized_factor_eval X.sheaf, normalized_factor_eval X.sheaf]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  exact he

end AlgebraicGeometry
