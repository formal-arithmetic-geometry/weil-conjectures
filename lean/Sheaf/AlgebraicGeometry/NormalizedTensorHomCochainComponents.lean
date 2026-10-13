/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedTensorHomCochains
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

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
  sorry

end AlgebraicGeometry
