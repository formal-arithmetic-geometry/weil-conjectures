/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Change of rings preserves K-flat complexes with flat terms

Source: Stacks Project, Cohomology on Sites, Lemma 21.18.1, Tag 0G7E,
identity-topos coefficient-change case (blueprint: lem-pur-kflat-change-of-rings).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)

/-- Change of rings preserves K-flatness and flatness of every term.
Source: Stacks, Tag 0G7E (blueprint: lem-pur-kflat-change-of-rings).

Proof:
1. Restriction of scalars leaves underlying abelian sheaves unchanged. Kernels are
sectionwise and cokernels are sheafified sectionwise cokernels; thus restriction preserves
and reflects exactness and acyclicity (def-pc-sheaf-restrict-scalars,
def-weil-sheaf-of-modules-category).
2. For an R-module M and S-module N, the balanced maps n tensor (m tensor s) maps to
sn tensor m and n tensor m maps to n tensor (m tensor 1) give inverse natural maps
U(N tensor_S (M tensor_R S)) and UN tensor_R M. Construct them on presheaf tensor
generators, then extend by module sheafification and bilinear extension
(def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification,
lem-pc-sites-module-sheafification-bilinear-extension).
3. Restrict a short exact sequence of S-modules, tensor with K.X p, and use step 2.
Exactness of tensor with K.X p and reflection of exactness prove flatness of its change
of rings (Stacks, Tag 05V4).
4. Take direct sums of step 2 over a+b=n. Restriction commutes with these sheafified
sums of finite-support tuples. The resulting isomorphism of total complexes respects
the two differential terms, including the sign (-1)^a on the second term
(def-pc-tensor-complex-sheaves).
5. If F is acyclic over S, UF is acyclic over R. K-flatness of K makes Tot(UF tensor_R K)
acyclic. Steps 4 and 1 give acyclicity of Tot(F tensor_S (K tensor_R S)), which is
K-flatness of the changed complex (def-pc-kflat-complex). Combine with step 3. -/
theorem changeOfRings_isKFlat_of_flat_terms
    (hK : CochainComplex.IsAcyclicTensorKFlat K)
    (hflat : ∀ p : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (monoidalCategory R) (K.X p))) :
    CochainComplex.IsAcyclicTensorKFlat (changeOfRingsComplex φ K) ∧
      ∀ p : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (monoidalCategory S)
          ((changeOfRingsComplex φ K).X p)) := by
  sorry

end SheafOfModules
