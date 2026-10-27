/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison

/-! # Flat base change along a quasi-isomorphism of simplicial rings

Source: Stacks Project, Tags 08RX and 08QD.
(blueprint: lem-sfb-simplicial-flat-base-change-quasi-iso).

Simplicial modules over a varying ring are Mathlib presheaves of modules on Delta.
The tensor below is Mathlib's degreewise tensor, before forgetting to abelian groups.
The cochain convention is the existing alternating complex in nonpositive degrees.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Simplicial
open scoped TensorProduct

namespace Algebra.SimplicialFlatBaseChange

/-- The target ring regarded as a simplicial module over the source ring.
This is restriction of scalars of the rank-one target module, with no flatness
assumption on the target ring. Source: Stacks, Tags 08RX and 08QD
(blueprint: lem-sfb-simplicial-flat-base-change-quasi-iso). -/
def scalarModule {R S : SimplicialObject CommRingCat.{u}} (f : R ⟶ S) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight f (forget₂ CommRingCat RingCat))).obj
      (PresheafOfModules.unit (S ⋙ forget₂ CommRingCat RingCat))

/-- The canonical map of underlying simplicial abelian groups, `x ↦ x ⊗ 1`.
The target has terms `M_n ⊗[R_n] S_n`; its operators apply the two given
simplicial operators to the tensor factors. Source: Stacks, Tags 08RX and 08QD
(blueprint: lem-sfb-simplicial-flat-base-change-quasi-iso). -/
def baseChangeMap {R S : SimplicialObject CommRingCat.{u}} (f : R ⟶ S)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    M.presheaf ⟶ (PresheafOfModules.Monoidal.tensorObj M (scalarModule f)).presheaf where
  app X := AddCommGrpCat.ofHom
    (((TensorProduct.mk (R.obj X) (M.obj X) ((scalarModule f).obj X)).flip
      (1 : S.obj X)).toAddMonoidHom)
  naturality X Y g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change TensorProduct.mk (R.obj Y) (M.obj Y) ((scalarModule f).obj Y)
      (M.map g x) (1 : S.obj Y) =
      (PresheafOfModules.Monoidal.tensorObj M (scalarModule f)).map g
        (TensorProduct.mk (R.obj X) (M.obj X) ((scalarModule f).obj X)
          x (1 : S.obj X))
    dsimp [PresheafOfModules.Monoidal.tensorObj,
      PresheafOfModules.Monoidal.tensorObjMap, PresheafOfModules.presheaf]
    change TensorProduct.mk (R.obj Y) (M.obj Y) ((scalarModule f).obj Y)
      (M.map g x) (1 : S.obj Y) =
      TensorProduct.mk (R.obj Y) (M.obj Y) ((scalarModule f).obj Y)
        (M.map g x) ((scalarModule f).map g (1 : S.obj X))
    change _ = TensorProduct.mk (R.obj Y) (M.obj Y) ((scalarModule f).obj Y)
      (M.map g x) (S.map g 1)
    rw [show S.map g (1 : S.obj X) = (1 : S.obj Y) from (S.map g).hom.map_one]

/-- Degreewise flat simplicial modules preserve a quasi-isomorphism of varying
simplicial rings under ordinary scalar extension. Source: Stacks, Tag 08RX
(lemma-O-homology-qis), interpreted by Tag 08QD (remark-simplicial-modules).
(blueprint: lem-sfb-simplicial-flat-base-change-quasi-iso).

Proof:
1. Regard Delta with identity-cover topology as a ringed site. Its module sheaves
   are precisely the given presheaves of modules, and flatness is degreewise.
2. Resolve M by sums of free Yoneda modules (lem-weil-pbc-free-yoneda-presheaf-module).
3. The terms of that resolution are flat (lem-weil-pbc-projective-module-flat).
   Flat kernels and tensor exactness follow from
   lem-weil-pbc-site-flat-quotient-tensor-ses and lem-weil-pbc-flat-tensor-exact.
4. Base change takes a free generator at [m] to the same generator over S.
5. By lem-sfb-simplicial-simplex-copower-contraction, the alternating complex of
   the free generator over R, respectively S, is homotopy equivalent to s(R),
   respectively s(S). The augmentation square commutes. Thus its base-change
   map in the derived category is the composite of the R augmentation, s(f),
   and the inverse S augmentation, and is invertible by the hypothesis on s(f).
6. Direct sums preserve this quasi-isomorphism, giving it on each resolution term.
7. Form the two first-quadrant bicomplexes of alternating chains of the resolution.
   Exactness in the resolution direction and the flat-quotient tensor result
   show that their augmentations to s(M) and s(M tensor_R S) are quasi-isomorphisms,
   by lem-sc-first-quadrant-total-column-comparison. No transpose is needed here:
   its fixed second index columns are the resolution complexes.
8. Transpose the bicomplexes to apply the same comparison to the maps from Step 6.
   The signed transpose isomorphism multiplies bidegree (p,n) by (-1)^(pn),
   so the induced original-total map is a quasi-isomorphism as well.
9. The augmentation square identifies the resulting comparison with x ↦ x tensor 1.
   Two-out-of-three proves the assertion. Reindexing n to -n gives the stated
   nonpositive cochain complexes (def-weil-abstract-derived-category). -/
theorem quasiIso_baseChangeMap
    {R S : SimplicialObject CommRingCat.{u}} (f : R ⟶ S)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (hflat : ∀ n : ℕ, Module.Flat (R.obj (op ⦋n⦌)) (M.obj (op ⦋n⦌)))
    (hf : QuasiIso ((CotangentResolution.negativeComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight f (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)))) :
    QuasiIso ((CotangentResolution.negativeComplex AddCommGrpCat.{u}).map
      (baseChangeMap f M)) := by
  sorry

end Algebra.SimplicialFlatBaseChange
