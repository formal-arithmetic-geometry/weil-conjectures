/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Flat opcycles from universal ordinary tensor exactness

Source: Stacks Project, Cohomology on Sites, Tag 08G0, cokernel-flatness argument;
the universal ordinary-tensor version is the local diagram chase in the DAG node
(blueprint: lem-weil-pbc-site-flat-opcycles-tor-criterion).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing totalization coproducts through ringedSiteModules needs more search steps.
set_option synthInstance.maxSize 512 in
/-- Universal exactness of ordinary tensor in degree `n - 1` makes the opcycles in
 degree `n` flat. The test sheaf is placed in degree zero, and `mapBifunctor` is the
 direct-sum total tensor complex, with the recorded sheaf tensor product.

Source: Stacks Project, Tag 08G0, cokernel/Tor argument, generalized by the node's
local diagram chase (blueprint: lem-weil-pbc-site-flat-opcycles-tor-criterion).

Proof:
1. Write `R = P^{n-2}`, `B = P^{n-1}`, `D = P^n`, and `Q = coker(B → D)`.
Tensoring a degree-zero sheaf gives `N ⊗ P` with differential `1 ⊗ d`. By symmetry,
the hypothesis is exactness of `R ⊗ N → B ⊗ N → D ⊗ N` for every `N`.
2. The tensor-Hom adjunction of `lem-pc-sheaf-modules-tensor-closed` shows that
 tensor preserves cokernels and epimorphisms. Thus `B ⊗ N → D ⊗ N → Q ⊗ N → 0`
 is exact for every `N`, without a flatness assumption on `N`.
3. By `lem-weil-pbc-module-sheaves-colimits-forgetful` and
 `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`, epimorphisms of module
 sheaves admit local section lifts. Exactness gives local preimages of sections
 in kernels. Kernels are sectionwise; monomorphisms are sectionwise injective.
4. For a short exact sequence `0 → N₁ → N₂ → N₃ → 0`, locally lift a section
 `x` of `Q ⊗ N₁` killed in `Q ⊗ N₂` to `y` in `D ⊗ N₁`. The image of `y` in
 `D ⊗ N₂` locally lifts to `z` in `B ⊗ N₂` by step 2.
5. The image of `z` in `B ⊗ N₃` is a cycle. By step 1 it locally equals `d w`
 for `w` in `R ⊗ N₃`. Lift `w` locally to `R ⊗ N₂` using step 2 and subtract
 its boundary from `z`. The corrected `z₀` maps to zero in `B ⊗ N₃` and has
 the same image as `z` in `D ⊗ N₂`.
6. Flatness of `B` lifts `z₀` locally from `v` in `B ⊗ N₁`. Flatness of `D`
 makes `D ⊗ N₁ → D ⊗ N₂` monic, so `d v = y`. Hence `x = 0` locally, and
 sheaf separatedness gives `x = 0`. Thus `Q ⊗ N₁ → Q ⊗ N₂` is monic.
7. Step 2 and step 6 show preservation of every short exact sequence. Factor
 an arbitrary exact pair through its image and kernel to deduce preservation
 of all exact pairs. Together with right exactness this makes `Q ⊗ -` exact;
 symmetry makes `- ⊗ Q` exact, which is `IsFlat Q`.
-/
theorem isFlat_opcycles_of_universal_tensor_exactAt
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (P : CochainComplex
      (ringedSiteModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ)
    (hflat : ∀ i : ℤ, IsFlat (R := O) (P.X i)) (n : ℤ)
    (hexact : ∀ N : ringedSiteModules
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O),
      (CochainComplex.mapBifunctor ((CochainComplex.singleFunctor _ 0).obj N) P
        (@curriedTensor _ _ (monoidalCategory O))).ExactAt (n - 1)) :
    IsFlat (R := O) (P.opcycles n) := by
  classical
  let := monoidalCategory O
  let := symmetricCategory O
  let : MonoidalPreadditive (ringedSiteModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    Classical.choice (tensorClosed O).1
  let : MonoidalClosed (ringedSiteModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    Classical.choice (tensorClosed O).2.1
  -- Symmetry converts the one-sided sheaf definition to categorical flatness.
  have hcatflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
    have : Limits.PreservesFiniteLimits (tensorRight (P.X i)) := (hflat i).1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Limits.preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (P.X i)).symm)
  -- A degree-zero test complex gives termwise tensor, then symmetry swaps factors.
  have hterm (N : ringedSiteModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (n - 1) := by
    let e₁ := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) N P
    let e₂ := (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight N) (.up ℤ)).app P
    exact (hexact N).of_iso (e₁ ≪≫ e₂)
  -- The generic Tor criterion already contains the abelian diagram chase.
  exact (ObjectProperty.flat_opcycles_of_exactAt P n (hcatflat _) (hcatflat _) hterm).2

end SheafOfModules
