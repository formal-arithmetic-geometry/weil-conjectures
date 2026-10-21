/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-!
# Flat scalar restriction preserves K-flat complexes

Source: Stacks Project, Cohomology on Sites, Tag 06YN and the scalar-change argument
underlying Tag 06YY; Modules on Sites, Tags 03EK and 03ER.
(blueprint: lem-weil-pbc-flat-scalar-restriction-kflat)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace SheafOfModules

/-- Restriction along a flat map of commutative ring sheaves preserves K-flatness of
possibly unbounded complexes, and preserves flatness of their terms.
Source: Stacks Project, Tags 06YN, 06YY (scalar-change context), 03EK and 03ER.
(blueprint: lem-weil-pbc-flat-scalar-restriction-kflat).

Proof:
1. Write U for scalar restriction. Its composite with forgetting to abelian sheaves is
   the forgetful functor over B. By lem-weil-pbc-module-sheaves-colimits-forgetful both
   forgetful functors are faithful and exact and preserve small direct sums. Faithfulness
   detects zero objects, so they detect exactness. Thus U is exact, preserves and reflects
   acyclicity, and preserves small direct sums with their induced scalar action.
2. Write E(M) = M tensor_R B for scalar extension. By
   lem-weil-pbc-extension-tensor-comparison and lem-pc-sheaf-modules-tensor-closed,
   U(E(M)) is M tensor_R U(B). This is natural in M: both maps send a local pure tensor
   m tensor b to f(m) tensor b, and maps out of module sheafification are determined by
   their composites with the unit (def-weil-presheaf-modules-sheafification). Flatness of
   U(B), and detection of exactness by U, make E exact. Hence E sends every acyclic
   R-complex A to an acyclic B-complex, by lem-weil-pbc-exact-functor-complex-cohomology.
3. Construct inverse balanced sheaf maps M tensor_R U(N) and U(E(M) tensor_B N), by
   m tensor n mapping to (m tensor 1) tensor n and (m tensor b) tensor n mapping to
   m tensor bn. Give the first tensor its B-action by sheafifying the presheaf tensor
   with c(m tensor n) = m tensor cn. The action extends uniquely by
   lem-pc-sites-module-sheafification-interface. The first map is B-linear by uniqueness
   through this unit. Use lem-pc-sites-module-sheafification-bilinear-extension for the
   inner sheafification and lem-pc-sites-sheaf-tensor-bilinear-universal for the outer
   tensor. Balancing proves the inverse identities and naturality in both M and N.
4. Apply these maps to every summand indexed by p + q = n. Since U preserves direct
   sums, they give Tot(A tensor_R U(P)) isomorphic to U(Tot(E(A) tensor_B P)). The
   differential square commutes: both images of a tensor x are
   (d_A(a) tensor 1) tensor x + (-1)^p (a tensor 1) tensor d_P(x).
   Equality on local pure tensors, followed by the coproduct universal property, proves
   this for the sheaf tensors and their direct-sum totalizations, including unbounded ones
   (def-pc-tensor-complex-sheaves).
5. For every acyclic A, E(A) is acyclic by step 2. K-flatness of P makes its total
   tensor with E(A) acyclic. Exact U and step 4 make Tot(A tensor_R U(P)) acyclic.
   Quantification over A is precisely def-pc-kflat-complex for U(P).
6. If P.X q is flat over B, apply E, tensor_B P.X q, and then U to any short exact
   R-module sequence. Each operation is exact. Naturality of step 3 identifies this with
   tensor_R U(P.X q), proving flatness by def-pc-flat-sheaf-modules. This does not infer
   termwise flatness from K-flatness. -/
theorem isKFlat_restrictScalars_of_flat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{w}} (φ : R ⟶ B)
    (hB : IsFlatOnSite (J := J) (R := R)
      ((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj
          (unit (J := J) ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))))
    (P : CochainComplex
      (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ∧
    ((∀ q : ℤ, IsFlatOnSite (J := J) (R := B) (P.X q)) →
      ∀ q : ℤ, IsFlatOnSite (J := J) (R := R)
        ((restrictScalars.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj (P.X q))) := by
  sorry

end SheafOfModules
