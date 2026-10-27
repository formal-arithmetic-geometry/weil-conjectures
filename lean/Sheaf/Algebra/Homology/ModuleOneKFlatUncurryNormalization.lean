/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.ModuleHomComplexDerivedComparison
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.OneKFlatChainTranspose
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Ordinary uncurrying on one-K-flat representatives

Source: Stacks Project, More on Algebra, Tag 0A65, lemma-internal-hom and
its proof, together with equation-internal-hom.
(blueprint: lem-trf-module-one-kflat-uncurry-normalization)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CochainComplex

/-- The derived right-tensor transpose agrees with ordinary uncurrying when either
factor is K-flat and the target is K-injective. The inverse of the one-K-flat
comparison is exactly the native localization tensorator `μ`, so it is written
without introducing an inverse or a second tensor comparison. The right-tensor
transpose is left currying after the native Koszul braiding. The existing
`moduleHomComplexDerivedComparison` is the canonical Hom representative map, normalized
by evaluation (and invertible for a K-injective target).

Source: Stacks Project, Tag 0A65, proof and equation-internal-hom.
(blueprint: lem-trf-module-one-kflat-uncurry-normalization)

Proof:
1. Choose flat-term K-flat resolutions F -> U and P -> V using
   lem-pc-kflat-resolution on the punctual ringed site.
2. Precompose phi by Hom(P -> V,I), and psi by 1_U tensor (P -> V).
   Actual product projections show the new maps satisfy the same pure-tensor
   equation. Tensor currying and the direct-sum universal property give ordinary
   uncurrying without a sign or a factor interchange.
3. Apply lem-sfb-hom-kflat-chain-transpose to (U,P,I). Identify its normalized
   tensor comparison with the native one by lem-sf-ringed-derived-tensor-hom-adjunction
   on (F,P), then by naturality and cancellation along F -> U on (U,P).
4. The tensor square commutes by lem-sf-ringed-derived-native-tensor. The Hom
   square commutes by functoriality; lem-pur-rhom-well-defined makes the Hom map
   induced by P -> V invertible, since the target I is K-injective.
5. Naturality of the right-tensor adjunction in its second variable identifies
   both composites after RHom(Q(P -> V),1). Cancel this isomorphism to obtain the
   displayed equation. Either K-flat disjunct suffices to invert the tensorator
   at (U,V); no termwise flatness or boundedness of U or V is used. -/
theorem module_oneKFlat_uncurry_normalization
    (R : Type u) [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (U V I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (hflat : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat U ∨
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat V)
    (φ : U ⟶ moduleHomComplex V I) (ψ : U ⊗ V ⟶ I)
    (huncurry : ∀ (p q : ℤ) (x : U.X p) (y : V.X q),
      ψ.f (q + p)
          ((HomologicalComplex.ιTensorObj U V p q (q + p) (Int.add_comm p q))
            (x ⊗ₜ[R] y)) =
        (((φ.f p) x).v q (q + p) rfl) y) :
    MonoidalClosed.curry
        ((@id (DerivedCategory.Q.obj V ⊗ DerivedCategory.Q.obj U ≅
            DerivedCategory.Q.obj U ⊗ DerivedCategory.Q.obj V)
          (DerivedMonoidal.braiding' DerivedCategory.Qh
          (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
          (DerivedCategory.Q.obj V) (DerivedCategory.Q.obj U))).hom ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q U V ≫ DerivedCategory.Q.map ψ) =
      DerivedCategory.Q.map φ ≫ ModuleCat.moduleHomComplexDerivedComparison V I := by
  sorry

end CochainComplex
