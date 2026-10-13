/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.PicardRightCechCupConstruction
public import Sheaf.AlgebraicGeometry.PicardExternalCupHomologyUnique
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators
import Sheaf.Algebra.Homology.TensorKunnethNat

/-! # Affine Cech comparison of the external cup formula

Source: Stacks Project, Varieties, Tag 0BED; Cohomology, Tags 01FD and 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-homology).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The specified Cech cup coordinates transport to the external tensor-cycle formula.
No normalized scalar-model cochain map or coefficient sequence is an input or output.
Source: Stacks, Tag 0BED, equation-kunneth-on-cech; Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-right-cech-cup-homology).

Proof: All nonempty finite intersections of the affine factor covers are affine
by the affine diagonal criterion. The product cover covers the fibre product;
its intersections are the fibre products of the corresponding factor affine
intersections over Spec k, hence affine. Pullback and tensor preserve
quasi-coherence. Apply the canonical affine Cech comparisons to both factors
and the external coefficient on the product. Restriction of scalars is exact
and commutes with the finite products forming the Cech terms, so these comparisons
are k-linear comparisons for the scalar Cech complexes. Compose the product
comparison with the inverse of the fixed resolution comparison and the extension
homology isomorphism to obtain b. For a, use tensor Kunneth for the factor Cech
complexes and the scalar resolution complexes, tensoring the factor comparisons
on each direct-sum summand. The canonical comparison of the extended natural
total with the total of the extended complexes identifies their summand cycles.
On a pair of factor cycles, the prescribed front/back tuple coordinates are the
refinement maps along the two projections followed by Cech cup. Compatibility
of refinement with pullback and Cech cup with sheaf cup identifies its image under
b with externalCup of the factor classes. The factor comparisons in a give these
same classes for the scalar-model tensor cycle. Lift factor homology classes
through their surjective homology projections; tensor Kunneth and pure-tensor
spanning extend this identity to every tensor-cycle representative in the stated
normalization predicate. No invertibility of external cup is used. Empty covers
force the corresponding schemes to be empty and all affected cohomology groups
to vanish; zero coefficients and degree zero satisfy the same formulas. -/
theorem picardRightCechCup_homology
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) [F.IsQuasicoherent]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUc : iSup U = ⊤) (hVc : iSup V = ⊤)
    (θ : picardRightTensorCechFunctor f g U V F ⟶
      picardRightProductCechFunctor f g U V F)
    (hθ : IsPicardRightCechCup f g U V F θ)
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ (a : ∀ n : ℕ,
        ((picardRightTensorCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardExternalTotal f g F G).homology (n : ℤ))
      (b : ∀ n : ℕ,
        ((picardRightProductCechFunctor f g U V F).obj G).homology (n : ℤ) ≅
          (picardScalarModel (pullback.fst f g ≫ f)
            (externalCupCoefficients f g F G)).homology (n : ℤ)),
      IsPicardExternalCupHomology f g F G (fun n ↦
        (a n).inv ≫ HomologicalComplex.homologyMap (θ.app G) (n : ℤ) ≫ (b n).hom) :=
  by
    classical
    let A := picardScalarModel f F
    let B := picardScalarModel g G
    let T := picardExternalTotal f g F G
    have hg := fun n ↦ picardRightCechCup_generators f g F U V hU hV hUc hVc θ hθ G n
    choose e b he using hg
    have hk := fun n ↦ HomologicalComplex.tensor_kunneth_nat A B
      (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
    choose s hs using hk
    let a := fun n ↦ ((e n).symm.trans (s n)).toModuleIso
    refine ⟨a, b, ?_⟩
    intro n i x y z hz
    obtain ⟨z', hz', hsz'⟩ := hs n i x y
    have hzz : z' = z := by
      apply (ModuleCat.mono_iff_injective (T.iCycles (n : ℤ))).mp inferInstance
      exact hz'.trans hz.symm
    subst z'
    change s n (DirectSum.lof k _ _ i
      (TensorProduct.tmul k (A.homologyπ (i.val.1 : ℤ) x)
        (B.homologyπ (i.val.2 : ℤ) y))) = T.homologyπ (n : ℤ) z at hsz'
    have hpre : (a n).inv (T.homologyπ (n : ℤ) z) =
        e n (DirectSum.lof k _ _ i
          (TensorProduct.tmul k (A.homologyπ (i.val.1 : ℤ) x)
            (B.homologyπ (i.val.2 : ℤ) y))) := by
      rw [← hsz']
      change e n ((s n).symm (s n _)) = _
      rw [LinearEquiv.symm_apply_apply]
    change picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n
      ((b n).hom (HomologicalComplex.homologyMap (θ.app G) (n : ℤ)
        ((a n).inv (T.homologyπ (n : ℤ) z)))) = _
    rw [hpre]
    exact he n i (A.homologyπ (i.val.1 : ℤ) x) (B.homologyπ (i.val.2 : ℤ) y)


end AlgebraicGeometry.Scheme.Modules
