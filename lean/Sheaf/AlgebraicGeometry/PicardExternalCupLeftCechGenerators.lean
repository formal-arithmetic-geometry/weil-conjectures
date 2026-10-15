/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupLeftCechExact
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.AlgebraicGeometry.PicardLeftCechCupHomology
import Sheaf.Algebra.Homology.TensorKunnethNat

/-! # External Cech cup on the factor homology generators

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-external-cup-left-cech-generators).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct DirectSum
namespace AlgebraicGeometry.Scheme.Modules

/-- The natural Cech cup has the external-cup formula on each pure factor-homology
 tensor in Kunneth coordinates. No scalar-total cochain map is an input, and no
 assertion about its homology map is made.

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech and the
functoriality sentence immediately after it; Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-picard-external-cup-left-cech-generators).

Proof: Refine the pullbacks of the finite affine covers to their product cover.
Apply the tensor-pullback adjunction units on sections, restrict to the front and
back intersections, and tensor the resulting sections. The Cech cup Leibniz rule
makes these maps on the bidegree summands into a map from the tensor total to the
product Cech complex. Restrictions and units commute with every coefficient
morphism, giving theta on all modules; extend the natural complexes by zero.
For quasi-coherent F, affine diagonals make the factor intersections affine.
The product intersections are affine products of such opens. Pullback and tensor
preserve quasi-coherence. Affine Cech comparison and exact scalar restriction,
followed by the fixed resolution comparison, give the product homology iso b and
factor homology isos from the scalar models to the extended Cech complexes.
Apply field tensor Kunneth to the two extended Cech complexes and precompose its
isomorphism with the direct sum of the tensors of these factor isos to obtain e.
For x and y, lift their images in factor Cech homology to cycles (the homology
projections are surjective). The Kunneth cycle formula represents e of their
pure tensor by the total tensor cycle. Refinement compatibility identifies its
image under theta with pullback of the factor classes followed by Cech cup.
Cech cup comparison identifies this with sheaf cup; the scalar Ext comparisons
identify (-1)^(p*q) times its compared image with externalCup. This proves
the generator
formula, with the cast implementing p+q=n. This uses neither invertibility of
external cup nor any normalization or existence of scalar-total cochain maps.
For zero coefficients or empty schemes all relevant spaces are zero. Degree zero
has the single summand (0,0), with the ordinary section pairing. -/
theorem picardExternalCup_left_cech_generators
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (G : Y.Modules) [G.IsQuasicoherent] :
    ∃ θ : picardLeftTensorCechFunctor f g G ⟶ picardLeftProductCechFunctor f g G,
      ∀ (F : X.Modules) (_ : F.IsQuasicoherent) (n : ℕ),
        ∃ (e : (⨁ i : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
              (picardScalarModel f F).homology (i.val.1 : ℤ) ⊗[k]
                (picardScalarModel g G).homology (i.val.2 : ℤ)) ≃ₗ[k]
              ((picardLeftTensorCechFunctor f g G).obj F).homology (n : ℤ))
          (b : ((picardLeftProductCechFunctor f g G).obj F).homology (n : ℤ) ≅
            (picardScalarModel (pullback.fst f g ≫ f)
              (externalCupCoefficients f g F G)).homology (n : ℤ)),
          ∀ (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
            (x : (picardScalarModel f F).homology (i.val.1 : ℤ))
            (y : (picardScalarModel g G).homology (i.val.2 : ℤ)),
            (-1 : ℤ) ^ (i.val.1 * i.val.2) •
              picardScalarModelEquiv (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) n
              (b.hom (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)
                (e (DirectSum.lof k _ _ i (x ⊗ₜ[k] y))))) =
              cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
                (externalCupCoefficients f g F G) d)) i.property)
                (externalCup f g F G i.val.1 i.val.2
                  (picardScalarModelEquiv f F i.val.1 x)
                  (picardScalarModelEquiv g G i.val.2 y)) := by
  obtain ⟨θ, hθ⟩ := picardLeftCechCup_exists f g G
  refine ⟨θ, ?_⟩
  intro F hF n
  let A := picardScalarModel f F
  let B := picardScalarModel g G
  obtain ⟨a, b, hab⟩ := picardLeftCechCup_homology f g G θ hθ F
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat A B
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  refine ⟨e.trans (a n).symm.toLinearEquiv, b n, ?_⟩
  intro i x y
  obtain ⟨u, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ _)).mp inferInstance x
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ _)).mp inferInstance y
  obtain ⟨z, hz, hez⟩ := he i u v
  change (-1 : ℤ) ^ (i.val.1 * i.val.2) •
    picardScalarModelEquiv (pullback.fst f g ≫ f)
    (externalCupCoefficients f g F G) n
    ((b n).hom (HomologicalComplex.homologyMap (θ.app F) (n : ℤ)
      ((a n).inv (e (DirectSum.lof k _ _ i
        ((A.homologyπ _ u) ⊗ₜ[k] (B.homologyπ _ v))))))) = _
  rw [hez]
  exact hab n i u v z hz

end AlgebraicGeometry.Scheme.Modules
