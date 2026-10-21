/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportData
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# K-flat comparison of actual ordinary etale support sequences

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality, expanded by the agent-written
support diagram; Stacks Tags 03DB, 03ER, 06YU, 07A4, 0FPI, 0152 and 014A
(blueprint: lem-pur-etale-kflat-support-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] HomologicalComplex.monoidalCategoryStruct
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.leftAdjoint Functor.rightAdjoint Functor.leftDerivedFunctor
  upperStar lowerStar closedUpperShriek ProEtale.pbcFixedScalarExtension
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh


variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}

/-- The actual support comparison: short exact rows, the kernel-induced chain map,
the complete distinguished-triangle diagram, and its coefficient-projection normalization.
Any functorial degreewise-injective K-injective replacement F with quasi-isomorphism η
is allowed. No B-action on Q, I or F is part of the data.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality (agent-written support diagram);
Stacks 03DB, 03ER, 06YU, 07A4, 0FPI, 0152, 014A
(blueprint: lem-pur-etale-kflat-support-comparison).

Proof:
1. Put S=i_*H_A(I), C=j_*j^*I and likewise S',C' for J. The actual support rows
   are short exact by lem-pur-etale-injective-support-sequence. The fixed-K-flat
   tensor computation identifies Q tensor I and Q tensor C with the derived tensors
   (lem-weil-pbc-kflat-fixed-tensor-triangulated). Signed symmetry puts B second;
   lem-pur-etale-scalar-mate-projection identifies this with restricted scalar extension.
   Use the inverse of Q(a) to identify J with the same middle object.
2. Tensor each degree-q support row by the flat sheaf Q^p
   (def-pc-flat-sheaf-modules). Sum over p+q=n. Each finite subsum is exact, and the
   full sum is its filtered colimit, hence exact by lem-pc-module-filtered-colimits-tensor.
   Both differential terms d_Q tensor 1 and (-1)^p 1 tensor d respect the row.
3. Form the cochain adjunct of the tensor/pullback comparison followed by 1 tensor
   the open counit and j^*a. Its summand characterization is IsRightMap;
   the ordinary cochain adjunction and
   lem-pur-cochain-pullback-tensor-coherence supply its signs and naturality.
   No commutation of j_* with infinite sums is used.
4. Transpose the right square. Both transposes equal j^*a by the ordinary triangle
   identity and tensor-comparison naturality. Thus a sends the top kernel into S'.
   The kernel universal property gives the unique first map and its chain-map equation.
   Naturality in chain maps follows by cancellation of the monomorphism S'→J.
5. Apply lem-weil-pbc-complex-ses-triangle to the strict diagram of short exact rows.
   Its canonical boundary is natural, yielding the third triangle square, with its sign.
   The middle map is the identity under tensorModel and replacementIso.
6. Compute the transpose of the localized quotient map using
   lem-sp-etale-derived-chain-transpose and its counit equation at j^*I. K-flat
   inverse image and tensor coherence identify it with the defining projection-formula
   transpose (lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   def-kun-projection-formula-map). This identifies maps, not just their objects.
7. Apply lem-pur-etale-scalar-mate-projection at j^*L. Exact inverse image preserves
   the bounds on L and TL; the bound on T Rj_*j^*L is the remaining source bound.
   The bounded-below direct-image/restriction comparison from
   lem-sbc-canonical-restrict-scalars-functor-comparisons identifies the result with
   restrictedProjection. No B-injective is assumed injective after scalar restriction.
8. If coefficientProjection is invertible, its restriction and the bounded-below
   comparisons are invertible. The middle identity and the triangle two-isomorphisms
   lemma lem-sf-triangle-morphism-iso make the first map invertible. Naturality of η,
   the unique kernel map, and the SES boundary gives naturality of the entire diagram. -/
theorem etale_kflat_support_comparison [Finite A] [Finite B]
    (φ : A →+* B) (i : Z ⟶ P) [IsClosedImmersion i]
    (j : U ⟶ P) [IsOpenImmersion j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : _root_.DerivedCategory.Plus (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hTL : ∃ n : ℤ, ((scalarExtension φ P).obj L.obj).IsGE n)
    (_hRTL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} B) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} B) j)).obj
        ((scalarExtension φ P).obj L.obj))).IsGE n)
    (_hRL : ∃ n : ℤ, ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj)).IsGE n)
    (_hTRL : ∃ n : ℤ, ((scalarExtension φ P).obj
      ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L.obj))).IsGE n)
    (I : Complex A P) [I.IsKInjective] [∀ n : ℤ, Injective (I.X n)]
    (e : (localize A P).obj I ≅ L.obj)
    (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (_hQf : ∀ n : ℤ, ObjectProperty.flat (Q.X n))
    (F : Complex A P ⥤ Complex A P) (η : 𝟭 _ ⟶ F)
    [∀ K : Complex A P, (F.obj K).IsKInjective]
    [∀ (K : Complex A P) (n : ℤ), Injective ((F.obj K).X n)]
    [∀ K : Complex A P, QuasiIso (η.app K)] :
    let N := Q ⊗ I
    let J := F.obj N
    let a := η.app N
    let S := totalTensorSequence Q (etaleSupportSequence A i j hij I)
    let S' := etaleSupportSequence A i j hij J
    ∃ (hI : CochainComplex.IsKInjective
        ((pullComplex A j).obj I))
      (hJ : CochainComplex.IsKInjective
        ((pullComplex A j).obj J))
      (hTop : S.ShortExact)
      (hBottom : S'.ShortExact)
      (m : S ⟶ S'),
      m.τ₂ = a ∧
      IsRightMap j Q I J a m.τ₃ ∧
      (∀ m' : S ⟶ S',
        m'.τ₂ = a →
        IsRightMap j Q I J a m'.τ₃ → m' = m) ∧
      _root_.DerivedCategory.triangleOfSES hTop ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSES hBottom ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSESδ hTop ≫
          ((localize A P).map m.τ₁)⟦1⟧' =
        (localize A P).map m.τ₃ ≫ _root_.DerivedCategory.triangleOfSESδ hBottom ∧
      (tensorModel φ Q π hQ I L.obj e).inv ≫ (localize A P).map m.τ₂ ≫
          (replacementIso a (tensorModel φ Q π hQ I L.obj e)).hom =
        𝟙 _ ∧
      (localize A P).map m.τ₃ ≫
          (targetThirdModel φ j J L.obj
            (replacementIso a (tensorModel φ Q π hQ I L.obj e)) hJ).hom =
        (sourceThirdModel φ j Q π hQ I L.obj e hI).hom ≫ restrictedProjection φ j L.obj ∧
      (IsIso ((localize A P).map m.τ₃) → IsIso ((localize A P).map m.τ₁)) ∧
      (∀ (I' : Complex A P) (f : I ⟶ I'),
        let N' := Q ⊗ I'
        let J' := F.obj N'
        let a' := η.app N'
        let S₁ := totalTensorSequence Q (etaleSupportSequence A i j hij I')
        let S₂ := etaleSupportSequence A i j hij J'
        let s : S ⟶ S₁ := totalTensorSequenceMap Q (etaleSupportSequenceMap A i j hij f)
        let t : S' ⟶ S₂ := etaleSupportSequenceMap A i j hij (F.map ((tensorLeft Q).map f))
        ∀ m' : S₁ ⟶ S₂, m'.τ₂ = a' → IsRightMap j Q I' J' a' m'.τ₃ →
          s ≫ m' = m ≫ t) := by
  sorry

attribute [instance] HomologicalComplex.monoidalCategoryStruct

end AlgebraicGeometry.Etale.KFlatSupportComparison
