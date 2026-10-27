/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportRows
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.AlgebraicGeometry.FlatSupportChainDiagram

import Sheaf.AlgebraicGeometry.EtaleKFlatSupportStrict
import Sheaf.AlgebraicGeometry.EtaleKFlatSupportProjection

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
attribute [-instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison


attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}


attribute [local irreducible] tensorModel sourceThirdModel targetThirdModel
  replacementIso restrictedProjection coefficientProjection scalarOpenIso restrictionOpenIso
  OpenSupport.rightMap etaleSupportSequence upperStarLowerStarAdjunction
  topSequenceFamily bottomSequenceFamily

private theorem finish_triangle {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C]
    {S T : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (m : S ⟶ T)
    [IsIso (_root_.DerivedCategory.Q.map m.τ₂)]
    [IsIso (_root_.DerivedCategory.Q.map m.τ₃)] :
    IsIso (_root_.DerivedCategory.Q.map m.τ₁) := by
  exact CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃
    (_root_.DerivedCategory.triangleOfSES.map hS hT m)
    (_root_.DerivedCategory.triangleOfSES_distinguished hS)
    (_root_.DerivedCategory.triangleOfSES_distinguished hT)
    (by change IsIso (_root_.DerivedCategory.Q.map m.τ₂); infer_instance)
    (by change IsIso (_root_.DerivedCategory.Q.map m.τ₃); infer_instance)
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
    let S := (topSequenceFamily A i j hij Q).obj I
    let N := Q ⊗ I
    let _J := F.obj N
    let a := η.app N
    let S' := (bottomSequenceFamily A i j hij Q F).obj I
    let v := OpenSupport.rightMap
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      Q I (F.obj (Q ⊗ I)) (η.app (Q ⊗ I))
    ∃ (hI : CochainComplex.IsKInjective
        ((pullComplex A j).obj I))
      (hJ : CochainComplex.IsKInjective
        ((pullComplex A j).obj (F.obj (Q ⊗ I))))
      (hTop : S.ShortExact)
      (hBottom : S'.ShortExact)
      (m : S ⟶ S'),
      HEq m.τ₂ a ∧
      HEq m.τ₃ v ∧
      (∀ m' : S ⟶ S',
        HEq m'.τ₂ a →
        HEq m'.τ₃ v → m' = m) ∧
      _root_.DerivedCategory.triangleOfSES hTop ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSES hBottom ∈ distTriang _ ∧
      _root_.DerivedCategory.triangleOfSESδ hTop ≫
          ((localize A P).map m.τ₁)⟦1⟧' =
        (localize A P).map m.τ₃ ≫ _root_.DerivedCategory.triangleOfSESδ hBottom ∧
      (tensorModel φ Q π hQ I L.obj e).inv ≫ (localize A P).map (η.app (Q ⊗ I)) ≫
          (replacementIso (η.app (Q ⊗ I)) (tensorModel φ Q π hQ I L.obj e)).hom =
        𝟙 _ ∧
      (localize A P).map v ≫
          (targetThirdModel φ j (F.obj (Q ⊗ I)) L.obj
            (replacementIso (η.app (Q ⊗ I)) (tensorModel φ Q π hQ I L.obj e)) hJ).hom =
        (sourceThirdModel φ j Q π hQ I L.obj e hI).hom ≫ restrictedProjection φ j L.obj ∧
      (IsIso ((localize A P).map m.τ₃) → IsIso ((localize A P).map m.τ₁)) ∧
      DiagramNatural (topSequenceFamily A i j hij Q)
        (bottomSequenceFamily A i j hij Q F)
        (IsComparison A i j hij Q F η) I m := by
  classical
  intro S N J a S' v
  obtain ⟨hI, hJ, hTop, hBottom, m, hm₂, hm₃, huniq, hmid, hnat⟩ :=
    support_comparison_strict i j hij I Q _hQf F η
  refine ⟨hI, hJ, hTop, hBottom, m, hm₂, hm₃, huniq,
    _root_.DerivedCategory.triangleOfSES_distinguished hTop,
    _root_.DerivedCategory.triangleOfSES_distinguished hBottom,
    _root_.DerivedCategory.triangleOfSESδ_naturality hTop hBottom m, ?_, ?_, ?_, hnat⟩
  · simp only [replacementIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      IsIso.hom_inv_id_assoc, Iso.inv_hom_id]
  · exact support_comparison_projection φ i j hij L _hTL _hRTL _hRL _hTRL
      I e Q π hQ _hQf F η hI hJ
  · intro hvIso
    have := hmid
    have : IsIso ((localize A P).map m.τ₃) := hvIso
    exact finish_triangle hTop hBottom m


attribute [instance] Scheme.instAbelianSheafEtaleSmallEtaleTopology
attribute [instance] HomologicalComplex.monoidalCategoryStruct CategoryTheory.catToReflQuiver
end AlgebraicGeometry.Etale.KFlatSupportComparison
