/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.RingedSliceEvaluationModels

/-! # Slice evaluation on resolved representatives

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-representative-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- Normalized slice evaluation on a flat-term K-flat source and K-injective target.
Source: Stacks Project, Tags 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-representative-evaluation).

Proof: resolve Hom(P,I) by a flat-term K-flat Q. The Hom normalization supplies kappa,
kappa_U and the relocalization chain isomorphism gamma. Compose Q to Hom(P,I) with
the map induced by the fixed augmentation of I, and use the uncurry_model field of T.
On the slice use the restricted resolution, gamma, and the fixed augmentation of rI
with the uncurry_model field of T_U. Both uncurried chain maps send a local x tensor p
to the corresponding Hom-family component applied to p. The local-family formula for
gamma identifies the local arguments. The two resulting chain maps initially have
different targets r(F(I)) and F_U(rI). Compare them in the common target F_U(r(F(I))):
postcompose the first by its fixed augmentation, and the second by F_U(r(augmentation(I))).
The componentwise postcomposition formula is homComplexFunctor_obj_map_f_π:
coefficientHomComponent and homComplexπ choose the same projections, by proof irrelevance
after unfolding homComplexFunctor and the reducible Exists.choose alias. Naturality of
the fixed augmentation then says these common-target formulas agree on each local pure
tensor. Sheafification and total-summand extensionality give equality of these
chain maps. Localize and use the tensor and Hom normalization squares. The two
RingedKInjectiveHomModel augmentation equations cancel the fixed
K-injective replacements. The resolving quasi-isomorphisms and tensor model maps are
isomorphisms, so their cancellation gives exactly the counit identity below. The Hom
complex need not be K-flat, and no evaluation map is inverted. -/
theorem ringedSlice_representativeEvaluation
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U))
      (ht : RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d)
      (hh : RingedSliceHomModel.{c, v, u, w, w'} J A U S T SU TU d)
    (P I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (fP : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X n))
    [I.IsKInjective] :
    (d.rho ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op (DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj I))) (DerivedCategory.Q.obj P)).inv ≫
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
            (S.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) =
      SU.tensor.map (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
        ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op (DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj I))),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P))) (Y :=
        ((derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj (op
        ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj I)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P)))
      ((d.eta (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).hom, 𝟙 _) ≫
        SU.evaluation
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P))
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj I))
      := by
  sorry

end CategoryTheory
