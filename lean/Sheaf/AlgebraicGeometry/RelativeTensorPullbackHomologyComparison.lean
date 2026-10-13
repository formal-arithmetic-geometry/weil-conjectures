/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Relative tensor-pullback homology comparison

Source: Stacks Project, Tag 08EV, second displayed equality;
Cohomology, Lemma 20.27.4 (Tag 08DE).
(blueprint: lem-pc-relative-tensor-pullback-homology-comparison)
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Restricting scalars identifies the homology of tensor with derived pullback
with the homology computed by any K-flat resolution of the restricted complex.
This comparison does not require finite Tor amplitude or any boundedness of K or P.
Source: Stacks Project, Tag 08EV, second displayed equality, and Cohomology,
Lemma 20.27.4 (Tag 08DE).

Proof: Resolve F[0] by a bounded-above flat complex L, zero above zero. Exact
inverse image carries L to a K-flat resolution of the inverse-image module.
Resolve K over O_X by a K-flat complex A. The termwise pullback of L is K-flat
and computes Lf*(F[0]), so A tensor f*L computes the displayed derived tensor.
After restricting scalars, tensor associativity identifies this complex with
A restricted to f-inverse O_S tensor f-inverse L. Exact restriction of scalars
preserves the quasi-isomorphism A -> K. Since f-inverse L is K-flat, tensoring
it with the zigzag A| -> K| <- P gives quasi-isomorphisms. Since P is K-flat,
tensoring P with the augmentation f-inverse L -> f-inverse F[0] is also a
quasi-isomorphism. The resulting zigzag identifies homology with that of
P tensor f-inverse F[0]. Exact restriction of scalars and the exact forgetful
functor to abelian sheaves commute with homology. Finally, the isomorphism
Q(K) -> E transports the derived tensor and its homology. The construction
uses no chosen arbitrary derived object and works also for zero modules and
empty schemes.
(blueprint: lem-pc-relative-tensor-pullback-homology-comparison) -/
theorem relativeTensorPullback_homology_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing f.base S.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlat (R := TopCat.Sheaf.inverseImageRing f.base S.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
    (hq : QuasiIso q)
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor P
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (TopCat.Sheaf.inverseImageModule f.base S.sheaf F))
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)) := by sorry

end AlgebraicGeometry.Scheme
