/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # The relative Tor bound on a strictly perfect chart

Source: Stacks Project, Tags 0DJQ and 08CI, the local relative Tor calculation.
(blueprint: lem-pc-strict-perfect-tensor-relative-tor-bound).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A strictly perfect chart of amplitude `[a,b]` gives the relative tensor bound
`[a+c,b+d]` on that chart, for any global relative K-flat model of the tensor.
Source: Stacks Project, Tag 0DJQ, proof, and Tag 08CI, implication (2) to (1).

Proof: On U, represent E by L. Its terms are retracts of finite free modules,
so they are flat over O_U. Since L is bounded, it is K-flat over O_U, and
L tensor G|_U represents the restriction of E tensor^L G. Its degree n term
is the finite direct sum of L^p tensor G^q for p+q=n. If n is outside
[a+c,b+d], every summand vanishes by one of the two degree bounds.
For relative flatness, choose an affine neighbourhood V of f(x). On affine
neighbourhoods W of x inside f^{-1}V the sections of G^q are flat over O_S(V).
Their filtered colimit is flat over O_S(V), and localization gives flatness
over O_{S,f(x)}. Thus G^q restricted to U is flat over (f^{-1}O_S)|_U.
Tensoring with L^p makes a retract of a finite sum of these flat modules;
finite sums and retracts preserve flatness. The bounded total complex is
therefore K-flat over (f^{-1}O_S)|_U. The quasi-isomorphism q and the model
isomorphisms identify its relative derived tensors with those computed by
P|_U. Open restriction is exact, preserves total tensors and K-flatness,
and hence identifies the restriction of each homology sheaf with the local
homology. Tensoring the bounded flat model with F[0] leaves its degree
bounds unchanged, so the homology sheaf restricts to zero on U. Its sections
on every V <= U are zero. This also covers empty U, zero complexes, and
reversed degree bounds, when the bounded complex in question is zero.
(blueprint: lem-pc-strict-perfect-tensor-relative-tor-bound). -/
theorem strictPerfect_tensor_relativeTor_bound
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (G K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E ⊗ DerivedCategory.Q.obj G)
    (U : X.Opens)
    (L : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hL : IsStrictlyPerfect X U L)
    (eL : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj L)
    (a b c d : ℤ)
    (hLb : ∀ n : ℤ, n < a ∨ b < n → IsZero (L.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    ∀ (P : CochainComplex (SheafOfModules.{u} A) ℤ),
      CochainComplex.IsKFlat (R := R) P →
      ∀ q : P ⟶ ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
              (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K,
        QuasiIso q → ∀ (F : SheafOfModules.{u} A) (i : ℤ),
          i < a + c ∨ b + d < i → ∀ (V : X.Opens), V ≤ U →
            IsZero ((SheafOfModules.evaluation A (Opposite.op V)).obj
              ((CochainComplex.mapBifunctor P
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) := by sorry

end AlgebraicGeometry.Scheme
