/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PointDerivedHomModels
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Finite-projective scalar dual comparison on the pro-etale point

Source: Stacks Tags 08JJ and 0A8X.
(blueprint: lem-pod-point-finite-projective-dual-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PointDerivedHom

variable (k : Type u) [Field k] {R : CommRingCat.{u + 1}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
  (α : constantRing.{u, u} k R ⟶ B)
  (L : ModuleCat.{u + 1} R ⥤ Modules.{u, u} k B)
  (hobj : ∀ M : ModuleCat.{u + 1} R, L.obj M = extensionObject.{u, u} k B α M)
  (adj : L ⊣ sections.{u, u} k B α)

attribute [-instance] abSheafify abLocallyBijective
local instance : HasSheafify (Scheme.ProEt.topology (Spec (.of k)))
    AddCommGrpCat.{u + 1} := abSheafify.{u, u} k
local instance : (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1} := abLocallyBijective.{u, u} k

/-- Extension of the ordinary scalar Hom dual is the actual ordinary sheaf Hom
dual, with evaluation normalization.
Source: Stacks Tags 08JJ and 0A8X
(blueprint: lem-pod-point-finite-projective-dual-comparison).

Proof: for a finite-projective module choose a finite dual basis m_i, lambda_i.
The evaluation map sends b tensor f to the local map c tensor x to bc f(x).
Its inverse sends a local morphism g to the sum of g(1 tensor m_i) tensor lambda_i.
The two dual-basis identities prove the composites on constant generators;
the associated-sheaf universal property and the finite-power retractions extend
these identities from generators to all sections on every slice. Both maps
commute with restriction. Projecting
the scalar Hom cochain of degree j onto (-j,0) and the sheaf Hom complex onto
the same component assembles these evaluation maps into an isomorphism. Both
differentials are -(-1)^j times precomposition with d_P, so the degree maps
commute with the signed differentials. Transporting the degree-zero single
coordinates gives the formula for every p+j=0, without identifying arbitrary
single-complex degrees by definitional equality. The zero module, empty basis, and
reversed support interval are covered by zero maps and empty sums. -/
theorem point_finiteProjective_dual_comparison
    (hmap : ∀ {M N : ModuleCat.{u + 1} R} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫ extensionMorphism.{u, u} k B α f ≫
        eqToHom (hobj N).symm)
    (hex : ExplicitAdjunction.{u, u} k B α L hobj adj)
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (P : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    let C := (extensionComplex.{u, u} k B α L adj).obj P
    let D := CochainComplex.moduleHomComplex P
      ((CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0).obj
      (ModuleCat.of R R))
    ∃ h : (extensionComplex.{u, u} k B α L adj).obj D ≅ sheafHom.{u, u} k B C
      ((CochainComplex.singleFunctor (Modules.{u, u} k B) 0).obj
      (SheafOfModules.unit (ring.{u, u} k B))),
      (∀ (p j : ℤ) (hpj : p + j = 0) (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
        (b c : B.obj.obj U) (f : D.X j) (x : P.X p),
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
          (SheafOfModules.unit (ring.{u, u} k B)) (p + j) hpj).hom.val.app U
          (homValue.{u, u} k B C ((CochainComplex.singleFunctor (Modules.{u, u} k B) 0).obj
      (SheafOfModules.unit (ring.{u, u} k B))) j p U
            ((h.hom.f j).val.app U (generator.{u, u} k B α L hobj (D.X j) U b f))
            (generator.{u, u} k B α L hobj (P.X p) U c x)) =
          b * c * scalar.{u, u} k B α U
            ((HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0
              (ModuleCat.of R R) (p + j) hpj).hom.hom ((f.v p (p + j) rfl).hom x))) := by
  sorry

attribute [instance] abSheafify abLocallyBijective
end WeilConjectures.PointDerivedHom
