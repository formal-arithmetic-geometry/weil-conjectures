/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.ModulePullbackTensor

/-!
# Derived pullback and derived tensor product

Source: Stacks Project, Cohomology, Lemma 079U
(cohomology-lemma-pullback-tensor-product), line 6411
(blueprint: lem-pc-derived-pullback-tensor-product).

There is no derived tensor bifunctor on `D(𝒪_X)`; as in
def-pc-derived-tensor-cohomology-vanishes and lem-pc-derived-pullback-tensor-qcoh,
`K ⊗^L L` is stated through K-flat representatives `K ≅ Q(P)`, `L ≅ Q(N)`, for which
`K ⊗^L L ≅ Q(Tot(P ⊗_{𝒪_X} N))`.
-/

universe uPull wPull

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The tensor product of sheaves of `𝒪_X`-modules, `SheafOfModules.monoidalCategory X.sheaf`
(def-pc-tensor-complex-sheaves), made a local instance for the total tensor complexes below. -/
noncomputable local instance (X : Scheme.{uPull}) :
    MonoidalCategory (SheafOfModules.{uPull} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxSize 256 in
/-- (blueprint: lem-pc-derived-pullback-tensor-product) For a morphism of schemes
`g : T ⟶ S`, derived pullback commutes with derived tensor product:
`Lg^*(K ⊗^L L) ≅ Lg^*K ⊗^L Lg^*L`, canonically and naturally in `K` and `L`.

There is no derived tensor bifunctor on `D(𝒪_X)`, so the statement is made on K-flat
representatives: every `K, L ∈ D(𝒪_S)` are `Q(P), Q(N)` with `P, N` K-flat
(lem-pc-kflat-resolution), and then `K ⊗^L L = Q(Tot(P ⊗ N))`. The functor `F` is the
recorded termwise module pullback `Scheme.Modules.tensorPullback g` and `ε` is the
left-derived counit of `derivedPullback g` (the form of def-pc-derived-pullback and
lem-pc-flat-complex-derived-pullback); `Lg^*K = Q(g^*P)` and `Lg^*L = Q(g^*N)` through `ε`,
and `g^*P` is K-flat (lem-pc-kflat-pullback-preservation), so
`Lg^*K ⊗^L Lg^*L = Q(Tot(g^*P ⊗ g^*N))`. The complex isomorphism
`φ P N : g^*Tot(P ⊗ N) ≅ Tot(g^*P ⊗ g^*N)` is the canonical one: on each summand
`P^p ⊗ N^q` it is the module pullback tensor isomorphism of
lem-weil-pbc-module-pullback-tensor, and it is natural in `P` and `N`. The canonical map
`Lg^*(Q(Tot(P ⊗ N))) ⟶ Q(Tot(g^*P ⊗ g^*N))`, the counit followed by `Q(φ P N)`, is an
isomorphism; naturality of `ε` and of `φ` gives naturality in `K` and `L`.

Proof (the node's two steps):
1. Choose K-flat resolutions of both arguments using `lem-pc-kflat-resolution`. Their
   pullbacks are K-flat by `lem-pc-kflat-pullback-preservation`; the tensor total complex is
   K-flat by `lem-pc-kflat-tensor-product`, so these complexes represent the three derived
   tensors via `def-pc-derived-pullback` and `def-pc-tensor-complex-sheaves`; in particular
   the counit `ε` is invertible at `Tot(P ⊗ N)`.
2. The module pullback tensor isomorphisms of `lem-weil-pbc-module-pullback-tensor`,
   degreewise and natural in both factors, form an isomorphism of total complexes `φ`.
   Passing to the derived categories gives the displayed comparison and its naturality. -/
theorem derivedPullback_tensorProduct
    {T S : Scheme.{uPull}} (g : T ⟶ S)
    [HasDerivedCategory.{wPull}
      (SheafOfModules.{uPull} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{wPull}
      (SheafOfModules.{uPull} (moduleRings T.toRingedSpace))] :
    ∃ (F : SheafOfModules.{uPull} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{uPull} (moduleRings T.toRingedSpace))
      (hF : ∀ M, F.obj M = Scheme.Modules.tensorPullbackObj g M)
      (_ : ∀ {M N} (a : M ⟶ N),
        F.map a = eqToHom (hF M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
          eqToHom (hF N).symm)
      (_ : F.Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      (derivedPullback g).IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso
            (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∃ φ : ∀ P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ,
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
            CochainComplex.mapBifunctor ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _),
        (∀ (P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ)
            (p q n : ℤ) (h : p + q = n),
          F.map (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (ComplexShape.up ℤ)
              p q n h) ≫ (φ P N).hom.f n =
            eqToHom (hF _) ≫
              ((Classical.choose (Scheme.Modules.module_pullback_tensor g)) (P.X p)
                (N.X q)).hom ≫
              (eqToHom (hF (P.X p)).symm ⊗ₘ eqToHom (hF (N.X q)).symm) ≫
              HomologicalComplex.ιMapBifunctor
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) (curriedTensor _)
                (ComplexShape.up ℤ) p q n h) ∧
        (∀ (P P' N N' : CochainComplex
              (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ)
            (a : P ⟶ P') (b : N ⟶ N'),
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (HomologicalComplex.mapBifunctorMap a b (curriedTensor _) (ComplexShape.up ℤ)) ≫
              (φ P' N').hom =
            (φ P N).hom ≫
              HomologicalComplex.mapBifunctorMap
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map b) (curriedTensor _)
                (ComplexShape.up ℤ)) ∧
        ∀ P N : CochainComplex (SheafOfModules.{uPull} (moduleRings S.toRingedSpace)) ℤ,
          CochainComplex.IsKFlat (R := S.sheaf) P → CochainComplex.IsKFlat (R := S.sheaf) N →
            IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor _))) ≫
              DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (φ P N).hom)) := by
  sorry

end AlgebraicGeometry
