/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat

/-! # Bounded flat complexes with finite cohomology over a Noetherian ring

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/
lem-pc-noetherian-flat-complex-perfect.md, order 672
(blueprint: lem-pc-noetherian-flat-complex-perfect).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Over a Noetherian commutative ring, an object with a bounded flat representative and
finitely generated cohomology in every degree has a bounded finite projective representative.
The conclusion spells out ring-perfectness, allowing any chosen derived-category universe.
Source: blueprint, sec-picard-framework/sk-thm-picard-semicon,
lem-pc-noetherian-flat-complex-perfect.md, order 672
(blueprint: lem-pc-noetherian-flat-complex-perfect).

Proof:
1. Choose a flat representative `F` concentrated in `[a,b]`. Its tensor with every module
   has zero cohomology below `a`.
2. Construct a bounded-above finite free complex `P` mapping quasi-isomorphically to `F`.
   Start with finitely many cycles generating `H^b(F)`. Descend degree by degree, choosing
   generators of the cone cohomology and using the cone-cycle equations to define each
   new differential and chain-map component. Noetherian finiteness of kernels and cokernels
   (lem-pc-noetherian-finite-kernels-cokernels) keeps all cone cohomology finite. Each fixed
   degree stabilizes, and the resulting cone is acyclic (def-weil-abstract-derived-category).
3. Both bounded-above flat complexes are K-flat (lem-pc-bounded-above-flat-kflat, applied
   on the one-point ringed space), so they compute the same derived tensor. The left tail
   of `P` resolves `Q = coker(P^{a-1} → P^a)`. Thus Tor_1(Q,N), computed by that resolution
   (def-weil-pbc-tor-modules), is H^{a-1}(P tensor N) = H^{a-1}(F tensor N) = 0.
4. Test this for `N = A/I` and apply lem-weil-pbc-flat-tor-ideal-criterion: `Q` is flat.
   It is finitely presented as a cokernel of finite free modules, hence finite projective
   by lem-weil-pbc-finitely-presented-flat-module-projective. Replace the left tail by `Q`
   in degree `a`; the resulting bounded finite projective complex represents `C`, giving
   precisely the affine perfectness described in def-pc-perfect-complex. -/
theorem exists_bounded_finite_projective_model_of_flat_of_finite_homology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (C : DerivedCategory (ModuleCat.{u} A))
    (hflat : ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
      (∀ n : ℤ, Module.Flat A (F.X n)) ∧ Nonempty (Q.obj F ≅ C))
    (hfinite : ∀ i : ℤ, Module.Finite A ((homologyFunctor (ModuleCat.{u} A) i).obj C)) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite A (P.X n)) ∧
      (∀ n : ℤ, Module.Projective A (P.X n)) ∧
      Nonempty (Q.obj P ≅ C) := by
  classical
  obtain ⟨F, ⟨a, b, hbound⟩, hF, ⟨eF⟩⟩ := hflat
  have : F.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff F a).2 fun i hi ↦ hbound i (Or.inl hi)
  have : F.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff F b).2 fun i hi ↦ hbound i (Or.inr hi)
  have hfinF (i : ℤ) : Module.Finite A (F.homology i) := by
    have := hfinite i
    exact Module.Finite.equiv
      (((homologyFunctor (ModuleCat A) i).mapIso eF.symm) ≪≫
        (homologyFunctorFactors (ModuleCat A) i).app F).toLinearEquiv
  -- Keep the original localization before choosing the small derived category.
  let Qw := Q (C := ModuleCat.{u} A)
  let : HasDerivedCategory.{u} (ModuleCat.{u} A) :=
    HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u} A)
  let Qu := Q.{u} (C := ModuleCat.{u} A)
  have hfinQu (i : ℤ) :
      Module.Finite A ((homologyFunctor.{u} (ModuleCat.{u} A) i).obj (Qu.obj F)) := by
    have : Module.Finite A
        ((HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i).obj F) := hfinF i
    exact Module.Finite.equiv
      ((homologyFunctorFactors.{u} (ModuleCat A) i).app F).toLinearEquiv.symm
  obtain ⟨P, c, d, hc, hd, hP, ⟨eP⟩⟩ :=
    isPerfect_of_flat_of_finite_homology F a b hF (Iso.refl (Qu.obj F)) hfinQu
  have : P.IsStrictlyGE c := hc
  have : P.IsStrictlyLE d := hd
  -- The localization lift sends the small model isomorphism back to the chosen universe.
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  have hinv : W.IsInvertedBy Qw := Localization.inverts Qw W
  let T := Localization.lift Qw hinv Qu
  let eT := Localization.fac Qw hinv Qu
  refine ⟨P, ⟨c, d, fun i hi ↦ ?_⟩, fun i ↦ (hP i).2,
    fun i ↦ (hP i).1, ⟨?_⟩⟩
  · rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE c i hi
    · exact P.isZero_of_isStrictlyLE d i hi
  · exact (eT.app P).symm ≪≫ T.mapIso eP.symm ≪≫ eT.app F ≪≫ eF

end DerivedCategory
