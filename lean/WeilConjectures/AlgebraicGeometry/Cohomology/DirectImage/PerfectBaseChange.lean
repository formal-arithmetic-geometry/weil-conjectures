/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex


public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComplex
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Model

/-!
# Perfectness of the higher direct images, with base change

For a proper morphism `f : X ⟶ T` of finite presentation and an `𝒪_X`-module `ℱ` of finite
presentation which is flat over `T`, the higher direct images are locally on `T` computed by a
bounded complex of finite free modules, compatibly with every base change
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

Over an affine open `V` of `T`, the pair `(f, ℱ)` is the base change of a pair `(p, 𝒢)` over an
affine scheme `S` with Noetherian ring of global sections
(`AlgebraicGeometry.Scheme.Modules.exists_isNoetherianRing_model`), for which the statement is
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing`;
base changes of `f` over `V` are base changes of `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback of a bounded complex of finite free modules is a bounded complex of finite free
modules. -/
lemma IsFiniteFreeComplex.pullback {X Z : Scheme.{u}} {P : CochainComplex X.Modules ℤ} {d : ℕ}
    (hP : IsFiniteFreeComplex P d) (j : Z ⟶ X) :
    IsFiniteFreeComplex (((Modules.pullback j).mapHomologicalComplex _).obj P) d where
  isStrictlyGE := by
    have := hP.isStrictlyGE
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyGE 0 i hi)
  isStrictlyLE := by
    have := hP.isStrictlyLE
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ (Modules.pullback j).map_isZero (P.isZero_of_isStrictlyLE d i hi)
  exists_iso_free n := by
    obtain ⟨r, ⟨e⟩⟩ := hP.exists_iso_free n
    exact ⟨r, ⟨(Modules.pullback j).mapIso e ≪≫ pullbackFreeIso j _⟩⟩

section General

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)



end General

section Perfect

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- **Perfectness of `Rf_* ℱ` and base change.** Let `f : X ⟶ S` be proper of finite
presentation with `S = Spec A` affine, and `ℱ` an `𝒪_X`-module of finite presentation, flat over
`S`. Then `Rf_* ℱ` is perfect and its formation commutes with arbitrary base change:

* locally on `S`, `Rf_* ℱ` is represented by a bounded complex of finite free modules whose
  pullback along every `g : T' ⟶ S` computes the higher direct images of `ℱ_{T'}`; this is the
  classical input `exists_isFiniteFreeComplex_higherDirectImage` of `sk-thm-picard-coherence`
  [Stacks, Tag 0B91];
* over the affine base, `Rf_* ℱ` is represented by the bounded complex `K` of flat `A`-modules
  of `AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`, and for every
  cartesian square with `T = Spec B` affine, `Lg^* Rf_* ℱ = B ⊗[A] K ≅ Rf_{T*} ℱ_T` in `D(B)`
  (`lem-pc-rf-base-change-flat-module`; proper morphisms are quasi-compact and separated);
* if `A` is noetherian, `Rf_* ℱ` is a perfect object of `D(A)`, and so are all its base changes
  `Rf_{T*} ℱ_T` in `D(B)`
  (`AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isNoetherianRing`,
  `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange`).

Perfectness in `D(A)` over a non-noetherian base is the classical input of the first item; it is
not deduced here from it, as the comparison of the two representatives of `Rf_* ℱ` would need
the finite free complexes to be quasi-isomorphic to the Čech complex.

(blueprint: `lem-pc-rf-perfect-base-change`) -/
theorem perfect_and_baseChange_cechModuleComplex_of_isProper [IsProper f]
    [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] [Fintype ι]
    [ℱ.IsFinitePresentation] (hℱ : ℱ.IsFlatOver f) :
    (∀ t : S, ∃ (V : S.Opens) (P : CochainComplex V.toScheme.Modules ℤ) (d : ℕ), t ∈ V ∧
      IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ V.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ V.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
    (∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (H : IsPullback g' f' f g)
      [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
      IsIso (cechModuleComplexBaseChangeComparison f ℱ U hU H hg)) ∧
    (IsNoetherianRing Γ(S, ⊤) → (Q.obj (cechModuleComplex f ℱ U)).IsPerfect ∧
      ∀ {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X} {f' : Y ⟶ T} (_ : IsPullback g' f' f g)
        [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)] (_ : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom),
        (Q.obj (cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i))).IsPerfect) := by
  refine ⟨fun t ↦ exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t,
    fun H _ _ hg ↦ isIso_cechModuleComplexBaseChangeComparison f ℱ U hU hU' hℱ H hg,
    fun _ ↦ ?_⟩
  have hP := isPerfect_Q_cechModuleComplex_of_isNoetherianRing f ℱ U hU hU' hℱ
  exact ⟨hP, fun H _ _ hg ↦ (isPerfect_Q_cechModuleComplex_baseChange f ℱ U hU hU' hℱ hP H hg).2⟩

end Perfect

end AlgebraicGeometry.Scheme.Modules
