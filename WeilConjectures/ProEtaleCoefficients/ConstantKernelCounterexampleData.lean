/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.RingTheory.NonFiniteMultiplicationKernel
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Constant square-zero kernel counterexample data

Source: `literature/blueprint/latest/blueprint/sec-proetale-coefficients/`
`sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.proof.md`,
counterexample construction, and `prop-sfb-bounded-constructible-triangulated.proof.md`,
Kernels and common-stratification paragraphs.
(blueprint: lem-sfb-constant-kernel-counterexample-data)

The scalar ring and endomorphism are the existing square-zero construction. The
constant module functor sheafifies genuine constant module presheaves by `mapMod`;
thus all actions, and not only their underlying abelian sheaves, are specified.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry BoundedConstructibleCounterexample
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ConstantKernelData

/-- The constant square-zero ring object, with the sheafified multiplication and unit.
Source: blueprint counterexample construction
(blueprint: lem-sfb-constant-kernel-counterexample-data). -/
abbrev Ring (X : Scheme.{u}) : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.constRingSheaf (Scheme.ProEt.topology X) Coeff.{u + 1}

/-- Constant module objects, including their sheafified actions and linear maps.
Source: blueprint counterexample construction, constant module clause
(blueprint: lem-sfb-constant-kernel-counterexample-data). -/
def constantModule (X : Scheme.{u}) : ModuleCat.{u + 1} Coeff.{u + 1} ⥤
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (Ring X) :=
  Functor.const (Scheme.ProEt X)ᵒᵖ ⋙ Presheaf.moduleToMod Coeff.{u + 1} ⋙
    (presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapMod
      (Presheaf.constRingObj Coeff.{u + 1})

/-- Multiplication by the square-zero vector `e = (0, δ₀)` on the regular module.
Source: blueprint counterexample construction, multiplication map clause
(blueprint: lem-sfb-constant-kernel-counterexample-data). -/
def multiplication (X : Scheme.{u}) : Mod.regular (Ring X) ⟶ Mod.regular (Ring X) :=
  (constantModule X).map (ModuleCat.ofHom scalarEnd.{u + 1})

/-- The constant module of the scalar multiplication kernel, with its canonical action.
Source: blueprint counterexample construction, kernel identification clause
(blueprint: lem-sfb-constant-kernel-counterexample-data). -/
def kernelModule (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (Ring X) :=
  (constantModule X).obj (ModuleCat.of Coeff.{u + 1} (LinearMap.ker scalarEnd.{u + 1}))

end AlgebraicGeometry.ProEtale.ConstantKernelData

namespace AlgebraicGeometry.ProEtale

open scoped ZeroObject

private def pullRegularIso {Y X : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    ((upperStar Ab.{u + 1} g).mapMod R).obj (Mod.regular R) ≅
      Mod.regular ((upperStar Ab.{u + 1} g).obj R) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

private lemma regular_finitelyPresented {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    Mod.IsFinitelyPresented R (Mod.regular R) := by
  let e : Mod.finiteFree R 1 ≅ Mod.regular R := biproductUniqueIso _
  exact ⟨1, 0, 0, ⟨e.symm ≪≫ (cokernelZeroIsoTarget (X := Mod.finiteFree R 0)).symm⟩⟩

private lemma constructible_regular_or_zero {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsZero M ∨ Nonempty (M ≅ Mod.regular R)) :
    IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a) :=
    .singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _)
  refine ⟨U, fun i ↦ ?_⟩
  let F := (upperStar Ab.{u + 1} (S.immersion a)).mapMod R
  let G := (upperStar Ab.{u + 1} (U.f i)).mapMod
    ((upperStar Ab.{u + 1} (S.immersion a)).obj R)
  rcases hM with hM | hM
  · refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
    exact (G.map_isZero (F.map_isZero hM)).iso (isZero_cokernel_of_epi (𝟙 _))
  · obtain ⟨e⟩ := hM
    let e' := G.mapIso (F.mapIso e ≪≫ pullRegularIso (S.immersion a) R) ≪≫
      pullRegularIso (U.f i) _
    obtain ⟨n, m, f, ⟨ef⟩⟩ := regular_finitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} (S.immersion a)).obj R))
    exact ⟨n, m, f, ⟨e' ≪≫ ef⟩⟩

private lemma boundedConstructible_regular {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular R)) := by
  let K := (DerivedCategory.singleFunctor _ 0).obj (Mod.regular R)
  apply (mem_boundedConstructible_iff R K).2
  refine ⟨⟨0, 0, fun i hi ↦ ?_⟩, fun i ↦ ?_⟩
  · rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE K 0 i hi
    · exact DerivedCategory.isZero_of_isLE K 0 i hi
  · apply constructible_regular_or_zero
    by_cases hi : i = 0
    · subst i
      exact Or.inr ⟨(DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _⟩
    · left
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE K 0 i hi
      · exact DerivedCategory.isZero_of_isLE K 0 i hi

private lemma constant_kernel (X : Scheme.{u}) :
    Nonempty (kernel (ConstantKernelData.multiplication X) ≅
      ConstantKernelData.kernelModule X) := by
  let E := Presheaf.modConstRingEquivalence (Scheme.ProEt X) Coeff.{u + 1}
  have : PreservesFiniteLimits (Presheaf.moduleToMod (C := Scheme.ProEt X)
      Coeff.{u + 1}) := inferInstanceAs (PreservesFiniteLimits E.inverse)
  have : PreservesFiniteLimits (ConstantKernelData.constantModule X) :=
    inferInstanceAs (PreservesFiniteLimits
      (Functor.const (Scheme.ProEt X)ᵒᵖ ⋙ Presheaf.moduleToMod Coeff.{u + 1} ⋙
        (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod
          (Presheaf.constRingObj Coeff.{u + 1})))
  exact ⟨(PreservesKernel.iso (ConstantKernelData.constantModule X)
    (ModuleCat.ofHom scalarEnd.{u + 1})).symm ≪≫
      (ConstantKernelData.constantModule X).mapIso
        (ModuleCat.kernelIsoKer (ModuleCat.ofHom scalarEnd.{u + 1}))⟩

/-- The two regular degree-zero complexes are bounded constructible, and the kernel
of the specified multiplication map is the constant module of its scalar kernel.

Source: blueprint `det-def-sfb-bounded-constructible.proof.md`, counterexample,
and `prop-sfb-bounded-constructible-triangulated.proof.md`, Kernels and
common-stratification paragraphs
(blueprint: lem-sfb-constant-kernel-counterexample-data).

Proof:
1. The square-zero ring, basis vector and its linear multiplication map are the
existing `Coeff` and `scalarEnd`. The constant module functor applies the
presheaf module-object construction followed by strong monoidal sheafification.
Its value on the scalar regular module is the regular ring-sheaf module, and
its map on `scalarEnd` is the specified multiplication morphism.
2. The scalar sequence from its kernel to the two regular modules is exact.
Constant presheaves preserve this sequence sectionwise, and abelian
sheafification is exact. The sheafified inclusion is therefore an underlying
kernel. The unique kernel action agrees with the sheafified scalar action,
since the inclusion is linear. Kernel uniqueness gives the module isomorphism.
3. Use the one-stratum stratification and the identity pro-etale cover. The
regular module has presentation `R^0 → R^1 → R`; pullback preserves this
presentation. The zero module similarly has the rank-zero presentation.
The regular single complex has degree-zero cohomology the regular module and
zero cohomology in every other degree. Thus it is bounded constructible.
4. Both endpoints are this same regular single complex; combine step 3 with
the kernel isomorphism of step 2.
-/
theorem constantKernelCounterexampleData (k : Type u) [Field k] [IsSepClosed k] :
    boundedConstructible
        (ConstantKernelData.Ring (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
        ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular
          (ConstantKernelData.Ring (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))))) ∧
      boundedConstructible
        (ConstantKernelData.Ring (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
        ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular
          (ConstantKernelData.Ring (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))))) ∧
      Nonempty
        (kernel (ConstantKernelData.multiplication
            (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) ≅
          ConstantKernelData.kernelModule (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) := by
  exact ⟨boundedConstructible_regular _, boundedConstructible_regular _, constant_kernel _⟩

end AlgebraicGeometry.ProEtale
