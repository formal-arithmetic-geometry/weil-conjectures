/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues

/-! # Constant finite-projective models of a lisse sheaf
Source: blueprint lemma-flat-models-generators--2, proof of the generator assertion.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- Finite projective geometric stalks give finite projective constant trivializations.
Source: blueprint lemma-flat-models-generators--2, clause (3), the generators
"L locally constant with finite projective stalks".

Proof: take an etale trivializing cover from local constancy. Discard empty members,
which do not affect joint surjectivity. Each remaining member has a geometric point.
Apply that point's exact sheaf fiber to the chosen constant trivialization. The fiber
of the constant A-module sheaf is its given module, and the fiber of the restriction
of L is the geometric stalk of L at the composed point. The resulting A-linear
isomorphism identifies the constant module with that stalk. The hypotheses give
finiteness and projectivity of the stalk; a finite underlying set gives a finitely
generated A-module, and projectivity is invariant under A-linear isomorphism. Keep
the same constant trivializations on this refined cover. If the scheme is empty,
take the empty cover, for which every asserted model condition is vacuous. -/
theorem lisseProjective_constantModels
    {S : Scheme.{u}} (A : Type (u + 1)) [CommRing A] [Finite A]
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : FlatModelEtaleLisseProjective A L) :
    ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat.{u + 1} A, Module.Finite A P ∧ Module.Projective A P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (S.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj P) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have hfin : IsFiniteSheaf L := ⟨fun Ω _ _ t ↦ by
    have := (hL.2 Ω t).1
    exact (ModuleCat.isFinitelyGenerated_iff _).mpr (Module.Finite.of_finite)⟩
  have hlocal : IsFiniteLocallyConstantSheaf L :=
    { toIsLocallyConstantSheaf := hL.1, toIsFiniteSheaf := hfin }
  obtain ⟨d₀, hd₀⟩ := (Scheme.finite_locally_constant_module_values_iff L).1.mpr hlocal
  choose P hP eP using hd₀
  let 𝒰 : Cover.{u} etalePrecoverage S :=
    { I₀ := { i : d₀.cover.I₀ // Nonempty (d₀.cover.X i) }
      X i := d₀.cover.X i.1
      f i := d₀.cover.f i.1
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun y ↦ ?_, fun i ↦ d₀.cover.map_prop i.1⟩
        obtain ⟨i, x, hx⟩ := d₀.cover.exists_eq y
        exact ⟨⟨i, ⟨x⟩⟩, x, hx⟩ }
  let d : Scheme.LocallyConstantDatum L := ⟨𝒰, fun i ↦ d₀.isConstant i.1⟩
  have hmodels (i : d.cover.I₀) : Finite (P i.1) ∧
      Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (S.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} A)).obj (P i.1)) := ⟨hP i.1, eP i.1⟩
  refine ⟨d, fun i ↦ ?_⟩
  let U := d.cover.etalePrecoverageToEtale i
  have : Nonempty U.left := i.2
  let x : U.left := Classical.arbitrary _
  let Ω := AlgebraicClosure (U.left.residueField x)
  let t : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).2
    ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
  obtain ⟨e⟩ := (Scheme.finite_locally_constant_module_values_iff L).2.2
    d (fun i ↦ P i.1) hmodels i Ω t
  let : Module.Projective A
      (((pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
        (A := ModuleCat.{u + 1} A)).obj L) := (hL.2 Ω (t ≫ d.cover.f i)).2
  have := hP i.1
  exact ⟨P i.1, Module.Finite.of_finite,
    Module.Projective.of_equiv e.toLinearEquiv, eP i.1⟩

end AlgebraicGeometry
