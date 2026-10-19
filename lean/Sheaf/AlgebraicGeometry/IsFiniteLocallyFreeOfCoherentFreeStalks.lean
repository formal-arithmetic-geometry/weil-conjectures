/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-!
# Coherent modules with finite free stalks are finite locally free

Source: Stacks Project, Algebra, Tag 0GWM, applied on Noetherian affine opens;
Cohomology of Schemes, Tag 01XZ; Divisors, Tag 0CC4
(blueprint: lem-sc-coherent-free-stalks-locally-free).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option linter.style.haveILetI false in
private theorem flat_sections_of_free_stalks
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (hfree : ∀ x : X,
      Module.Free (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) :
    Module.Flat Γ(X, U) Γ(F, U) := by
  let R := Γ(X, U)
  let M := Γ(F, U)
  apply Module.flat_of_localized_maximal M
  intro P hP
  let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  let y : U := hU.isoSpec.inv p
  let x : X := y.1
  obtain ⟨f, hf, hloc⟩ := Scheme.isLocalizedModule_affine_germ F inferInstance U hU y
  have hp : (hU.primeIdealOf y).asIdeal = P := by
    have he : hU.primeIdealOf y = p := by
      change hU.isoSpec.hom (hU.isoSpec.inv p) = p
      simp
    exact congrArg PrimeSpectrum.asIdeal he
  let N := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F
  letI : Module R N := Module.compHom _ (X.presheaf.germ U x y.2).hom
  change M →ₗ[R] N at f
  let S := (hU.primeIdealOf y).asIdeal.primeCompl
  letI : Algebra R (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, y.2⟩
  letI : IsLocalization S (X.presheaf.stalk x) := hU.isLocalization_stalk y
  have hfree_x : Module.Free (X.presheaf.stalk x) N := (hfree x).1
  let g : M →ₗ[R] N := f
  letI : IsLocalizedModule S g := hloc
  letI : IsScalarTower R (X.presheaf.stalk x) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have hbase := IsLocalizedModule.isBaseChange S (X.presheaf.stalk x) g
  letI : Module.Free (X.presheaf.stalk x)
      (TensorProduct R (X.presheaf.stalk x) M) :=
    Module.Free.of_equiv hbase.equiv.symm
  letI : Module (X.presheaf.stalk x) (LocalizedModule S M) :=
    IsLocalizedModule.module S (LocalizedModule.mkLinearMap S M)
  letI : IsScalarTower R (X.presheaf.stalk x) (LocalizedModule S M) :=
    IsLocalizedModule.isScalarTower_module (A := X.presheaf.stalk x) S
      (LocalizedModule.mkLinearMap S M)
  letI : Module.Free (X.presheaf.stalk x) (LocalizedModule S M) := by
    let hb := IsLocalizedModule.isBaseChange S (X.presheaf.stalk x)
      (LocalizedModule.mkLinearMap S M)
    exact Module.Free.of_equiv hb.equiv
  have hflat_local : Module.Flat (X.presheaf.stalk x) (LocalizedModule S M) :=
    Module.Flat.of_free
  have hflat : Module.Flat R (LocalizedModule S M) :=
    (Module.flat_iff_of_isLocalization (X.presheaf.stalk x) S
      (LocalizedModule S M)).mp hflat_local
  have heq : P.primeCompl = S := by
    ext z
    change z ∉ P ↔ z ∉ (hU.primeIdealOf y).asIdeal
    rw [hp]
  exact heq ▸ hflat

set_option linter.style.haveILetI false in
/-- A coherent module on a locally Noetherian scheme whose stalks are finite free is
finite locally free, with no requirement that the ranks on different opens be equal.
Source: Stacks Project, Algebra, Tag 0GWM, and Cohomology of Schemes, Tag 01XZ
(blueprint: lem-sc-coherent-free-stalks-locally-free).

Proof:
1. Apply `isCoherent_iff_isQuasicoherent_and_isFiniteType` to install quasi-coherence and
   finite type. Then use `isFiniteLocallyFree_of_isAffineOpen`, reducing the result to finite
   presentation and flatness of sections on each affine open. The finite-type affine sections
   theorem gives finite generation; the Noetherian section ring gives finite presentation.
2. To prove flatness, fix an affine open U and a maximal ideal P of its section ring. The
   corresponding point y of U has a section-to-stalk map which is a localization by
   `isLocalizedModule_affine_germ`. Base change for this localized module and the finite-free
   stalk hypothesis make the localized section module free, hence flat. The localized-maximal
   criterion then gives flatness of the section module, completing the affine criterion.
3. Applying the affine criterion on every affine open is exactly finite local freeness.
-/
theorem isFiniteLocallyFree_of_coherent_free_stalks
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (hcoherent : RingedSpace.IsCoherent X.toRingedSpace F)
    (hfree : ∀ x : X,
      Module.Free (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  have hq :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hcoherent
  letI : F.IsQuasicoherent := hq.1
  letI : F.IsFiniteType := hq.2
  apply Scheme.Modules.isFiniteLocallyFree_of_isAffineOpen F
  intro U hU
  haveI : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfinite : Module.Finite Γ(X, U) Γ(F, U) :=
    Scheme.Modules.finite_sections_of_finiteType F hU
  exact ⟨Module.finitePresentation_of_finite _ _,
    flat_sections_of_free_stalks F hU hfree⟩

end AlgebraicGeometry.Scheme.Modules
