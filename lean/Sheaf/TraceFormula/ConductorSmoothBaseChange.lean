module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.ReducedNormalization
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-!
# Conductor and smooth base change

Source: Stacks Project, Algebra, Tag 07T8; Morphisms, Tags 035P, 035S, 0H7D;
ILO Exposé VIII, Lemma 2.2.9 (blueprint: lem-trf-conductor-smooth-base-change).
-/



universe u

set_option autoImplicit false
set_option warn.sorry false

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The cokernel of the canonical structure-sheaf map into the pushforward of the
componentwise normalization.
Source: Stacks Project, Algebra, Tag 07T8 (blueprint: lem-trf-conductor-smooth-base-change). -/
noncomputable def conductorCokernel (S : Scheme.{u}) : S.Modules :=
  cokernel (SheafOfModules.unitToPushforwardObjUnit
    (Scheme.fromReducedNormalization S).toRingCatSheafHom)

/-- The ideal sheaf obtained affine-locally as the annihilator of the normalization
cokernel.
Source: Stacks Project, Algebra, Tag 07T8 (blueprint: lem-trf-conductor-smooth-base-change). -/
noncomputable def conductorIdeal (S : Scheme.{u}) : S.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (fun U ↦
    Module.annihilator (Γ(S, U)) (Γ(conductorCokernel S, U)))

/-- For a reduced finite-type scheme over `ℚ`, the conductor ideal of componentwise
normalization is coherent, cuts out exactly the nonnormal locus, and commutes with
quasi-compact smooth pullback. The conductor ideal `D_S` itself is stated coherent as an
`𝒪_S`-module through its ideal sheaf `(conductorIdeal S).toModules`.
Source: Stacks Project, Algebra, Tag 07T8; Morphisms, Tags 035P, 035S, 0H7D;
ILO Exposé VIII, Lemma 2.2.9 (blueprint: lem-trf-conductor-smooth-base-change).
Proof: use finiteness and injectivity of componentwise normalization, coherence of its
pushforward and cokernel, the affine annihilator/support calculation, and the smooth
normalization comparison. Apply finite flat annihilator base change on affine smooth
charts; the local equalities glue and are compatible with identity and composition.
-/
theorem conductor_smooth_base_change
    (S : Scheme.{u}) [AlgebraicGeometry.IsReduced S]
    (q : S ⟶ Spec (.of (ULift ℚ))) [LocallyOfFiniteType q] [QuasiCompact q]
    : IsFinite (Scheme.fromReducedNormalization S) ∧
      (∀ U : S.Opens, Function.Injective
        ((Scheme.fromReducedNormalization S).app U).hom) ∧
      RingedSpace.IsCoherent S.toRingedSpace (conductorCokernel S) ∧
      RingedSpace.IsCoherent S.toRingedSpace (conductorIdeal S).toModules ∧
      (∀ x : S, x ∈ ((conductorIdeal S).support : Set S) ↔
        ¬ (IsDomain (S.presheaf.stalk x).carrier ∧
          IsIntegrallyClosed (S.presheaf.stalk x).carrier)) ∧
      IsNowhereDense
        ((conductorIdeal S).support : Set S) ∧
      ((conductorIdeal S = ⊤) ↔
        ∀ x : S, IsDomain (S.presheaf.stalk x).carrier ∧
          IsIntegrallyClosed (S.presheaf.stalk x).carrier) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S), QuasiCompact h → Smooth h →
        conductorIdeal T = (conductorIdeal S).comap h) ∧
      ((conductorIdeal S).comap (𝟙 S) = conductorIdeal S) ∧
      (∀ (T U : Scheme.{u}) (h : T ⟶ S) (g : U ⟶ T),
        (conductorIdeal S).comap (g ≫ h) =
          ((conductorIdeal S).comap h).comap g)
    := by sorry

end AlgebraicGeometry

end
