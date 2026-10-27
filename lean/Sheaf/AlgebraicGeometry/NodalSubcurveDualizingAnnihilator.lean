/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch
public import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.ClosedSubcurveDualizingAdjunction
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.TraceFormula.NodalSubcurveBoundary
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Dualizing modules of reduced component unions of a nodal curve

Source: Stacks Project, curves.tex, Tags 0E33(2), 0E34 and 0E38.
(blueprint: lem-sfb-nodal-subcurve-dualizing-annihilator).

Dualizing modules are supplied with their representing duality data, using the existing
ReducedCurveDualizingPair interface. It applies also to disconnected Y: its duality is
assembled from the finite clopen partition into connected components. The annihilator is
expressed sectionwise on every smaller open, so it is a sheaf condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The Hom map induced by an inclusion of the pushed-forward dualizing module.
It is the section-normalized pullback/pushforward adjunction followed by composition.
Source: Stacks Project, curves.tex, Tag 0E33(2), evaluation-at-one consequence.
(blueprint: lem-sfb-nodal-subcurve-dualizing-annihilator). -/
def nodalSubcurveHomMap {X Y : Scheme.{u}} (i : Y ⟶ X)
    (ωX : X.Modules) (ωY : Y.Modules)
    (j : (Scheme.Modules.pushforward i).obj ωY ⟶ ωX) (M : X.Modules) :
    ((Scheme.Modules.tensorPullback i).obj M ⟶ ωY) → (M ⟶ ωX) :=
  fun φ ↦ (Scheme.Modules.tensorPullbackSectionAdjunction i).homEquiv M ωY φ ≫ j

/-- A nonempty reduced component union inherits nodality and projectivity. Its dualizing
module pushes forward to the sheaf Hom from i_*O_Y, and evaluation at 1 identifies this
with the annihilator of i.ker. The adjunction-induced Hom map for any line bundle is
injective with precisely the annihilated image. The inclusion is an isomorphism at the
selected generic points, where the dualizing stalk has rank one, and zero at the others.

Source: Stacks Project, curves.tex, Tags 0E33(2), 0E34 and 0E38.
(blueprint: lem-sfb-nodal-subcurve-dualizing-annihilator).

Proof (the node's six steps):
1. Compose the closed immersion with a projective embedding of X
   (lem-weil-pbc-closed-immersion-comp) to prove projectivity of Y. Projective implies
   proper (lem-kun-projective-implies-proper). Finite type over the Noetherian field
   gives Noetherian schemes (lem-weil-pbc-finite-type-over-noetherian) and finitely many
   components (lem-weil-pbc-noetherian-finitely-many-components). The selected components
   are exactly the components of Y, so Y is nonempty and pure of dimension one.
   Its connected components form a finite clopen partition into projective reduced curves.
2. Apply lem-trf-nodal-subcurve-boundary with N = X. It gives nodality of Y and
   smoothness at component boundary points. Local rings of its clopen components agree.
3. Apply lem-sfb-nodal-line-serre-riemann-roch on X and each connected component of Y.
   By lem-sfb-reduced-curve-dualizing-module these are the same representing pairs.
   Their unique comparisons preserve duality. Apply
   lem-sfb-closed-subcurve-dualizing-adjunction on each component and assemble the
   isomorphisms by finite products, which are also finite sums of modules. This gives
   the asserted sheaf isomorphism, respecting all duality-preserving comparisons.
4. A local map O_X/I_Y → omega_X is determined by w = h(1), killed by I_Y.
   Conversely w defines the map a mod I_Y ↦ a w. The inverse constructions commute
   with restrictions, proving the evaluation formula, injectivity and annihilator image
   (def-sbc-closed-immersion-ideal-sheaf and def-pur-sheaf-hom).
5. Use def-pc-module-pullback's normalized adjunction and compose with the inclusion.
   It is injective. A map lies in its image exactly when its values lie in the
   annihilator. Factor it there uniquely; on a trivialization of M the factorization
   sends the generator to the unique preimage of its value. Uniqueness glues these maps.
6. Remove the other components near a selected generic point. The reduced schemes
   X and Y agree there, hence I_Y = 0 and evaluation at 1 is the quotient-Hom
   identification of the rank-one dualizing stalks. Rank one is supplied by
   lem-sfb-reduced-curve-dualizing-module. Near an unselected generic point Y is empty,
   so the pushed-forward module and the inclusion's stalk map are zero.
-/
theorem exists_nodalSubcurveDualizingAnnihilator
    (k : Type u) [Field k] [IsAlgClosed k]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hPureX : X.IsPureDimension 1)
    (hNodalX : ∀ x : X, IsClosed ({x} : Set X) →
      x ∉ (X ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃+*
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
            (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)})))
    (i : Y ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] [IsReduced Y]
    (S : Set (Set X)) (hS : S ⊆ irreducibleComponents X) (hne : S.Nonempty)
    (hUnion : Set.range i = ⋃₀ S) :
    IsHProjective (Y ↘ Spec (.of k)) ∧ Nonempty Y ∧ Y.IsPureDimension 1 ∧
    (∀ y : Y, IsClosed ({y} : Set Y) →
      y ∉ (i ≫ X ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y) ≃+*
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
            (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}))) ∧
    (∀ y : Y, i y ∈ closure ((Set.range i)ᶜ) →
      y ∈ (i ≫ X ↘ Spec (.of k)).smoothLocus) ∧
    ∃ e : ∀ (DX : ReducedCurveDualizingPair k X) (DY : ReducedCurveDualizingPair k Y),
        (Scheme.Modules.pushforward i).obj DY.omega ≅
          SheafOfModules.homObj (R := X.sheaf)
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)) DX.omega,
      (∀ (DX DX' : ReducedCurveDualizingPair k X)
          (DY DY' : ReducedCurveDualizingPair k Y)
          (a : DX.omega ≅ DX'.omega) (b : DY.omega ≅ DY'.omega),
        (∀ (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
          (f : F ⟶ DX.omega), DX'.duality F hF (f ≫ a.hom) = DX.duality F hF f) →
        (∀ (G : Y.Modules) (hG : RingedSpace.IsCoherent Y.toRingedSpace G)
          (g : G ⟶ DY.omega), DY'.duality G hG (g ≫ b.hom) = DY.duality G hG g) →
        (Scheme.Modules.pushforward i).map b.hom ≫ (e DX' DY').hom =
          (e DX DY).hom ≫ SheafOfModules.homObjMap (R := X.sheaf)
            (𝟙 ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf)))
            a.hom) ∧
      ∀ DX : ReducedCurveDualizingPair k X,
        ∃ ev : SheafOfModules.homObj (R := X.sheaf)
            ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf))
            DX.omega ⟶ DX.omega,
          (∀ (U : X.Opens)
            (φ : Γ(SheafOfModules.homObj (R := X.sheaf)
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf))
              DX.omega, U)),
            ev.val.app (op U) φ = φ.app (op (Over.mk (𝟙 U))) (1 : Γ(Y, i ⁻¹ᵁ U))) ∧
          (∀ U : X.Opens, Function.Injective (ev.val.app (op U))) ∧
          (∀ (U : X.Opens) (w : Γ(DX.omega, U)),
            w ∈ Set.range (ev.val.app (op U)) ↔
              ∀ (V : X.Opens) (hVU : V ≤ U) (j : Γ(X, V)), j ∈ i.ker.idealOfOpens V →
                j • DX.omega.val.map (homOfLE hVU).op w = 0) ∧
          ∀ DY : ReducedCurveDualizingPair k Y,
            (∀ (M : X.Modules), M.IsInvertible →
              Function.Injective
                (nodalSubcurveHomMap i DX.omega DY.omega ((e DX DY).hom ≫ ev) M) ∧
              ∀ f : M ⟶ DX.omega,
                f ∈ Set.range
                  (nodalSubcurveHomMap i DX.omega DY.omega ((e DX DY).hom ≫ ev) M) ↔
                  ∀ (U : X.Opens) (m : Γ(M, U)) (j : Γ(X, U)),
                    j ∈ i.ker.idealOfOpens U → j • f.val.app (op U) m = 0) ∧
            (∀ (Z : Set X), Z ∈ irreducibleComponents X → ∀ η : X, IsGenericPoint η Z →
              (Z ∈ S →
                IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace η).map
                  ((e DX DY).hom ≫ ev)) ∧
                IsField (X.presheaf.stalk η) ∧
                Nonempty (((RingedSpace.moduleStalkFunctor X.toRingedSpace η).obj DX.omega)
                  ≃ₗ[X.presheaf.stalk η] X.presheaf.stalk η)) ∧
              (Z ∉ S →
                (RingedSpace.moduleStalkFunctor X.toRingedSpace η).map
                  ((e DX DY).hom ≫ ev) = 0)) := by
  sorry

end AlgebraicGeometry
