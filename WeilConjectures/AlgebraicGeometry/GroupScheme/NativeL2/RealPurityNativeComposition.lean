/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.CategoryTheory.Simple
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeLisseClosure
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeFibreRank
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealPurityNativeRankDetection
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Actual composition filtrations for native lisse Weil modules

Source: sk-p-real-purity, first and last proof paragraphs
(blueprint: lem-rp-native-composition-filtration).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

/-- A lisse native Weil module on a smooth geometrically connected curve has an actual
finite constructible filtration with nonzero simple lisse subquotients.
Source: sk-p-real-purity, actual composition filtration and mixedness paragraphs
(blueprint: lem-rp-native-composition-filtration).

Proof: choose a geometric point of the connected finite-type geometric curve and use
its actual fibre dimension as rank. Exactness makes this rank additive; finite freeness
makes it finite, and the locally constant rank-loci theorem detects zero on the connected
curve. Kernels, cokernels and extensions are lisse by coefficient-heart closure. Apply
the natural-number rank induction to obtain a finite chain with simple lisse quotients.
Every stage embeds in the endpoint by composing the chain's monomorphisms. This makes
each quotient an actual simple subquotient of the original module. Lisse stages are
constructible. The zero module gives the empty chain. -/
theorem native_exists_composition_filtration
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : WeilModule D l X₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) :
    ∃ (n : ℕ) (G : Fin (n + 1) → WeilModule D l X₀)
      (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left (G i).carrier) ∧
      IsZero (G 0) ∧ Nonempty (G (Fin.last n) ≅ M) ∧ (∀ i, Mono (φ i)) ∧
      ∀ i, IsNonzeroSimpleSubquotient D l X₀ M (cokernel (φ i)) := by
  classical
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber X₀).hom := inferInstanceAs
    (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsNoetherian (D.geometricFiber X₀).left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom }
  have : GeometricallyConnected (D.geometricFiber X₀).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : ConnectedSpace (D.geometricFiber X₀).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (D.geometricFiber X₀).hom
  obtain ⟨x, -, hx⟩ := isClosed_univ.exists_closed_singleton
    (X := (D.geometricFiber X₀).left) Set.univ_nonempty
  let z := pointOfClosedPoint (D.geometricFiber X₀).hom x hx
  let P : ObjectProperty (WeilModule D l X₀) := fun N ↦
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) N.carrier
  let F := Endofunctor.IsoAlgebra.forget
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)
  let V := F ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙ pointSections l D.k
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    native_lisse_of_iso l _ (F.mapIso e) h⟩
  obtain ⟨hker, hext⟩ := native_weil_lisse_closure l D X₀
  let R : ObjectProperty.LisseRankData P := {
    rank := fun N ↦ Module.finrank (ULift.{u + 1} (PadicAlgCl l)) (V.obj N)
    congr := fun e ↦ (V.mapIso e).toLinearEquiv.finrank_eq
    zero := fun N hN ↦ native_lisse_of_isZero l _ N.carrier (F.map_isZero hN)
    detects_zero := fun N hN hr ↦ by
      have := native_fibre_finite_of_lisse D l N.carrier hN z
      have hz : Subsingleton (fibre l D N.carrier z) := Module.finrank_zero_iff.mp hr
      have hzero := native_isZero_of_subsingleton_fibre D l _ N.carrier hN z hz
      rw [IsZero.iff_id_eq_zero]
      apply F.map_injective
      simpa only [Functor.map_id, Functor.map_zero] using hzero.eq_of_src
        (F.map (𝟙 N)) 0
    kernel := fun hA hB f ↦ (hker f hA hB).1
    cokernel := fun hA hB f ↦ (hker f hA hB).2
    extension := fun f _ hA hQ ↦ hext f hA hQ
    additive := fun f _ hA hB ↦ native_fibre_rank_add D l X₀ z f hA (hker f hA hB).2 }
  obtain ⟨n, G, φ, h0, ⟨e⟩, hmono, hlisse, hsimple⟩ :=
    ObjectProperty.exists_filtration_isSimpleIn_of_rank P R M hM
  refine ⟨n, G, φ, fun i ↦ native_constructible_of_lisse l _ _ (hlisse i),
    h0, ⟨e⟩, hmono, ?_⟩
  intro i
  obtain ⟨g, hg⟩ := ObjectProperty.exists_mono_to_endpoint_of_chain φ hmono e i.succ
  exact ⟨hsimple i, G i.castSucc, G i.succ, φ i, g,
    hlisse _, hlisse _, hmono i, hg, ⟨Iso.refl _⟩⟩

end WeilConjectures.NativeL2
