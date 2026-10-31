/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Over
import WeilConjectures.AlgebraicGeometry.GaloisConnectedImageInvariantSeparation
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClopenPartitionDescent
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions

/-!
# Geometric connectedness of a connected scheme receiving a geometrically connected map

Source: Stacks Project, `varieties.tex`, Tag 056R,
`lemma-geometrically-connected-criterion`
(blueprint: lem-trf-geometrically-connected-image-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A connected scheme receiving a morphism from a geometrically connected scheme over a
field is geometrically connected.

Source: Stacks Project, `varieties.tex`, Tag 056R,
`lemma-geometrically-connected-criterion`
(blueprint: lem-trf-geometrically-connected-image-criterion).

Proof: For a finite separable extension of the base field, embed it into a finite Galois
extension. The source remains connected after this extension, and the two field-extension
projections from the target base changes are surjective. A hypothetical clopen partition of
the Galois base change pulls back to the connected source; the nonempty image of the source
lies in one part. Intersect all Galois translates of that part. The intersection and its
complement are nonempty invariant clopen subsets, so the invariant closed-subset descent
statement descends them to a separation of the original connected target. Hence the Galois
base change is connected, and connectedness descends along the projection to the original
finite separable base change. The finite-separable test for geometric connectedness then
gives the conclusion.
-/
theorem GeometricallyConnected.of_connectedSpace_of_geometricallyConnected
    {k : Type u} [Field k] {T X : Scheme.{u}}
    [T.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of k))]
    [GeometricallyConnected (T ↘ Spec (.of k))] [ConnectedSpace X] :
    GeometricallyConnected (X ↘ Spec (.of k)) := by
  classical
  apply (GeometricallyConnected.iff_connectedSpace_finite_separable k X).mpr
  intro E _ _ _ _
  obtain ⟨L, hL, aL, hfin, hsep, hsplit, hemb⟩ :=
    finite_galois_receiving_separable_extensions k 1 (fun _ ↦ E)
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
  let : Field L := hL
  let : Algebra k L := aL
  have : FiniteDimensional k L := hfin
  have : Algebra.IsSeparable k L := hsep
  have : Normal k L := normal_iff.mpr fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, hsplit x⟩
  have : IsGalois k L := ⟨⟩
  let gL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have : ConnectedSpace (T.baseChangeField k L) :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  let fL := ((Over.pullback gL).map (f.asOver (Spec (.of k)))).left
  have : Nonempty (X.baseChangeField k L) :=
    ⟨fL (Nonempty.some (inferInstance : Nonempty (T.baseChangeField k L)))⟩
  have hXL : ConnectedSpace (X.baseChangeField k L) := by
    apply connectedSpace_iff_clopen.mpr
    refine ⟨inferInstance, fun A hA ↦ ?_⟩
    by_contra! hne
    obtain ⟨C, P, Q, _, _, _, hPne, hQne, hP, hQ, hdisj, hcover, _, _, hinv⟩ :=
      galois_connected_image_invariant_separation k L T X f A Aᶜ hA hA.compl
        hne.1 (Set.nonempty_compl.mpr hne.2)
        disjoint_compl_right (Set.union_compl_self A)
    obtain ⟨R, ⟨hRne, hSne, hR, _, hRS, _, _, _⟩, _⟩ :=
      existsUnique_clopen_partition_of_galois_invariant k L X P Q hPne hQne hP hQ
        hdisj hcover (fun σ ↦ (hinv σ).1) (fun σ ↦ (hinv σ).2)
    have hRuniv : R.1 = Set.univ := hR.eq_univ hRne
    obtain ⟨x, hx⟩ := hSne
    exact Set.disjoint_left.mp hRS (hRuniv ▸ Set.mem_univ x) hx
  have : ConnectedSpace (X.baseChangeField k L) := hXL
  obtain ⟨τ⟩ := hemb 0
  let gE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let j : Over.mk gL ⟶ Over.mk gE :=
    Over.homMk (Spec.map (CommRingCat.ofHom τ.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact τ.commutes x)
  have : Surjective j.left := by
    change Surjective (Spec.map (CommRingCat.ofHom τ.toRingHom))
    exact ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Surjective (baseChangeMap (X ↘ Spec (.of k)) j) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (isPullback_baseChangeMap (X ↘ Spec (.of k)) j).flip inferInstance
  let q : X.baseChangeField k L ⟶ X.baseChangeField k E :=
    baseChangeMap (X ↘ Spec (.of k)) j
  have : Surjective q := ‹Surjective (baseChangeMap (X ↘ Spec (.of k)) j)›
  exact q.surjective.connectedSpace q.continuous

end AlgebraicGeometry

end
