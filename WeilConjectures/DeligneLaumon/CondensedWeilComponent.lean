/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibreFunctoriality
import WeilConjectures.AlgebraicGeometry.NormalityPerfectClosureTest

/-! # A normal geometric component as a condensed fibre context

Source: Weil II (1.1.10)--(1.1.12), and normality over a perfect field.
(blueprint: lem-dl-a1-condensed-weil-component-context).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

-- Retain the assigned generic-point hypothesis, although the construction works at every point.
set_option linter.unusedVariables false in
/-- The component through a geometric generic point has exactly the hypotheses of the
normalized condensed fibre theorem. Its inclusion and point remain the actual scheme maps.

Source: Weil II (1.1.10)--(1.1.12); Stacks Project, Tag 038O, normality over a perfect field.
(blueprint: lem-dl-a1-condensed-weil-component-context).

Proof: the finite base field is perfect. Apply the perfect-closure normality criterion
with the base field itself: its identity base change has the original normal stalks, so
every field base change does too. Finite type makes the geometric fibre Noetherian. Its
connected component through the point is clopen; restrict to that open subscheme. The
open-immersion stalk isomorphisms preserve normality. The spectrum of the point field is
a singleton, so the point factors through this open. Connectedness, local Noetherianity
and compactness give precisely the remaining fields of RealCondensedFibre.Context. -/
theorem component_context_exists (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ (D.geometricFiber U₀).left)
    (hNormal : ∀ x : U₀.left, IsDomain (U₀.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (U₀.left.presheaf.stalk x))
    (hGeneric : ∃ Z ∈ irreducibleComponents (D.geometricFiber U₀).left,
      IsGenericPoint (t (IsLocalRing.closedPoint Ω)) Z) :
    ∃ (C : RealCondensedFibre.Context.{u})
      (j : C.X ⟶ (D.geometricFiber U₀).left) (x : Spec (.of Ω) ⟶ C.X),
      IsOpenImmersion j ∧ Set.range j = connectedComponent (t (IsLocalRing.closedPoint Ω)) ∧
        x ≫ j = t := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k₀))
  have hg : IsIso g := by
    dsimp only [g]
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  let := hg
  let p := pullback.fst U₀.hom g
  have hself (y : (pullback U₀.hom g : Scheme.{u})) :
      IsDomain ((pullback U₀.hom g).presheaf.stalk y) ∧
        IsIntegrallyClosed ((pullback U₀.hom g).presheaf.stalk y) := by
    let e := (asIso (p.stalkMap y)).commRingCatIsoToRingEquiv
    have := (hNormal (p y)).1
    have := (hNormal (p y)).2
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  let X := (D.geometricFiber U₀).left
  have hn (y : X) : IsDomain (X.presheaf.stalk y) ∧
      IsIntegrallyClosed (X.presheaf.stalk y) :=
    ((normal_stalks_perfectClosure_iff D.k₀ D.k₀
      (fun a ↦ ⟨0, a, by simp⟩) U₀.left U₀.hom).mp hself) D.k y
  have : IsNoetherian X := {
    toIsLocallyNoetherian := by
      change IsLocallyNoetherian (pullback U₀.hom _)
      infer_instance
    toCompactSpace := by
      change CompactSpace ↥(pullback U₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) : Scheme.{u})
      infer_instance }
  let V : X.Opens := ⟨connectedComponent (t (IsLocalRing.closedPoint Ω)),
    isOpen_connectedComponent⟩
  have : ConnectedSpace V :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : CompactSpace V := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (V : Set X))
  have hrange : Set.range t ⊆ Set.range V.ι := by
    rintro y ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change t z ∈ connectedComponent (t (IsLocalRing.closedPoint Ω))
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact mem_connectedComponent
  let x := IsOpenImmersion.lift V.ι t hrange
  have hV (y : V.toScheme) : IsDomain (V.toScheme.presheaf.stalk y) ∧
      IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := by
    let e := (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
    have := (hn (V.ι y)).1
    have := (hn (V.ι y)).2
    exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩
  refine ⟨⟨V.toScheme, ⟨x (IsLocalRing.closedPoint Ω)⟩, inferInstance,
    inferInstance, inferInstance, hV⟩, V.ι, x, inferInstance, ?_, ?_⟩
  · exact Scheme.Opens.range_ι V
  · exact IsOpenImmersion.lift_fac V.ι t hrange

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
