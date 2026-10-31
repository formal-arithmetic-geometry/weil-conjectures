/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjectionConstruction

/-!
# Projection squares for restriction to isomorphic coefficient stages

Source: Zheng, Construction 4.1, Construction 5.15 and Lemma 5.22.
The records contain only compact-support geometry. They contain no exceptional
right adjoints, their evaluations, or their coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- Restriction followed by identity-on-representatives coefficient isomorphisms
has exact strict transports and normalized compact-support projection cubes.
Source: Zheng, Construction 4.1, Construction 5.15 and Lemma 5.22
(blueprint: lem-pur-strict-etale-isomorphic-stage-projection).

Proof: at level n extend scalars along the given ring isomorphism after evaluation
at index n. On successor arrows use the quotient tensor interchange determined by
its tensor unit. The generator equations for a identify the two composite ring
maps, so these arrows satisfy the system relations. Ring isomorphisms make each
level tensor exact; componentwise kernels and cokernels make the strict functor
exact. Localize this functor and its evaluation isomorphisms on complexes. The
universal derived counits identify its finite-level descent with the recorded
level scalar functors, which are equivalences. The inverse-image coefficient
squares agree on tensor units. Their open and proper mates give the displayed
compact-support square and its finite-level evaluations. On a quotient square,
both tensor composites have the same ring map and tensor unit. The normalized
open/proper mates therefore identify the two projection words. Whiskering and
associativity give quotient_cube. All these statements are equations of actual
maps before localization and descend by its universal property; no faithfulness
of evaluation on derived morphisms is used. This is the geometric part of the
cofinal-mate argument; positivity and the ramified ideal identity are separate. -/
theorem strictEtaleIsomorphicStageProjection
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    (_ha : ∀ n, Function.Bijective (a.ring n))
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c) :
    ∃ (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
      (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
      (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
      (_P : StrictEtaleTransportProjection a c SA SB TX TY TZ),
      ∀ n, (TX.level n).derived.IsEquivalence ∧ (TY.level n).derived.IsEquivalence := by
  obtain ⟨TX, hTX⟩ := nonempty_strictEtaleCoefficientTransport_of_bijective
    a _ha SA.PX SB.PX
  obtain ⟨TY, hTY⟩ := nonempty_strictEtaleCoefficientTransport_of_bijective
    a _ha SA.PY SB.PY
  obtain ⟨TZ, hTZ⟩ := nonempty_strictEtaleCoefficientTransport_of_bijective
    a _ha SA.PZ SB.PZ
  obtain ⟨P⟩ := nonempty_strictEtaleTransportProjection_of_equivalences
    a c SA SB TX TY TZ hTX hTY hTZ
  exact ⟨TX, TY, TZ, P, fun n ↦ ⟨hTX n, hTY n⟩⟩

end AlgebraicGeometry
