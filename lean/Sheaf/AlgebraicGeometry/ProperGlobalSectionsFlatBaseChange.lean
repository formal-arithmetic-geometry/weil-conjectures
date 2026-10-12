/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-!
# Flat base change for global sections of a proper scheme

Source: Stacks Project, Cohomology of Schemes, Lemma 30.5.2, Tag 02KH,
with the structure sheaf in degree zero
(blueprint: lem-weil-pbc-stein-flat-base-change-global-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flat base change for the structure sheaf in degree zero. The square of global-section
maps of the cartesian square `X ×_{Spec R} Spec S` is a pushout of commutative rings, i.e.
the canonical map `Γ(X, ⊤) ⊗_{Γ(Spec R)} Γ(Spec S) → Γ(X ×_{Spec R} Spec S, ⊤)` is an
isomorphism. The last clause says that if the canonical map `R → Γ(X, ⊤)` is an isomorphism,
then so is the canonical map `S → Γ(X ×_{Spec R} Spec S, ⊤)`.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), specialized to a proper morphism and
`i = 0` (blueprint: lem-weil-pbc-stein-flat-base-change-global-sections).

Proof: Apply `lem-pc-flat-base-change-cohom` to the square defined by `f` and
`Spec.map (CommRingCat.ofHom (algebraMap R S))`, with the quasi-coherent structure sheaf.
Properness implies quasi-compactness and quasi-separatedness. The pullback of the
structure sheaf is the structure sheaf of the pullback scheme, and in degree zero the
theorem says the canonical comparison `H^0(X, O_X) ⊗_R S → H^0(X_U, O_{X_U})` is an
isomorphism. If `H^0(X, O_X) = R`, the tensor identity `R ⊗[R] S ≅ S` gives the final
clause. -/
theorem Scheme.Hom.globalSections_flat_base_change
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] :
    IsPushout f.appTop (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop ∧
      (IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) →
        IsIso ((Scheme.ΓSpecIso (.of S)).inv ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop)) := by
  sorry

end AlgebraicGeometry
