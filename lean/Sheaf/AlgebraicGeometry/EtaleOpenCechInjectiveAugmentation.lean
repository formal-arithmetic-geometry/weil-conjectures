/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # The injective étale Čech row on an open covering

Source: Stacks Project, Tags 03AW and 03F6.
(blueprint: lem-sc-etale-open-cech-injective-augmentation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction from the terminal open object augments the pulled-back Čech
complex of a single injective étale sheaf by a quasi-isomorphism.

Source: Stacks Project, Tags 03AW and 03F6; the row calculation in
lem-sc-etale-open-cech-resolution-total, proof steps 1 and 2.
(blueprint: lem-sc-etale-open-cech-injective-augmentation)

Proof: The family of opens generates a covering sieve on top. Cover preservation
sends it to a covering sieve on i(top). Finite-limit preservation, and terminality
of i(top), identify i of every finite intersection with the fibre product of
the corresponding members over i(top). The unique projection-compatible product
isomorphisms commute with all Čech faces, hence identify the displayed complex
with the Čech complex of this image covering. Lift the index by ULift if the
large-index étale Čech interface requires it; reindexing products along the
canonical equivalence does not change the complex. The sheaf condition identifies
its zeroth homology with sections at i(top), through the restriction map fixed
by he. Injective Čech acyclicity gives zero homology in positive degrees. The
single-term source has the same zeroth homology and zero positive homology, so
e induces isomorphisms in every degree. For an empty covering, the sheaf condition
forces sections at i(top) to be zero and all the Čech terms are zero. This
argument uses no injective resolution or total complex. -/
theorem etaleOpenCechInjectiveAugmentation_quasiIso
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hc : CoverPreserving (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology i)
    [PreservesFiniteLimits i] (ht : IsTerminal (i.obj ⊤))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (J : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (e : (CochainComplex.single₀ AddCommGrpCat.{u + 1}).obj (J.obj.obj (op (i.obj ⊤))) ⟶
      (cechComplexFunctor U).obj (i.op ⋙ J.obj))
    (he : ∀ t : Fin 1 → ι,
      e.f 0 ≫ Pi.π (fun s : Fin 1 → ι ↦
        J.obj.obj (op (i.obj (∏ᶜ fun k ↦ U (s k))))) t =
          J.obj.map (i.map (homOfLE le_top)).op) : QuasiIso e := by sorry

end AlgebraicGeometry.Scheme
