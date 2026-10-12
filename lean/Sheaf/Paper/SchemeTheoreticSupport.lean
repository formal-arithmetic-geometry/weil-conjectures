/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.RingTheory.AnnihilatorLocalizationAway

/-! # Scheme-theoretic support

Source: Stacks Project, Morphisms, Lemma 05JU and Definition 05JV
(blueprint: lem-weil-pbc-scheme-theoretic-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The annihilator ideal sheaf cuts out the scheme-theoretic support of a finite type
quasi-coherent module. Its sections on an arbitrary open are the kernel of the closed
immersion's map on sections; the displayed equivalence identifies these with the rule
of annihilating every section on every smaller open.
Source: Stacks Project, Morphisms, Lemma 05JU and Definition 05JV, with Lemma 01QQ
(blueprint: lem-weil-pbc-scheme-theoretic-support).

Proof (the node's seven steps):
1. The rule on arbitrary opens is an ideal, stable under restriction, and membership is
   local by the sheaf property (def-weil-sheaf-of-modules-category); hence it is an ideal sheaf.
2. On an affine open it equals the annihilator of sections: use the principal-open basis
   (lem-weil-pbc-affine-open-spec-points, def-weil-affine-spectrum,
   lem-weil-pbc-affine-ideals-closed-subscheme) and the quasi-coherent section base-change
   formula (lem-weil-pbc-quasi-coherent-affine-section-base-change), then sheaf locality.
3. Finite type makes the affine section module finite
   (lem-weil-pbc-quasi-coherent-finite-type-affine). The annihilator localizes
   (lem-weil-pbc-annihilator-localization-finite, def-weil-pbc-module-localization-away),
   so the affine ideals satisfy basic-open compatibility.
4. The compatible ideals cut out a closed subscheme with the stated quotient charts
   (lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-closed-immersion,
   def-sbc-closed-immersion-ideal-sheaf).
5. Its kernel ideal sheaf equals the annihilator sheaf on affine opens, hence on every
   open by sheaf locality. It is therefore quasi-coherent (def-pc-scheme,
   def-sbc-closed-immersion-ideal-sheaf).
6. The image equals the nonzero-stalk locus on affine opens by the finite-module support
   formula (lem-weil-pbc-finite-type-module-support-closed,
   lem-weil-pbc-affine-open-spec-points, def-weil-pbc-closed-subset-proper-over-base),
   hence globally because affine opens cover (def-pc-scheme).
7. Taking the smaller open equal to the given open proves annihilation. Any closed
   immersion's ideal sheaf annihilating F is contained in this sheaf, since its sections
   restrict to sections of that ideal on every smaller open
   (def-sbc-closed-immersion-ideal-sheaf). -/
theorem schemeTheoreticSupport
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (I : X.IdealSheafData),
      (∀ (U : X.affineOpens),
        I.ideal U = Module.annihilator (X.presheaf.obj (Opposite.op U.1))
          (F.presheaf.obj (Opposite.op U.1))) ∧
      IsClosedImmersion I.subschemeι ∧
      I.subschemeι.ker = I ∧
      (∀ (U : X.Opens) (a : X.presheaf.obj (Opposite.op U)),
        a ∈ RingHom.ker (I.subschemeι.app U).hom ↔
          ∀ (V : X.Opens) (h : V ≤ U) (s : F.presheaf.obj (Opposite.op V)),
            X.presheaf.map (homOfLE h).op a • s = 0) ∧
      (∀ (U : X.affineOpens),
        IsPullback (I.subschemeCover.f U)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
          I.subschemeι U.2.fromSpec) ∧
      Set.range I.subschemeι = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ (V : X.Opens) (a : RingHom.ker (I.subschemeι.app V).hom)
        (s : F.presheaf.obj (Opposite.op V)), a • s = 0) ∧
      (∀ (Z' : Scheme.{u}) (i' : Z' ⟶ X), IsClosedImmersion i' →
        (∀ (V : X.Opens) (a : RingHom.ker (i'.app V).hom)
          (s : F.presheaf.obj (Opposite.op V)), a • s = 0) →
        ∀ (U : X.Opens),
          RingHom.ker (i'.app U).hom ≤ RingHom.ker (I.subschemeι.app U).hom) := by
  sorry

end AlgebraicGeometry.Scheme
