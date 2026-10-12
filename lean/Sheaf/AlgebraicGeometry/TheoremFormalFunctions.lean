/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Paper.MLCohomologyPowersIdeal
import Sheaf.Paper.PQFCohomology

/-! # The theorem on formal functions

Source: Stacks Project, Cohomology of Schemes, Theorem 02OC
(blueprint: lem-weil-pbc-theorem-formal-functions).

The index n represents the positive level n+1. The comparison is specified on every
limit projection, so the asserted isomorphism is the canonical one, not an arbitrary
isomorphism of the two modules. The degree-zero assertion uses actual global sections.
H^p and Γ are A-modules by restriction of scalars along (ΓSpecIso A).inv ≫ f.appTop.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical maps on quotients induce an A-linear isomorphism of inverse limits.
Source: Stacks Project, Theorem 02OC
(blueprint: lem-weil-pbc-theorem-formal-functions).

Proof: (1) The quotient-induced maps are A-linear by functoriality of module cohomology.
Multiplication by I^n is zero on the quotient sheaf; hence the maps kill I^n H and factor
through theta_n, compatibly with transitions. (2) Lemma 02OB
(lem-weil-pbc-ml-cohomology-powers-ideal) gives a constant c with K_n ⊆ I^(n-c)H and
stable images N_n = image(H → M_n). (3) A compatible sequence in M_n belongs termwise
to N_n, since its nth term comes from M_(n+c); thus lim N_n = lim M_n.
(4) The induced quotient isomorphisms H/K_n ≅ N_n commute with transitions.
(5) I^n H ⊆ K_n and K_(n+c) ⊆ I^n H, so the two filtrations are cofinal.
(6) The quotient maps H/I^n H → H/K_n and H/K_(n+c) → H/I^n H give mutually inverse
maps on limits. (7) Their composite with lim(H/K_n ≅ N_n) and lim N_n → lim M_n
has components theta_n, proving the claimed canonical isomorphism. At p=0, H^0 is Γ.
-/
theorem theorem_formal_functions {A : Type v} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ θ : ∀ n : ℕ,
        ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F ⧸
          (I ^ (n + 1) • ⊤ : Submodule A ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) →ₗ[A]
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
          (formalModuleQuotient J (n + 1) F),
      (∀ n : ℕ, (θ n).comp
        (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) =
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ J (n + 1) F)).hom) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)
          (Nat.succ_le_succ h))) ∧
      ∃ e : ModuleCat.of A (AdicCompletion I ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)) ≅
          limit (formalCompletionSystem J F ⋙
            (RingedSpace.moduleCohomology X.toRingedSpace p ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
        ∀ n : ℕ, e.hom ≫
          limit.π (formalCompletionSystem J F ⋙
            (RingedSpace.moduleCohomology X.toRingedSpace p ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
          ModuleCat.ofHom ((θ n).comp
            (AdicCompletion.eval I ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F) (n + 1))) := by
  sorry

/-- The degree-zero formal-functions isomorphism for global sections.
Source: Stacks Project, Theorem 02OC, p=0
(blueprint: lem-weil-pbc-theorem-formal-functions).

Proof: (1) The quotient-induced maps are A-linear by functoriality of module cohomology.
Multiplication by I^n is zero on the quotient sheaf; hence the maps kill I^n H and factor
through theta_n, compatibly with transitions. (2) Lemma 02OB
(lem-weil-pbc-ml-cohomology-powers-ideal) gives a constant c with K_n ⊆ I^(n-c)H and
stable images N_n = image(H → M_n). (3) A compatible sequence in M_n belongs termwise
to N_n, since its nth term comes from M_(n+c); thus lim N_n = lim M_n.
(4) The induced quotient isomorphisms H/K_n ≅ N_n commute with transitions.
(5) I^n H ⊆ K_n and K_(n+c) ⊆ I^n H, so the two filtrations are cofinal.
(6) The quotient maps H/I^n H → H/K_n and H/K_(n+c) → H/I^n H give mutually inverse
maps on limits. (7) Their composite with lim(H/K_n ≅ N_n) and lim N_n → lim M_n
has components theta_n, proving the claimed canonical isomorphism. At p=0, H^0 is Γ.
-/
theorem globalSections_formal_functions {A : Type v} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ θ : ∀ n : ℕ,
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F ⧸
          (I ^ (n + 1) • ⊤ : Submodule A ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) →ₗ[A]
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
          (formalModuleQuotient J (n + 1) F),
      (∀ n : ℕ, (θ n).comp
        (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) =
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ J (n + 1) F)).hom) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)
          (Nat.succ_le_succ h))) ∧
      ∃ e : ModuleCat.of A (AdicCompletion I ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)) ≅
          limit (formalCompletionSystem J F ⋙
            (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
        ∀ n : ℕ, e.hom ≫
          limit.π (formalCompletionSystem J F ⋙
            (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
          ModuleCat.ofHom ((θ n).comp
            (AdicCompletion.eval I ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F) (n + 1))) := by
  sorry

end AlgebraicGeometry
