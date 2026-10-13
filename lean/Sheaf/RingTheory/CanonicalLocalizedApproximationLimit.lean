/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Sheaf.RingTheory.LocalizedApproximationColimits

/-! # Comparison of canonical localized approximation colimits

Source: Stacks Project, Algebra, Tag 00RC, first reduction, and Tag 037D.
(blueprint: lem-weil-pbc-canonical-localized-approximation-limit)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- The colimit comparison for the explicitly constructed fraction diagrams.

Source: Stacks Project, Algebra, Tag 037D; Tag 00RC, first reduction paragraph.
(blueprint: lem-weil-pbc-canonical-localized-approximation-limit)

Proof:
Contract the prime of S along ULift.down and the stage cocone maps. Localization
commutes with the two supplied filtered ring colimits (Tag 037D); transport the
comparison through the ULift ring equivalences. For modules, lift a numerator and
denominator in M_q to a common stage, using joint surjectivity of the original
ring and group cocones. The denominator remains outside the contracted prime.
If two fractions agree, lift a multiplier outside q killing their cross difference
and descend that zero relation to a later stage by eventual equality in the
original additive-group colimit. Thus the fraction cocone to M_q is a colimit.
Transport the S_q action across its additive comparison with the chosen colimit.
Any localized scalar and module element come from a common stage, so the assumed
coprojection scalar formula identifies the supplied act with this transported
fraction action. Likewise the supplied ψ equals the canonical map R_(q∩R) to S_q:
the two maps agree on every coprojection, which uniquely determines a colimit map.
Compose R→R_(q∩R) with the inverse base-ring comparison to obtain ρ. This is an
IsLocalization because the base comparison is a ring isomorphism intertwining
these maps. On fractions the comparisons preserve multiplication by the image
of R in S: IsScalarTower identifies that action with the original R-action on M.
Thus the inverse additive comparison M_q→colimit Dₗ is R-linear for the action
restricted first through ψ and then through ρ. This proves the linear equivalence.
The argument also covers zero modules, singleton diagrams, and noninjective
transitions. The ring map and action are supplied rather than chosen here. -/
theorem canonical_localized_approximation_limit
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    let R' := ULift.{max u v w} R
    let S' := ULift.{max u v w} S
    let M' := ULift.{max u v w} M
    letI : Algebra R' S' := ULift.algebra' R S'
    ∀
    {Λ : Type (max u v w)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{max u v w}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R'))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{max u v w})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M'))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R' → S'` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R') π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M') ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R' S')) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x))
    (q : PrimeSpectrum S),
    let q' : PrimeSpectrum S' := ⟨q.asIdeal.comap ULift.ringEquiv.toRingHom,
      Ideal.IsPrime.comap _⟩
    let hs := fun (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i) ↦
      hmodel.2.2.2.2.1 i j (leOfHom f) b x
    let Aₗ := primeRingDiagram A (η ≫ κ) q'
    let Bₗ := primeRingDiagram B κ q'
    let Dₗ := primeModuleDiagram B κ q' D hs
    ∀ (ψ : (colimit Aₗ : CommRingCat.{max u v w}) →+*
        (colimit Bₗ : CommRingCat.{max u v w}))
      (act : Module (colimit Bₗ : CommRingCat.{max u v w})
        (colimit Dₗ : AddCommGrpCat.{max u v w})),
      letI := act
      (∀ i, ψ.comp (colimit.ι Aₗ i).hom =
        (colimit.ι Bₗ i).hom.comp (primeDiagramHom A B η κ q' i)) →
      (∀ (i : Λ) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (colimit.ι Dₗ i).hom (b • x) =
          (colimit.ι Bₗ i).hom b • (colimit.ι Dₗ i).hom x) →
      (∃ ρ : R →+* (colimit Aₗ : CommRingCat.{max u v w}),
        letI := ρ.toAlgebra
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ψ
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ρ
        IsLocalization (q.asIdeal.comap (algebraMap R S)).primeCompl
          (colimit Aₗ : CommRingCat.{max u v w}) ∧
        Nonempty (LocalizedModule q.asIdeal.primeCompl M ≃ₗ[R]
          (colimit Dₗ : AddCommGrpCat.{max u v w}))) := by sorry

end Algebra
