/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.GabberModificationData
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.QuasiProjectiveTowerAmple
import Sheaf.AlgebraicGeometry.AmpleFiniteGroupQuotientConstruction
import Sheaf.AlgebraicGeometry.AmpleAdmissibleFiniteGroupQuotient
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Finite group quotients of relatively quasi-projective schemes

Source: Rydh, Existence and properties of geometric quotients, Theorem 4.4,
Proposition 4.7 and Remark 4.9, pp. 20--23
(blueprint: lem-per-projective-finite-group-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A finite-projective-space immersion is locally of finite type. -/
private theorem quasiProjective_lft {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GabberModification.QuasiProjective f) : LocallyOfFiniteType f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have : IsImmersion i := hi
  rw [← hif]
  infer_instance

/-- The same immersion also makes its structure morphism separated. -/
private theorem quasiProjective_separated {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GabberModification.QuasiProjective f) : IsSeparated f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  have : IsImmersion i := hi
  rw [← hif]
  infer_instance

/-- An absolute ample module gives the required relative finite-space immersion.
The existing projective-space lift supplies the immersion over the intermediate base. -/
private theorem quasiProjective_of_ample
    (S B Q : Scheme.{u}) [IsAffine S] (b : B ⟶ S) [LocallyOfFiniteType b]
    (r : Q ⟶ B) [LocallyOfFiniteType r]
    (M : Q.Modules) [M.IsInvertible] (hM : Scheme.Modules.IsAmple Q M) :
    GabberModification.QuasiProjective r := by
  let c := b ≫ S.isoSpec.hom
  have : LocallyOfFiniteType (r ≫ c) := inferInstance
  obtain ⟨d, hd, n, i, hi, hif, _⟩ :=
    Scheme.Modules.IsAmple.exists_immersion_affine_base Γ(S, ⊤) Q (r ≫ c) M hM
  have : IsImmersion i := hi
  exact ⟨n, ProjectiveSpace.liftBaseChange r i hif.symm, inferInstance, by simp⟩

/-- Universal closedness descends through the surjection. The already obtained
quasi-projective immersion is then proper and therefore closed. -/
private theorem projective_of_surjective_quasiProjective
    {V Q B : Scheme.{u}} (q : V ⟶ Q) [Surjective q] (r : Q ⟶ B)
    [LocallyOfFiniteType r] (hr : GabberModification.QuasiProjective r)
    (hp : IsHProjective (q ≫ r)) : IsHProjective r := by
  have : IsHProjective (q ≫ r) := hp
  have : IsSeparated r := quasiProjective_separated r hr
  have : UniversallyClosed r := UniversallyClosed.of_comp_surjective q r
  have : IsProper r := {}
  obtain ⟨n, i, hi, hif⟩ := hr
  have : IsImmersion i := hi
  have : IsProper (i ≫ ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B) := by
    rw [hif]
    infer_instance
  have : IsProper i :=
    IsProper.of_comp i (ℙ(ULift.{u} (Fin (n + 1)); B) ↘ B)
  have : IsClosedImmersion i :=
    IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range
  exact ⟨⟨ULift.{u} (Fin (n + 1)), inferInstance, i, inferInstance, hif⟩⟩

/-- Injectivity into the reduced source's section rings proves reducedness, and
surjectivity transports irreducibility. No affine chart choices are needed. -/
private theorem integral_of_admissible_quotient
    {H : Type v} [Group H] [Finite H] {V Q : Scheme.{u}}
    (a : H →* Aut V) (q : V ⟶ Q) [Surjective q]
    (hq : IsAdmissibleFiniteSchemeQuotient a q) [IsIntegral V] : IsIntegral Q := by
  have : IsReduced Q := ⟨fun U ↦
    isReduced_of_injective (q.app U).hom ((hq.2.2.2.2.2 U).1)⟩
  have : IrreducibleSpace Q :=
    Function.Surjective.irreducibleSpace q.continuous q.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced Q

/-- Finite group quotients preserve finite-projective-space quasi-projectivity and
projectivity over a Noetherian base admitting such an immersion over an affine
Noetherian scheme. The quotient is categorical among all schemes. Its fixed-section
structure sheaf and orbit topology use the existing admissible quotient predicate;
geometric fibres are the actual scheme pullbacks. Arbitrary invariant opens inherit
the quotient, including opens which are not quasi-compact.

Source: Rydh, Theorem 4.4, Proposition 4.7 and Remark 4.9, pp. 20--23
(blueprint: lem-per-projective-finite-group-quotient).

Proof:
1. Use exists_ample_of_quasiProjective_tower for the absolute ample source
   (Step 1 of the original plan). Finite type over the Noetherian B makes V Noetherian.
2. Apply exists_finiteGroup_quotient_of_ample to construct Q, r and q, including the
   geometric fibres, categorical quotient and arbitrary invariant-open restrictions
   (Steps 2--7). This construction does not supply projectivity or ampleness.
3. Apply exists_ample_on_admissible_finiteGroup_quotient to the already constructed
   q (Steps 8--9). The ample-to-immersion theorem over Spec Γ(S,⊤), followed by
   ProjectiveSpace.liftBaseChange, gives a finite-space immersion over B (Step 10).
4. If p is projective, universal closedness descends through the surjective q.
   The quasi-projective r is separated, so r is proper. Its finite-space immersion
   is proper by cancellation over a separated target and hence closed (Step 11).
5. If V is integral, the invariant-section injection makes every section ring of
   Q reduced. Surjectivity transports irreducibility. Thus Q is integral (Step 12).
Quasi-compactness of r follows from the Noetherian topology: Q is the surjective
continuous image of the Noetherian V.
-/
theorem exists_finiteGroup_quotient_of_quasiProjective
    (S B V : Scheme.{u}) [IsAffine S] [IsNoetherian S] [IsNoetherian B]
    (b : B ⟶ S) (hb : GabberModification.QuasiProjective b)
    (p : V ⟶ B) [LocallyOfFiniteType p] [QuasiCompact p]
    (hp : GabberModification.QuasiProjective p)
    (H : Type v) [Group H] [Finite H] (a : H →* Aut V)
    (ha : ∀ h : H, (a h).hom ≫ p = p) :
    ∃ (Q : Scheme.{u}) (r : Q ⟶ B) (q : V ⟶ Q),
      q ≫ r = p ∧ IsAdmissibleFiniteSchemeQuotient a q ∧ Surjective q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Q),
        Nonempty ↥(pullback (C := Scheme.{u}) q t) ∧
        ∀ x y : ↥(pullback (C := Scheme.{u}) q t),
          ∃ (h : H) (l : pullback q t ⟶ pullback q t),
            l ≫ pullback.fst q t = pullback.fst q t ≫ (a h).hom ∧
            l ≫ pullback.snd q t = pullback.snd q t ∧ l x = y) ∧
      (∀ (Z : Scheme.{u}) (f : V ⟶ Z), (∀ h : H, (a h).hom ≫ f = f) →
        ∃! g : Q ⟶ Z, q ≫ g = f) ∧
      GabberModification.QuasiProjective r ∧ LocallyOfFiniteType r ∧ QuasiCompact r ∧
      (IsHProjective p → IsHProjective r) ∧ (IsIntegral V → IsIntegral Q) ∧
      ∀ U : V.Opens, (∀ h : H, (a h).hom ⁻¹ᵁ U = U) →
        ∃ (W : Q.Opens) (aU : H →* Aut U.toScheme) (qU : U.toScheme ⟶ W.toScheme),
          q ⁻¹ᵁ W = U ∧
          (∀ h : H, (aU h).hom ≫ U.ι = U.ι ≫ (a h).hom) ∧
          qU ≫ W.ι = U.ι ≫ q ∧ IsAdmissibleFiniteSchemeQuotient aU qU ∧
          ∀ (Z : Scheme.{u}) (f : U.toScheme ⟶ Z),
            (∀ h : H, (aU h).hom ≫ f = f) →
              ∃! g : W.toScheme ⟶ Z, qU ≫ g = f := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian V := {}
  obtain ⟨L, hL, hLamp⟩ := exists_ample_of_quasiProjective_tower S B V b hb p hp
  have : L.IsInvertible := hL
  obtain ⟨Q, r, q, hqr, hq, hsurj, hfib, hcat, hrft, hopen⟩ :=
    exists_finiteGroup_quotient_of_ample B V p L hLamp H a ha
  have : Surjective q := hsurj
  have : LocallyOfFiniteType r := hrft
  have : NoetherianSpace Q :=
    noetherianSpace_of_surjective q q.continuous q.surjective
  have : QuasiCompact r := inferInstance
  obtain ⟨M, hM, hMamp⟩ :=
    exists_ample_on_admissible_finiteGroup_quotient H a q hq L hLamp
  have : M.IsInvertible := hM
  have : LocallyOfFiniteType b := quasiProjective_lft b hb
  have hr : GabberModification.QuasiProjective r :=
    quasiProjective_of_ample S B Q b r M hMamp
  refine ⟨Q, r, q, hqr, hq, hsurj, hfib, hcat, hr, hrft, inferInstance, ?_, ?_, hopen⟩
  · intro hp'
    apply projective_of_surjective_quasiProjective q r hr
    rwa [hqr]
  · intro hV
    have : IsIntegral V := hV
    exact integral_of_admissible_quotient a q hq

end AlgebraicGeometry
