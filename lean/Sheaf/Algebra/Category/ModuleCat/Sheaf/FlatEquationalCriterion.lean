/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses

/-!
# Local equational criterion for flat module sheaves

Source: Stacks Project, Modules on Sites, Tag 08FC, equivalence (1) and (2)
(blueprint: lem-weil-pbc-site-flat-equational-criterion).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace SheafOfModules

/-- Actual covering presieves are cofinal among covering sieves.
Source: Stacks Project, Sites, Definition 00VH and its associated Grothendieck topology.
This is the covering conversion used in Tag 08FC
(blueprint: lem-weil-pbc-site-flat-equational-criterion). -/
private theorem covering_presieve_refinement
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {U : C} {S : Sieve U} (hS : S ∈ J.toGrothendieck U) :
    ∃ Q ∈ J U, Q ≤ S.arrows := by
  classical
  have : J.HasIsos := hJ.1
  induction hS with
  | of U Q hQ => exact ⟨Q, hQ, Sieve.le_generate Q⟩
  | top U =>
      exact ⟨Presieve.singleton (𝟙 U), J.mem_coverings_of_isIso (𝟙 U), by simp⟩
  | pullback U S hS V f ih =>
      obtain ⟨Q, hQ, hle⟩ := ih
      obtain ⟨I, W, g, rfl⟩ := Q.exists_eq_ofArrows
      obtain ⟨P, p, q, hpq, hP⟩ := hJ.2.2 I U W g hQ V f
      refine ⟨Presieve.ofArrows P p, hP, ?_⟩
      intro T a ha
      obtain ⟨i⟩ := ha
      change S (p i ≫ f)
      rw [(hpq i).w]
      exact S.downward_closed (hle _ _ ⟨i⟩) (q i)
  | transitive U S T hS hT ihS ihT =>
      obtain ⟨Q, hQ, hle⟩ := ihS
      have hlocal (V : C) (f : V ⟶ U) (hf : Q f) :
          ∃ P ∈ J V, P ≤ (T.pullback f).arrows := ihT (hle _ _ hf)
      choose P hP hPT using hlocal
      refine ⟨Q.bind (fun V f hf ↦ P V f hf),
        hJ.2.1 U Q (fun V f hf ↦ P V f hf) hQ hP, ?_⟩
      intro V f hf
      obtain ⟨W, g, a, hg, ha, rfl⟩ := hf
      exact hPT W a hg _ _ ha

/-- A module sheaf is flat exactly when each finite relation between its sections locally
factors through a finite free module with zero coefficient relation.
Source: Stacks Project, Modules on Sites, Tag 08FC, (1) iff (2)
(blueprint: lem-weil-pbc-site-flat-equational-criterion).

Proof: Use the existing equational criterion with independent universes and covering
sieves. The actual covering axioms imply, by induction on the generated topology, that
any covering sieve contains a covering presieve: use the identity cover for the maximal
sieve, covering pullbacks for pullback stability, and bind covering presieves for
transitivity. This gives the forward implication. Conversely, generate a covering sieve
from the given covering presieve and restrict its factorization along each further
arrow. Semilinearity of restriction preserves the factorization and the zero coefficient
identities. Thus the covering-sieve criterion gives flatness. Empty coefficient families
and empty covering presieves require no special assumptions. -/
theorem isFlat_iff_local_equationalCriterion
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    (A : Sheaf J.toGrothendieck CommRingCat.{u})
    (M : ringedSiteModules.{u}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) :
    IsFlatOnSite (J := J.toGrothendieck) (R := A) M ↔
      ∀ (U : C) (n : ℕ) (a : Fin n → A.obj.obj (op U))
        (s : Fin n → M.val.obj (op U)),
        (∑ p : Fin n, a p • s p) = 0 →
        ∃ S : Presieve U, S ∈ J U ∧
          ∀ (V : C) (f : V ⟶ U), S f →
            ∃ (l : ℕ) (b : Fin n → Fin l → A.obj.obj (op V))
              (t : Fin l → M.val.obj (op V)),
              (∀ p : Fin n, M.val.map f.op (s p) = ∑ q : Fin l, b p q • t q) ∧
              (∀ q : Fin l, (∑ p : Fin n, A.obj.map f.op (a p) * b p q) = 0) := by
  constructor
  · intro hM U n a s hs
    obtain ⟨S, hS, hfact⟩ :=
      (isFlatOnSite_iff_local_equationalCriterion A M).mp hM U n a s hs
    obtain ⟨T, hT, hTS⟩ := covering_presieve_refinement J _hJ hS
    exact ⟨T, hT, fun V f hf ↦ hfact V f (hTS V f hf)⟩
  · intro hM
    apply (isFlatOnSite_iff_local_equationalCriterion A M).mpr
    intro U n a s hs
    obtain ⟨T, hT, hfact⟩ := hM U n a s hs
    refine ⟨Sieve.generate T, J.generate_mem_toGrothendieck hT, ?_⟩
    intro V f hf
    obtain ⟨W, g, e, he, rfl⟩ := hf
    obtain ⟨l, b, t, hbt, hab⟩ := hfact W e he
    refine ⟨l, fun p q ↦ A.obj.map g.op (b p q),
      fun q ↦ M.val.map g.op (t q), ?_, ?_⟩
    · intro p
      rw [op_comp, PresheafOfModules.map_comp_apply, hbt, map_sum]
      apply Finset.sum_congr rfl
      intro q hq
      exact M.val.map_smul g.op _ _
    · intro q
      have hzero := congrArg (fun x ↦ A.obj.map g.op x) (hab q)
      simpa only [op_comp, Functor.map_comp_apply, map_sum, map_mul, map_zero] using hzero

end SheafOfModules
