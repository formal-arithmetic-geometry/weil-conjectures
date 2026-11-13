/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceMaximalFailure
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceProperComparison
import WeilConjectures.AlgebraicGeometry.GrothendieckExistenceDevissage

/-! # Grothendieck existence for proper schemes

## References

* [Stacks Project, Cohomology of Schemes, Tag 088C]
* [EGA III_1, Theorem 5.1.4]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Completion of coherent modules on a proper scheme over an I-adically complete
Noetherian ring is an equivalence. The kernel ideal of Spec(A/I) → Spec(A) is the ideal
sheaf associated to I; its `comap f` is I O_X. The Noetherian structure on X is supplied
by `isNoetherian_of_locallyOfFiniteType f`, rather than an additional hypothesis.
(Stacks, Proposition 088C; EGA III_1, Theorem 5.1.4) -/
theorem grothendieck_existence_proper (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    (@completion X (isNoetherian_of_locallyOfFiniteType f)
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap f)).IsEquivalence := by
  classical
  by_contra hbad
  obtain ⟨Z, j, hj, hp, hZ, hn, M, hM, hquot⟩ :=
    proper_existence_maximal_failure A I X f hbad
  let := hj
  let := hp
  let := hZ
  let := hn
  let J := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap (j ≫ f)
  obtain ⟨K, hK, H, α, htorsion⟩ := proper_existence_comparison A I (j ≫ f) M
  have hthick : ∀ e : ℕ, 1 ≤ e → ∀ hW : IsNoetherian (K ^ e).subscheme,
      (@completion (K ^ e).subscheme hW (J.comap (K ^ e).subschemeι)).IsEquivalence := by
    intro e he hW
    exact hquot (K ^ e) (hK e he) hW
  exact hM (grothendieck_existence_devissage J K M hthick H α htorsion)

end AlgebraicGeometry
