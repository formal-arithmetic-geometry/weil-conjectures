/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.LerayAcyclicPushforwardLinearComparison
import Sheaf.Paper.QuasiCompactH1Zero
import Sheaf.AlgebraicGeometry.OpenDimOneHigherDirectImageVanishing

/-!
# Open subschemes of a Noetherian affine scheme of dimension at most one

Source: Stacks Project, Varieties, Tag 09N9, lemma-open-in-affine-curve-affine,
Noetherian affine specialization (blueprint: lem-a1-affine-curve-open-affine).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

set_option autoImplicit false

/-- Every open subscheme of the spectrum of a Noetherian commutative ring whose
spectrum has topological Krull dimension at most one is affine, including the empty open.

Source: Stacks Project, Varieties, Tag 09N9, lemma-open-in-affine-curve-affine,
Noetherian affine specialization (blueprint: lem-a1-affine-curve-open-affine).

Proof:
1. The spectrum is a Noetherian space (lem-sc-affine-noetherian-underlying-space).
Every open and every intersection of opens is quasi-compact by
lem-sfb-noetherian-space-compact-subsets. Thus the inclusion of U is quasi-compact
and U is retrocompact. An open immersion is a monomorphism; its diagonal is an
isomorphism, hence quasi-compact, so the inclusion is quasi-separated
(def-weil-finite-type-morphism, def-weil-open-immersion, def-weil-quasi-separated-morphism).
2. By clause (1) of lem-weil-pbc-spec-domain-stalks-function-field each stalk is A_p.
It is Noetherian: contract an ideal J of A_p to I in A, choose finite generators
of I (def-weil-pbc-noetherian-ring), and localize them. If a/s belongs to J,
then a/1 belongs to J since s/1 is a unit, so these localized generators generate J
(def-weil-pbc-localization-at-prime).
3. By lem-sc-scheme-stalk-dimension-generalization-chains the dimension of a stalk
is the supremum of lengths of chains of irreducible closed subsets starting at
the closure of its point. These are among the chains defining the dimension of X,
so each stalk has dimension at most one (def-kun-topological-krull-dimension).
4. For any quasi-coherent module F on U, apply
lem-a1-open-dimension-one-higher-image-vanishing with the retrocompactness and
local-ring properties just checked to obtain vanishing of all positive R^q j_* F.
5. The inclusion is qcqs, so j_* F is quasi-coherent (pqf-lem-pushforward-qcoh).
Affine vanishing gives H^p(X, j_* F) = 0 for p > 0 (pqf-lem-affine-vanishing).
6. The acyclic-pushforward Leray comparison, with auxiliary map the identity of X,
identifies this cohomology with H^p(U, F)
(lem-pc-m1-leray-acyclic-pushforward-linear-comparison).
7. In particular H^1(U, I) vanishes for every quasi-coherent ideal I. Since U is
quasi-compact, lem-pqf-quasicompact-h1-zero proves it is affine. None of these
steps requires U to be nonempty. -/
theorem isAffineOpen_spec_of_isNoetherianRing_of_topologicalKrullDim_le_one
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 1)
    (U : (Spec (CommRingCat.of A)).Opens) : IsAffineOpen U := by
  let X := Spec (CommRingCat.of A)
  have hnoeth (x : X) : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have hlocaldim (x : X) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact (coheight_le_topologicalKrullDim x).trans hdim
  have hretro : IsRetrocompact (U : Set X) :=
    fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  have : CategoryTheory.EnoughInjectives U.toScheme.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives U.toScheme.toRingedSpace).2
  change IsAffine U.toScheme
  apply quasiCompact_affine_of_h1_ideal_zero U.toScheme
  intro I hI
  let F : U.toScheme.Modules := I.toModules
  have : F.IsQuasicoherent := hI
  have hvan (q : ℕ) (hq : 0 < q) :
      CategoryTheory.Limits.IsZero ((Scheme.Modules.higherDirectImage U.ι q).obj F) := by
    exact isZero_higherDirectImage_open_of_stalk_dimension_le_one X hnoeth hlocaldim
      U hretro F hI q hq
  let G := (Scheme.Modules.pushforward U.ι).obj F
  have : G.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated U.ι F
  have : Subsingleton (G.H 1) := Scheme.Modules.subsingleton_H_succ_of_isAffine G 0
  obtain ⟨e⟩ :=
    Scheme.Modules.nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
      U.ι (CategoryTheory.CategoryStruct.id X) F hvan 1
  have : Subsingleton (F.H 1) :=
    ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩
  obtain ⟨c, _⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison U.toScheme 1
  exact ⟨fun x y ↦ (c F).injective (Subsingleton.elim _ _)⟩

end AlgebraicGeometry
