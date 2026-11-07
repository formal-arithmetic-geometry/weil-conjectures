/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationChart
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverPoint

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The punctured root cover has an affine etale chart containing a lift of y.

Source: Stacks Project, Tag 0EYG, off-divisor branch; standard basic-open localization.
(blueprint: lem-sbc-root-split-away-localization-point)

Proof: Put A=R[T]/(T^n-g), h=algebraMap R A g, and take the actual localization
S=A[1/h], with phi the composite R to A to S. The basic-open localization
isomorphism gives e:Spec S to V and its compatibility with Spec phi. Over
U=D(g) the monic polynomial gives a finite free algebra of positive rank n.
The root t is invertible because t^n=g is invertible, and n is invertible by hn.
Thus the derivative n*t^(n-1) is invertible and the cover V to U is etale.
It is surjective: each residue-field fibre is a nonzero algebra of dimension n,
so has a prime ideal. Since hy places y in U, choose a point of V over y and
transport it through e to z. Open immersions are etale, so Spec phi is etale.
The localization makes phi(g) a unit. This constructs the ring explicitly;
only a point over the prescribed point is chosen, not data for a definition.
For n=1 the cover is just D(g); n=0 is excluded. A point y excludes the zero
base ring, while g=0 makes hy impossible. No regularity is used.
-/
theorem root_split_away_localization_point
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    (y : Spec R) (hy : g ∉ y.asIdeal) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S) (e : Spec S ≅ V.toScheme),
      e.hom ≫ V.ι ≫ q = Spec.map (CommRingCat.ofHom φ) ∧
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧ IsUnit (φ g) := by
  intro A N q V
  obtain ⟨S, φ, e, he, hunit⟩ := root_split_away_localization_chart R g n
  have het : Etale (V.ι ≫ q) := root_split_away_cover_etale R g n hn
  obtain ⟨v, hv⟩ : ∃ v : V.toScheme, (V.ι ≫ q) v = y :=
    root_split_away_cover_point R g n hn.1 y hy
  have hz : (Spec.map (CommRingCat.ofHom φ)) (e.inv v) = y := by
    rw [← he]
    change q (V.ι (e.hom (e.inv v))) = y
    rw [Scheme.inv_hom_apply e v]
    exact hv
  have hφ : Etale (Spec.map (CommRingCat.ofHom φ)) := by
    rw [← he]
    infer_instance
  exact ⟨S, φ, e.inv v, e, he, hφ, hz, hunit⟩

end AlgebraicGeometry.Scheme
