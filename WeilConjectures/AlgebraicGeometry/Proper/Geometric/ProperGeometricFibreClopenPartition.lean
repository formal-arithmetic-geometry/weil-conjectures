/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SteinFiniteFibresResidueFields
import WeilConjectures.AlgebraicGeometry.Integral.IntegralFibreEtaleSplitting
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFibreConnectedPreimage

/-!
# An étale clopen partition adapted to a proper geometric fibre

Source: Stacks Project, More on Morphisms, Tag 0BUI, proof of
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`, Stein splitting paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper family admits, étale locally at a marked base point, a finite clopen
partition whose pieces meet the marked geometric fibre in connected nonempty subsets.
There is no assertion about other fibres and no flatness hypothesis.

Source: Stacks Project, More on Morphisms, Tag 0BUI, proof of
`lemma-proper-flat-nr-geom-conn-comps-lower-semicontinuous`, from the Stein factorization
through the sentence identifying its purely inseparable fibre pieces.
(blueprint: lem-weil-pbc-proper-geometric-fibre-clopen-partition)

Proof: First restrict the base to an affine neighbourhood of the marked point, and
identify it with its affine spectrum. Apply affine Stein factorization to obtain
X → T → S with T affine, the second map integral, and the first proper with
geometrically connected (thus nonempty) fibres. The Stein finite-fibre lemma gives
finitely many points over the marked point and finite residue extensions. Apply
integral-fibre étale splitting to T → S. Pull its finite disjoint clopen covering
back along the base change of X → T. Preimages preserve closedness, openness,
disjointness and the covering property. On the marked fibre each intermediate
piece has one point with purely inseparable residue extension. That fibre is
radicial: its point map is injective and its only residue extension is purely
inseparable. Universal injectivity shows that its base change to the algebraic
closure has at most one point. It is nonempty because the purely inseparable
residue field embeds in the algebraic closure (uniqueness of p-power roots gives
this embedding; in characteristic zero the extension is trivial). Thus its
geometric fibre has exactly one point. Over that point the base-changed Stein
map has connected nonempty fibre, by geometric connectedness. The fibre
homeomorphism identifies it with the corresponding clopen subset of the total
geometric fibre. Compose the pointed étale neighbourhood with the initial open
immersion to the original base, and transport the clopens and their geometric
fibres by the iterated-pullback isomorphisms. If the marked fibre is empty,
integral splitting produces the empty partition after shrinking; the same
argument and all universally quantified connectedness conditions still apply.
-/
theorem Scheme.Hom.exists_etale_geometricFibre_clopen_partition
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g u = s ∧
      ∃ (m : ℕ) (V : Fin m → (pullback f g).Opens),
        (∀ i, IsClosed (V i : Set ↥(pullback f g))) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
        ∀ i, _root_.IsConnected
          ((pullback.fst (pullback.snd f g)
            (Spec.map (CommRingCat.ofHom
              (algebraMap (U.residueField u) (AlgebraicClosure (U.residueField u)))) ≫
                U.fromSpecResidueField u)) ⁻¹' (V i : Set ↥(pullback f g))) := by
  classical
  obtain ⟨A, j, hj, s₀, hs₀⟩ := Scheme.exists_Spec_apply_eq s
  have : IsOpenImmersion j := hj
  let X₀ := pullback f j
  let f₀ : X₀ ⟶ Spec A := pullback.snd f j
  have hstein := f₀.steinFactorization_affine
  have : GeometricallyConnected X₀.toSpecΓ := hstein.2.2.1
  let π := f₀.steinFactorizationBase
  have : IsIntegralHom π := IsIntegralHom.SpecMap_iff.mpr hstein.1
  obtain ⟨hfinite, hres⟩ := f₀.steinFactorizationBase_finite_fibres_residueFields s₀
  obtain ⟨U, g₀, u, hU, hg₀, hgu, m, V, hclosed, _, hdisj, hcover, hpieces⟩ :=
    exists_integral_fibre_etale_splitting π s₀ hfinite hres
  have : Etale g₀ := hg₀
  let g := g₀ ≫ j
  let e := pullbackLeftPullbackSndIso f j g₀
  let a : pullback f g ⟶ X₀ := e.inv ≫ pullback.fst f₀ g₀
  let p : pullback f g ⟶ U := pullback.snd f g
  have he : e.inv ≫ pullback.snd f₀ g₀ = p := by simp [e, f₀, p, g]
  have ha : a ≫ f₀ = p ≫ g₀ := by
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hsquare : IsPullback a p f₀ g₀ :=
    IsPullback.of_iso_pullback ⟨ha⟩ e.symm rfl he
  let q : pullback f g ⟶ pullback π g₀ :=
    pullback.lift (a ≫ X₀.toSpecΓ) p (by
      rw [Category.assoc, Scheme.toSpecΓ_steinFactorizationBase]
      exact ha)
  have hq₁ : q ≫ pullback.fst π g₀ = a ≫ X₀.toSpecΓ := by simp [q]
  have hq₂ : q ≫ pullback.snd π g₀ = p := by simp [q]
  have hqsquare : IsPullback a q X₀.toSpecΓ (pullback.fst π g₀) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd π g₀)
      (v₂₂ := π) (h₃₁ := g₀)
    · rw [hq₂, show X₀.toSpecΓ ≫ π = f₀ from
        Scheme.toSpecΓ_steinFactorizationBase f₀]
      exact hsquare
    · exact hq₁.symm
    · exact IsPullback.of_hasPullback π g₀
  have : GeometricallyConnected q :=
    MorphismProperty.of_isPullback hqsquare inferInstance
  refine ⟨U, g, u, inferInstance, ?_, m, fun i ↦ q ⁻¹ᵁ V i, ?_, ?_, ?_, ?_⟩
  · exact (congrArg j hgu).trans hs₀
  · intro i
    exact (hclosed i).preimage q.continuous
  · intro i j hij
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hdisj hij).eq_bot]
    rfl
  · rw [← Scheme.Hom.preimage_iSup, hcover]
    rfl
  · intro i
    exact q.isConnected_geometricFibre_preimage (pullback.snd π g₀) p hq₂ u (V i)
      (hpieces i).2

end AlgebraicGeometry
