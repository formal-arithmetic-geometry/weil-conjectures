/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveCompletionInsep
import WeilConjectures.AlgebraicGeometry.Field.FieldCurveNormalizationGoodOpen
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpreadMarkedCurveDiagram
import WeilConjectures.AlgebraicGeometry.Good.GoodCurvesFibreDensity

/-!
# Good curve diagrams near a generic point
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A separated, finitely presented, quasi-compact morphism `f : X ⟶ S` whose fibre over a generic
point `η` has dimension at most one admits a good curve diagram after a finite radicial base cover:
there are an open `U ∋ η` and a finite, surjective, universally injective `g : V ⟶ U`, and over `V`
finite étale `T i`, smooth proper curves `Ybar i ⟶ T i` with geometrically connected fibres of
dimension at most one, opens `Y i ⊆ Ybar i` smooth and surjective over `T i` and a finite surjection
`ν : ∐ Y ⟶ X_V`, together with an open `W ⊆ X_V` dense in every fibre over which `ν` is a
thickening.
Source: Stacks Project, Tag 0GK7. -/
theorem exists_good_curves_generic_diagram
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ v : V, Dense ((pullback.snd f (g ≫ U.ι)).fiberι v ⁻¹' (W : Set _))) ∧
          (∀ (i : Fin n) (s : T i),
            Dense (((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _))) ∧
          IsThickening (pullback.snd ν W.ι) := by
  let k : Type u := S.residueField η
  let Z := f.fiber η
  let : Z.Over (Spec (.of k)) := f.fiberOverSpecResidueField η
  have : IsSeparated (Z ↘ Spec (.of k)) := by
    change IsSeparated (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have : QuasiCompact (Z ↘ Spec (.of k)) := by
    change QuasiCompact (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  obtain ⟨K, hK, hkK, hfin, hinsep, n, C, hC, c, Y, B, e, j, L, hLF, hLA,
    q, p, ν, hc, hinj, hcover, hν, hprops, _⟩ :=
    exists_field_curve_completion_insep k Z hdim
  let := hK
  let := hkK
  have := hfin
  have := hinsep
  let := hLF
  let := hLA
  let ZK := pullback (Z ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField η))
    infer_instance
  have hgood := field_curve_normalization_good_open ZK (pullback.snd _ _)
    n C Y hC c e hc hinj hcover
  dsimp only at hgood
  dsimp only [ZK] at hgood
  rw [← hν] at hgood
  obtain ⟨hνfin, hνsurj, W, _, hWcomp, hWthick⟩ := hgood
  have hcomm (i : Fin n) : Sigma.ι Y i ≫ ν ≫ pullback.snd _ _ =
      j i ≫ q i ≫ Spec.map (CommRingCat.ofHom (algebraMap K (L i))) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hcp, hjp, _⟩ := hprops i
    rw [hν, Sigma.ι_comp_desc_assoc]
    exact hcp.trans hjp.symm
  have hL (i : Fin n) : Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) :=
    ⟨(hprops i).1, (hprops i).2.1⟩
  have hj (i : Fin n) : IsOpenImmersion (j i) ∧ Nonempty (Y i) := by
    obtain ⟨_, _, ho, _, hn, _⟩ := hprops i
    exact ⟨ho, hn⟩
  have hq (i : Fin n) : Smooth (q i) ∧ IsProper (q i) ∧
      GeometricallyIrreducible (q i) ∧ topologicalKrullDim (B i) ≤ 1 := by
    obtain ⟨_, _, _, _, _, hsm, hproj, hgeom, hdimB, _⟩ := hprops i
    have := hproj
    exact ⟨hsm, inferInstance, hgeom, hdimB⟩
  have hW : (∀ i, Dense ((Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _))) ∧
      IsThickening (pullback.snd ν W.ι) := by
    refine ⟨?_, hWthick⟩
    intro i
    simpa only [hν, Sigma.ι_comp_desc] using hWcomp i
  obtain ⟨U, hηU, V, g, hgfin, hgsurj, hgrad, T, Y', B', t, j', p', ν', hrest⟩ :=
    exists_spread_marked_curve_diagram f η hη K n L Y B j q ν
      ⟨hνfin, hνsurj⟩ hcomm hL hj hq W hW
  obtain ⟨hν'fin, hν'surj, hcomm', ht, hj', hsm, hp', _, W', hW'surj, hW'thick⟩ := hrest
  have := hν'surj
  have hd := good_curves_fibre_density (pullback.snd f (g ≫ U.ι)) n T Y' B' t j' p' ν'
    hcomm' hj' (fun i ↦ (hp' i).1) (fun i s ↦ (hp' i).2.2 s |>.1) W' hW'surj
  exact ⟨U, hηU, V, g, hgfin, hgsurj, hgrad, n, T, Y', B', t, j', p', ν',
    hν'fin, hν'surj, hcomm', ht, hj', hsm, hp', W', hd.1, hd.2, hW'thick⟩

end AlgebraicGeometry
