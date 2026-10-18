/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
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
public import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.GoodCurvesNonemptyThickening
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Good curve diagrams near a generic point

Source: Stacks Project, More on Morphisms, Tag 0GK7, lemma-make-good-curves,
assertions (1)-(8) (blueprint: lem-weil-pbc-good-curves-generic-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem dense_fibres_of_componentwise_dense
    {V X : Scheme.{u}} {n : ℕ} (T Y : Fin n → Scheme.{u})
    (a : X ⟶ V) (ν : (∐ Y) ⟶ X) [Surjective ν]
    (q : ∀ i, Y i ⟶ T i) (t : ∀ i, T i ⟶ V)
    (hcomm : ∀ i, Sigma.ι Y i ≫ ν ≫ a = q i ≫ t i)
    (W : X.Opens)
    (hdense : ∀ i s, Dense (((q i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹' (W : Set X))) :
    ∀ v : V, Dense ((a.fiberι v) ⁻¹' (W : Set X)) := by
  intro v
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨x, hx⟩ := hOne
  obtain ⟨y, hy⟩ := ν.surjective (a.fiberι v x)
  have hcover := (sigmaOpenCover Y).exists_eq y
  change ∃ i : Fin n, ∃ yi : Y i, Sigma.ι Y i yi = y at hcover
  obtain ⟨i, yi, hyi⟩ := hcover
  let s := q i yi
  have hqs (z : (q i).fiber s) : q i ((q i).fiberι s z) = s := by
    exact ((q i).range_fiberι s).le ⟨z, rfl⟩
  have hts : t i s = v := by
    have hc := congrArg (fun f : Y i ⟶ V ↦ f yi) (hcomm i)
    simp only [Scheme.Hom.comp_apply] at hc
    rw [hyi, hy] at hc
    exact hc.symm.trans (((a.range_fiberι v).le ⟨x, rfl⟩) : a (a.fiberι v x) = v)
  let F : (q i).fiber s → a.fiber v := fun z ↦
    (a.fiberHomeo v).symm ⟨ν (Sigma.ι Y i ((q i).fiberι s z)), by
      change a (ν (Sigma.ι Y i ((q i).fiberι s z))) = v
      have hc := congrArg (fun f : Y i ⟶ V ↦ f ((q i).fiberι s z)) (hcomm i)
      simp only [Scheme.Hom.comp_apply] at hc
      rw [hc, hqs, hts]⟩
  have hF : Continuous F := by
    apply (a.fiberHomeo v).symm.continuous.comp
    exact (ν.continuous.comp ((Sigma.ι Y i).continuous.comp
      ((q i).fiberι s).continuous)).subtype_mk _
  have hFyi : F ((q i).asFiber yi) = x := by
    apply (a.fiberι v).isEmbedding.injective
    simp [F, s, hyi, hy]
  obtain ⟨z, hzO, hzW⟩ := (hdense i s).inter_open_nonempty
    (F ⁻¹' O) (hO.preimage hF) ⟨(q i).asFiber yi, by
      change F ((q i).asFiber yi) ∈ O
      rw [hFyi]
      exact hx⟩
  refine ⟨F z, hzO, ?_⟩
  simpa [F, Scheme.Hom.comp_apply] using hzW

/-- (blueprint: lem-weil-pbc-good-curves-generic-diagram)
Stacks Project, Tag 0GK7: a separated finitely presented family with generic fibre of
dimension at most one admits a good curve diagram after a finite radicial base cover.

Proof: First construct the good curve presentation with a thickening open meeting every
smooth curve fibre, using `exists_good_curves_nonempty_thickening`. Each smooth completion
with geometrically connected fibres is geometrically irreducible, by the existing
smooth-connected geometry theorem. Its surjective open curve part is therefore also
geometrically irreducible. On each such fibre the inverse image of W is a nonempty open,
hence dense. To prove density on an X-fibre, lift a point of any nonempty open through the
surjection from the coproduct and then into a summand. Restrict to the curve fibre over the
image point in T_i. The induced continuous map to the X-fibre pulls the given open back to
a nonempty open; the density just proved makes that pullback meet W. The proved private
helper implements this argument using the homeomorphisms between scheme fibres and the
corresponding topological fibres. All other clauses are those of the initial presentation. -/
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
  obtain ⟨U, hηU, V, g, hgfin, hgsurj, hginj, n, T, Y, Ybar, t, j, p, ν,
    hνfin, hνsurj, hcomm, ht, hj, hq, hp, W, hWmeet, hWthick⟩ :=
    exists_good_curves_nonempty_thickening f η hη hdim
  have : Surjective ν := hνsurj
  have hdense : ∀ (i : Fin n) (s : T i),
      Dense (((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) ⁻¹' (W : Set _)) := by
    intro i s
    have : IsOpenImmersion (j i) := hj i
    have : Smooth (p i) := (hp i).1
    have : GeometricallyConnected (p i) :=
      (GeometricallyConnected.iff_geometricallyConnected_fiber (p i)).mpr ((hp i).2.2 · |>.1)
    have : GeometricallyIrreducible (p i) :=
      GeometricallyIrreducible.of_smooth_of_geometricallyConnected (p i)
    have : Surjective (j i ≫ p i) := (hq i).2
    have : GeometricallyIrreducible (j i ≫ p i) := inferInstance
    have : IrreducibleSpace ((j i ≫ p i).fiber s) := inferInstance
    exact (W.isOpen.preimage
      ((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν).continuous).dense (hWmeet i s)
  refine ⟨U, hηU, V, g, hgfin, hgsurj, hginj, n, T, Y, Ybar, t, j, p, ν,
    hνfin, hνsurj, hcomm, ht, hj, hq, hp, W, ?_, hdense, hWthick⟩
  exact dense_fibres_of_componentwise_dense T Y (pullback.snd f (g ≫ U.ι)) ν
    (fun i ↦ j i ≫ p i) t hcomm W hdense

end AlgebraicGeometry
