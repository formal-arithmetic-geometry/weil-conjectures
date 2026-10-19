/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatSingletonFibreChart
import Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatDiscriminantBranchSupport
import Sheaf.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The local ramification criterion for a finite flat morphism

Source: Stacks Project, Tag 0BJH.
(blueprint: lem-sbc-finite-flat-codimension-one-etale-neighbourhood)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite flat morphism is etale near a nongeneric point if it is unramified
at all dimension-one generalizations of that point.

Source: Stacks Project, Tag 0BJH (pione-lemma-ramification-quasi-finite-flat).
(blueprint: lem-sbc-finite-flat-codimension-one-etale-neighbourhood)

Proof: Positive dimension of the source stalk means the point is not the generic
point of an irreducible component. Finiteness implies quasi-finiteness. The
neighbourhood hypotheses express unramifiedness at each indicated generalization.
These are the four hypotheses of Tag 0BJH. For completeness its argument is:
work etale locally on source and target to make the source point the unique
point above its image (Stacks 02LK); etale maps preserve local dimensions and
unramifiedness, so the hypotheses persist, and etaleness descends. The finite
flat morphism is finite locally free, and
its discriminant cuts out a locally principal closed subscheme of the target
whose support is exactly the branch locus. If the image point belongs to this
locus, equality of source and target local dimensions (Stacks 00ON) and the
locally principal locus lemma (Stacks 0BJG) give a dimension-one generalization
in it, including when the discriminant vanishes identically. A ramified point
above that generalization
specializes to the original source point because the morphism is finite and
there is only one point in the original fibre. Flatness and finite fibres
identify the source and target local dimensions. This gives a dimension-one
ramified generalization, contrary to the hypothesis. Thus the morphism is
etale at the point. The etale locus is open and gives the required neighbourhood.
The criterion is vacuous on empty sources; a zero-dimensional source point is
excluded by the explicit positive-dimension hypothesis. -/
theorem exists_etale_neighbourhood_of_finite_flat_of_codimension_one
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (x : X)
    (hpos : (0 : WithBot ℕ∞) < ringKrullDim (X.presheaf.stalk x))
    (hunram : ∀ x' : X, Specializes x' x →
      ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ V : X.Opens, x' ∈ V ∧ FormallyUnramified (V.ι ≫ f)) :
    ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f) := by
  obtain ⟨Z, T, a, _, g, z, ha, _, hg, hflat, hZ, hT, _, haz, hsingle, hlocus⟩ :=
    exists_finite_flat_singleton_fibre_chart f x
  have := ha
  have := hg
  have := hflat
  have := hZ
  have := hT
  have hdim (w : Z) : ringKrullDim (Z.presheaf.stalk w) =
      ringKrullDim (T.presheaf.stalk (g w)) := by
    simp only [ringKrullDim_stalk_eq_coheight]
    rw [g.coheight_apply_of_flat w]
  have hadim (w : Z) : ringKrullDim (Z.presheaf.stalk w) =
      ringKrullDim (X.presheaf.stalk (a w)) := by
    simp only [ringKrullDim_stalk_eq_coheight]
    rw [a.coheight_apply_of_flat w]
  obtain ⟨J, hJ, hbranch⟩ := exists_locallyPrincipal_branch_ideal_of_finite_flat g
  have hz : ∃ V : Z.Opens, z ∈ V ∧ Etale (V.ι ≫ g) := by
    by_contra hn
    have ht : g z ∈ J.support := (hbranch (g z)).2 ⟨z, rfl, hn⟩
    have htpos : (0 : WithBot ℕ∞) < ringKrullDim (T.presheaf.stalk (g z)) := by
      rw [← hdim z, hadim z, haz]
      exact hpos
    obtain ⟨t, hspec, htJ, htdim⟩ :=
      exists_dimension_one_generalization_in_locallyPrincipal_support J hJ (g z) ht htpos
    obtain ⟨w, hwt, hwbad⟩ := (hbranch t).1 htJ
    have hwz : Specializes w z := by
      have hc : g z ∈ closure (g '' ({w} : Set Z)) := by
        rw [Set.image_singleton, hwt]
        exact specializes_iff_mem_closure.mp hspec
      obtain ⟨v, hv, hvg⟩ := g.isClosedMap.closure_image_subset {w} hc
      have hvz : v = z := hsingle v hvg
      subst v
      exact specializes_iff_mem_closure.mpr hv
    have hwdim : ringKrullDim (X.presheaf.stalk (a w)) = 1 := by
      rw [← hadim w, hdim w, hwt]
      exact htdim
    have hawx : Specializes (a w) x := by
      rw [← haz]
      exact hwz.map a.continuous
    obtain ⟨V, hwV, hV⟩ := hunram (a w) hawx hwdim
    have : FormallyUnramified (V.ι ≫ f) := hV
    have : Etale (V.ι ≫ f) := Etale.of_formallyUnramified_of_flat (V.ι ≫ f)
    exact hwbad ((hlocus w).2 ⟨V, hwV, inferInstance⟩)
  rw [← haz]
  exact (hlocus z).1 hz

end AlgebraicGeometry.Scheme
