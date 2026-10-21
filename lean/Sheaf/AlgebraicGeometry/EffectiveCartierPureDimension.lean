/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, SHEAF group S6
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pure dimension of an effective Cartier divisor

Source: Stacks Project, Varieties, Tags 0A21 and 0BEV; the component isolation argument
in blueprint main-20261015, finite-cover-curve proof.
(blueprint: lem-zl-effective-cartier-pure-dimension).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The short reduced-closure argument from Modules.HilbertPolynomial, kept private. -/
private theorem integral_closure_subscheme {T : Scheme.{u}} (x : T) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {x}, isClosed_closure⟩).subscheme := by
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {x}, isClosed_closure⟩ : TopologicalSpace.Closeds T)
  have hr : Set.range J.subschemeι = closure {x} := by
    rw [J.range_subschemeι]
    simp [J]
  have h := J.subschemeι.isClosedEmbedding.isEmbedding
  have hirr : IsIrreducible (Set.range J.subschemeι) :=
    hr ▸ isIrreducible_singleton.closure
  have := Subtype.irreducibleSpace hirr
  have hu := (IrreducibleSpace.isIrreducible_univ (Set.range J.subschemeι)).image
    h.toHomeomorph.symm h.toHomeomorph.symm.continuous.continuousOn
  rw [Set.image_univ, h.toHomeomorph.symm.surjective.range_eq] at hu
  have := (irreducibleSpace_def _).mpr hu
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Every irreducible component of a Cartier divisor on an integral finite-type scheme
of dimension d has dimension d-1, including when the divisor is disconnected.

Source: Stacks Project, Tags 0A21 and 0BEV.
(blueprint: lem-zl-effective-cartier-pure-dimension).
Proof: Isolate a nonempty open of one component by removing the other components.
Lift that open to the ambient scheme. Cartier dimension drop computes its dimension.
The reduced induced scheme of the chosen component is integral; its nonempty open
has the same dimension as the component. These two open spaces are homeomorphic.
-/
theorem Scheme.IdealSheafData.isPureDimension_of_isInvertible
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : 1 ≤ d) (hX : X.IsPureDimension d)
    (J : X.IdealSheafData) (hJ : J.IsInvertible) :
    J.subscheme.IsPureDimension (d - 1) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hdim : topologicalKrullDim X = (d : WithBot ℕ∞) := by
    have h := hX Set.univ (by simp only [irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff])
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).symm.trans h
  have : TopologicalSpace.NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  intro Z hZ
  obtain ⟨o, ho, hone, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨a, ha, hao⟩ := J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp ho
  let A : X.Opens := ⟨a, ha⟩
  have hA : Nonempty A := by
    obtain ⟨z, hz⟩ := hone
    exact ⟨⟨J.subschemeι z, by change J.subschemeι z ∈ a; rwa [← hao] at hz⟩⟩
  let E := (J.comap A.ι).subscheme
  let e : E ⟶ J.subscheme := (J.comapIso A.ι).hom ≫ pullback.snd A.ι J.subschemeι
  have he : IsOpenImmersion e := by dsimp only [e]; infer_instance
  have herange : Set.range e = o := by
    have hr : Set.range (J.comapIso A.ι).hom = Set.univ :=
      (J.comapIso A.ι).hom.homeomorph.surjective.range_eq
    dsimp only [e]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hr, Set.image_univ,
      Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    exact hao
  have hE : Nonempty E := by
    obtain ⟨z, hz⟩ := hone
    rw [← herange] at hz
    exact ⟨hz.choose⟩
  have : QuasiCompact (A.ι ≫ f) := inferInstance
  have hAdim : topologicalKrullDim A = (d : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_eq f A).trans hdim
  have hEdim : topologicalKrullDim E = ((d - 1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isInvertible k A (A.ι ≫ f) d hd hAdim
      (J.comap A.ι) (hJ.comap_of_isOpenImmersion A.ι)
  let z := hZ.1.genericPoint
  have hcl : closure ({z} : Set J.subscheme) = Z :=
    (hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)).def
  let C := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({z} : Set J.subscheme), isClosed_closure⟩ : TopologicalSpace.Closeds J.subscheme)
  have : IsIntegral C.subscheme := integral_closure_subscheme z
  let W : C.subscheme.Opens := C.subschemeι ⁻¹ᵁ ⟨o, ho⟩
  have hrC : Set.range C.subschemeι = Z := by
    rw [C.range_subschemeι]
    change closure ({z} : Set J.subscheme) = Z
    exact hcl
  have hW : Nonempty W := by
    obtain ⟨y, hy⟩ := hone
    obtain ⟨x, rfl⟩ := (hrC ▸ hoZ hy : y ∈ Set.range C.subschemeι)
    exact ⟨⟨x, hy⟩⟩
  have hWdim : topologicalKrullDim W = topologicalKrullDim C.subscheme :=
    topologicalKrullDim_opens_eq (C.subschemeι ≫ J.subschemeι ≫ f) W
  have hCdim : topologicalKrullDim C.subscheme = topologicalKrullDim Z := by
    rw [← hrC]
    exact C.subschemeι.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range
  have hWo : topologicalKrullDim W = topologicalKrullDim o :=
    IsHomeomorph.topologicalKrullDim_eq _
      (C.subschemeι.isClosedEmbedding.isEmbedding.homeomorphOfSubsetRange
        (by rwa [hrC])).isHomeomorph
  have hEo : topologicalKrullDim E = topologicalKrullDim o := by
    rw [← herange]
    exact e.isOpenEmbedding.isEmbedding.topologicalKrullDim_eq_range
  exact hCdim.symm.trans (hWdim.symm.trans (hWo.trans (hEo.symm.trans hEdim)))

end AlgebraicGeometry
