/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences
import Sheaf.AlgebraicGeometry.ProEtale.FiniteProductWContractible
import Sheaf.AlgebraicGeometry.ProEtale.SingleWContractibleCover
import Sheaf.AlgebraicGeometry.ProEtale.SingleAffineHypercover

/-!
# Hypercovers by single w-contractible affines

Source: the blueprint of the Weil conjectures, chapter `sec-proetale-coefficients`,
unit `sk-prop-pe-hypercover` (blueprint: det-pe-hypercover-existence); Stacks Project,
Tag 09A1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped Simplicial

namespace AlgebraicGeometry

/-- Hypercovers by single spectra of w-contractible rings.

Source: Stacks Project, Tag 09A1, `lemma-w-contractible-hypercovering`, part (2);
Tags 094K, 0DAV and 0DB2 (blueprint: det-pe-hypercover-existence).
The simplicial object is valued in `Over U`, so its augmentation is part of its data
and its matching limits are relative to `U`. In degree one the matching object is
`W₀ ×_U W₀`. Covering predicates are tested on the underlying arrows in `X.ProEt`.

Proof:
1. Apply the finite-product theorem
   [det-pe-hypercover-product-wcontractible], proved directly using the disjoint-union
   decomposition of the prime spectrum and the evaluation-localization isomorphisms.
2. Apply [det-pe-hypercover-single-cover]. Its proof starts with an affine singleton
   cover and composes it with the faithfully flat ind-etale w-contractible extension
   of its coordinate ring. Stability of the precoverage under composition gives the cover.
3. Apply [det-pe-hypercover-single-affine] for the geometric simplicial construction
   and its covering proper-face matching arrows. Its proof realizes the finite-basis
   formal hypercover, proves the matching coverings, and chooses spectrum representatives.
4. In each degree rewrite by the supplied spectrum equality. The affine assertion of
   [det-pe-weak-contractible-equivalences] supplies the required representable-sheaf
   splitting property. Assemble the three clauses.
-/
theorem exists_proetale_hypercover_single_affine
    (X : Scheme.{u}) (U : X.ProEt)
    (hUqc : CompactSpace U.left) (hUqs : QuasiSeparatedSpace U.left) :
    (∀ (I : Type u) [Finite I] (D : I → Type u) [∀ i, CommRing (D i)]
      [∀ i, IsWContractibleRing (D i)], IsWContractibleRing (∀ i, D i)) ∧
      (∀ (V : X.ProEt), CompactSpace V.left →
        ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f)
          (g : @Scheme.ProEt.mk X _ f hf ⟶ V),
          IsWContractibleRing D ∧
            Presieve.singleton g ∈ (Scheme.ProEt.precoverage X) V) ∧
      ∃ (W : SimplicialObject (Over U)),
        (∀ (r : ℕ),
          ∃ (D : CommRingCat.{u}) (f : Spec D ⟶ X) (hf : WeaklyEtale f),
            IsWContractibleRing D ∧
              (W _⦋r⦌).left = @Scheme.ProEt.mk X _ f hf ∧
              (∀ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
                (φ : F ⟶ (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left)
                [Epi φ],
                ∃ s : (Scheme.ProEt.topology X).uliftYoneda.{u + 1}.obj (W _⦋r⦌).left ⟶ F,
                  s ≫ φ = 𝟙 _)) ∧
        Presieve.singleton (W _⦋0⦌).hom ∈
          (Scheme.ProEt.precoverage X) U ∧
        (∀ (r : ℕ),
          ∃ (c : Cone (SimplicialObject.properFaceDiagram W (r + 1)))
            (μ : W _⦋r + 1⦌ ⟶ c.pt),
            Nonempty (IsLimit c) ∧
              Presieve.singleton μ.left ∈ (Scheme.ProEt.precoverage X) c.pt.left ∧
              (∀ (a : SimplicialObject.ProperFaceCategory (r + 1)),
                μ ≫ c.π.app (Opposite.op a) = W.map a.obj.hom.op)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _ D _ _
    exact isWContractibleRing_pi_of_finite I D
  · intro V hVqc
    exact exists_single_wContractible_affine_cover X V hVqc
  · obtain ⟨W, hterm, hzero, hmatching⟩ :=
      exists_single_affine_wContractible_hypercover X U hUqc hUqs
    refine ⟨W, ?_, hzero, hmatching⟩
    intro r
    obtain ⟨D, f, hf, hD, hW⟩ := hterm r
    refine ⟨D, f, hf, hD, hW, ?_⟩
    rw [hW]
    let := hD
    let := hf
    exact (Scheme.proetale_weakContractible_equivalences X (Scheme.ProEt.mk f)).2.2 D f

end AlgebraicGeometry
