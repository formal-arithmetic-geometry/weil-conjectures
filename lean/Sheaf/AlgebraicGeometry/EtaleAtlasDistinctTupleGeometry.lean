/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.SpaceFibreProductComparison
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteComposition
import Sheaf.AlgebraicGeometry.SpaceSeparatedEtaleDiagonalComplement
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Geometry of distinct tuples in an affine étale atlas

Source: Stacks Project, Decent Spaces, Tags 0BBN and 07ST, and Morphisms of Spaces,
Tag 03KN (blueprint: lem-sfb-etale-atlas-distinct-tuple-geometry).

The finite fibre product is specified by its presheaf universal property. Equality loci
are scheme equalizers, and the distinct-tuple scheme is their complementary open.
The geometric-fibre equivalence is characterized by all its coordinate projections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite nonempty products of an affine étale chart over a quasi-separated algebraic
space are quasi-compact separated schemes. Their comparison to the absolute product is
separated and locally quasi-finite. Pairwise equality loci are clopen, and their complement
is a quasi-compact separated scheme étale over the space, with the stated geometric fibres.

Source: Stacks Project, Decent Spaces, Tag 0BBN (lemma-filter-quasi-compact), first two
proof paragraphs; Tag 07ST (lemma-filter-quasi-compact-quasi-separated), final paragraph;
Morphisms of Spaces, Tag 03KN (lemma-fibre-product-after-map), clauses (1) and (4).
(blueprint: lem-sfb-etale-atlas-distinct-tuple-geometry).

Proof:
1. The affine chart U is quasi-compact and absolutely separated by
   lem-weil-pbc-affine-scheme-qcqs, lem-trf-scheme-monomorphism-separated, and
   lem-sc-separated-over-affine-scheme-separated. Quasi-separatedness of X makes U → X
   quasi-compact by lem-sfb-space-qcqs-permanence. Induct on p, forming F_(p+1) = F_p ×_X U.
   Representability and lem-trf-space-fibre-products-etale-covers give a scheme;
   lem-trf-space-chartwise-etale-permanence gives étaleness. Base change preserves
   quasi-compactness by lem-sfb-space-quasicompact-affine-tests. Apply
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open to the whole target to obtain
   quasi-compactness of F_(p+1). The projections give the presheaf wide-pullback cone.
2. The product P_p of p copies of U over Spec Z is affine by iterating
   lem-weil-pbc-fibre-product-affine-spectra. The comparison for p = 1 is the identity.
   Factor the next comparison through F_p ×_(Spec Z) U: its first arrow is the binary
   comparison, and its second arrow is the base change of F_p → P_p. Apply
   lem-sfb-space-fibre-product-comparison, lem-weil-pbc-separated-lqf-base-change,
   lem-a1-scheme-lqf-composition and lem-sfb-space-separated-fp-composition.
   The composite is the coordinate comparison, so is separated and locally quasi-finite.
   Its affine target makes F_p absolutely separated by
   lem-sc-separated-over-affine-scheme-separated.
3. The diagonal of U → X is the pullback of the absolute diagonal of U. It is closed
   by lem-weil-pbc-closed-immersion-base-change and open by
   lem-sfb-space-separated-etale-diagonal-complement. Pull it back along the pair of
   coordinate projections: this is precisely their scheme equalizer. Thus each equality
   locus is open and closed. The complement of their finite union is clopen, hence
   quasi-compact by lem-weil-pbc-closed-in-quasi-compact.
4. The complementary open is separated by lem-weil-pbc-separated-cancellation and
   lem-sfb-space-separated-fp-composition. Its open inclusion is étale by
   lem-weil-pbc-etale-composition-cancellation; compose with F_p → X using
   lem-trf-space-chartwise-etale-permanence to obtain representable étaleness.
5. Evaluate the wide-pullback cone on Spec Ω. Its sections over x are tuples of sections
   of U over x. Such a section factors through the complementary open exactly when no
   two coordinates agree: Spec Ω has one point, and the equality locus represents equality
   of these scheme maps. This gives the equivalence with injective ordered tuples.
   It commutes with every coordinate projection, so is natural under field extension.
   For p = 1 there are no pairs i < j and the complementary open is the whole scheme.
   Empty charts and fibres give empty tuple sets because p is positive. -/
theorem etaleAtlas_distinctTuple_geometry
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (hqs : IsRepresentableWith (fun _ _ q ↦ QuasiCompact q.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [IsAffine U.left]
    (a : yoneda.obj U ⟶ X.obj.obj) (ha : IsEtale a) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (F : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (π : Fin p → (F ⟶ U)) (b : yoneda.obj F ⟶ X.obj.obj)
      (h : ∀ i : Fin p, yoneda.map (π i) ≫ a = b),
      Nonempty (IsLimit (WidePullbackCone.mk b (fun i ↦ yoneda.map (π i)) h)) ∧
      CompactSpace F.left ∧ F.left.IsSeparated ∧
      IsSeparated (Pi.lift π).left ∧ (Pi.lift π).left.IsLocallyQuasiFinite ∧
      (∀ i j : Fin p, i < j →
        IsOpenImmersion (equalizer.ι (π i).left (π j).left) ∧
        IsClosedImmersion (equalizer.ι (π i).left (π j).left)) ∧
      ∃ V : F.left.Opens,
        (V : Set F.left) =
          (⋃ (i : Fin p) (j : Fin p) (_ : i < j),
            Set.range (equalizer.ι (π i).left (π j).left))ᶜ ∧
        IsClosed (V : Set F.left) ∧ CompactSpace V.toScheme ∧ V.toScheme.IsSeparated ∧
        IsEtale
          (yoneda.map (Over.homMk (U := Over.mk (V.ι ≫ F.hom)) V.ι rfl) ≫ b) ∧
        (p = 1 → V = ⊤) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
          (x : X.obj.obj.obj (op (Over.mk s))),
          ∃ e :
            {w : Over.mk s ⟶ Over.mk (V.ι ≫ F.hom) //
              b.app (op (Over.mk s))
                (w ≫ Over.homMk (U := Over.mk (V.ι ≫ F.hom)) V.ι rfl) = x} ≃
            {t : Fin p → (Over.mk s ⟶ U) //
              Function.Injective t ∧ ∀ i : Fin p, a.app (op (Over.mk s)) (t i) = x},
            ∀ (w : {w : Over.mk s ⟶ Over.mk (V.ι ≫ F.hom) //
                b.app (op (Over.mk s))
                (w ≫ Over.homMk (U := Over.mk (V.ι ≫ F.hom)) V.ι rfl) = x})
              (i : Fin p),
              (e w).val i =
                w.val ≫ Over.homMk (U := Over.mk (V.ι ≫ F.hom)) V.ι rfl ≫ π i := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
