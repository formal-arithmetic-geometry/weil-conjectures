/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.RingTheory.Valuation.ValuationRing
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Quasi-compact valuative existence implies universal closedness

Source: Stacks Project, Morphisms of Spaces, Tags 03KA and 03IX
(blueprint: lem-sfb-space-qc-valuative-existence-closed).

The extension field and dominating valuation ring are permitted to vary with the
valuation square. The map `j` is the spectrum of the specified field embedding `e`,
regarded over the base; its normalization and the square over `Spec A` retain all
compatibilities, without any choice of a transport of the generic-point morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact morphism satisfying valuative existence after a dominating extension
is universally closed. Injectivity and `IsLocalHom i` say that the extension valuation
ring contains and dominates the original ring; equivalently its maximal ideal contracts
to the original maximal ideal. The equations for `j` give the field embedding and the
commutative square of valuation spectra, including the generic-point compatibility.
Source: Stacks Project, Morphisms of Spaces, Tag 03KA, with existence as in Tag 03IX
(blueprint: lem-sfb-space-qc-valuative-existence-closed).

Proof:
1. Fix an affine scheme T mapping to Y and put P = X ×_Y T. The fibre-product universal
property (lem-trf-space-fibre-products-etale-covers) transfers valuative existence to
P → T by pairing the lift to X with the prescribed map to T. Quasi-compactness gives
compactness of the point space of P.
2. Choose a surjective etale affine atlas U = Spec B → P
(lem-sfb-qc-space-affine-etale-atlas). A closed subset C of |P| has closed inverse image
D in U by continuity (lem-a1-space-affine-etale-cover). With T = Spec R, the composite
U → T is the spectrum of a ring map (def-weil-affine-spectrum), and its image of D
is the image of C because the atlas is surjective on points.
3. For a specialization y' to y in T, with y' in the image of C, choose a field-valued
representative of a point of C over y' (def-a1-algebraic-space-point-classes). The
prescribed-field probe (lem-sfb-scheme-specialization-prescribed-field-probe) gives a
valuation subring A of this field with closed image y. Apply step 1 to extend the generic
map over a dominating valuation ring A'. Domination puts its closed point over y.
The generic point specializes to this closed point (def-weil-affine-spectrum), so
continuity (lem-a1-space-affine-etale-cover) and invariance of point classes under field
extension show that the closed image remains in C. Thus the image is specialization stable.
4. Apply lem-sfb-affine-spectrum-specialization-stable-image-closed to D and the ring
map R → B. Every closed C therefore has closed image in T. Finally apply
lem-sfb-space-universally-closed-affine-tests to conclude universal closedness. -/
theorem universallyClosed_of_quasiCompact_of_valuativeExistence
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hex : ∀ (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (s : Spec (CommRingCat.of A) ⟶ S)
      (a : yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)) ⟶
        X.obj.obj) (b : yoneda.obj (Over.mk s) ⟶ Y.obj.obj),
      a ≫ f.hom.hom =
        yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) ≫ b →
      ∃ (K' : Type u) (_ : Field K') (A' : Type u) (_ : CommRing A')
        (_ : IsDomain A') (_ : ValuationRing A') (_ : Algebra A' K')
        (_ : IsFractionRing A' K') (i : A →+* A') (e : K →+* K'),
        Function.Injective i ∧ IsLocalHom i ∧
        ∃ (j : Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap A' K')) ≫
            (Spec.map (CommRingCat.ofHom i) ≫ s)) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)),
          j.left = Spec.map (CommRingCat.ofHom e) ∧
          j.left ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) =
            Spec.map (CommRingCat.ofHom (algebraMap A' K')) ≫
              Spec.map (CommRingCat.ofHom i) ∧
          ∃ w : yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom i) ≫ s)) ⟶ X.obj.obj,
            w ≫ f.hom.hom = yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom i)) rfl) ≫
              b ∧
            yoneda.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap A' K'))) rfl) ≫
              w = yoneda.map j ≫ a) :
    MapIsUniversallyClosed f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
