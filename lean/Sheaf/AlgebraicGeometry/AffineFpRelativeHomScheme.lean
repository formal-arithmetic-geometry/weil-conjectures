/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.ExistsSchemeOfZariskiCocycle
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine finitely presented relative Hom schemes

Source: Stacks Project, More on Morphisms, Tags 0BL3 and 05Y6, with a finite
presentation of the target algebra (blueprint: lem-sfb-affine-fp-relative-hom-scheme).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Relative Hom from a finite locally free source into an affine finitely presented target
is represented by an affine finitely presented scheme over the base.

Source: Stacks Project, More on Morphisms, Tags 0BL3 and 05Y6, finite-presentation
specialization (blueprint: lem-sfb-affine-fp-relative-hom-scheme).

The equivalences `e` have exactly the relative morphisms over each test scheme as codomain.
Their naturality equation compares maps to `Y` after the canonical projections. Since both
relative morphisms are over the smaller test scheme, its other projection is already fixed;
the pullback universal property identifies this equation with restriction by base change.
The last conjunct exhibits every affine base restriction as the spectrum of a polynomial
algebra in finitely many variables modulo finitely many relations, over that affine open.

Proof:
1. The finite locally free source has locally free structure-sheaf pushforward by
   lem-sc-finite-pushforward-locally-free. Refine its trivializing cover by affine opens
   (lem-weil-pbc-affine-opens-basis). Finite-morphism permanence and the open-preimage
   fibre-product identification give charts X_i = Spec B_i with finite bases over R_i.
   Their ranks may vary and may be zero.
2. Affineness gives Y_i = Spec C_i. The affine-open finite-presentation characterization
   (lem-weil-pbc-lfp-affine-opens-finite-presentation) gives finite presentations of C_i
   over R_i, without a Noetherian assumption.
3. Extending this presentation to B_i gives E_i = B_i tensor C_i, by the polynomial,
   quotient and tensor universal properties: the maps send generators to the same
   polynomial classes, and their composites fix each algebra generator.
4. Apply lem-sfb-finite-free-algebra-map-coordinates to E_i. If the target presentation
   has n generators and m relations and B_i has rank d, the coefficient algebra P_i has
   nd generators and md relations. Tensor uniqueness identifies its natural algebra-map
   bijection with maps C_i to B_i tensor A for every R_i-algebra A.
5. The affine spectrum and fibre-product-of-spectra identifications translate this to
   the relative-Hom bijection on affine tests. At A = P_i the identity supplies the
   universal relative morphism, and the formulas identify the bijection with its pullback.
6. Cover any test scheme by affine opens and their intersections by further affine opens.
   Naturality and injectivity on affine tests give overlap agreement; scheme-morphism
   gluing gives the inverse bijection on all tests. Local uniqueness gives naturality
   under every morphism of tests; intersections need not be affine.
7. On base overlaps, Yoneda identifies the two restricted representing schemes uniquely.
   Yoneda injectivity gives identity transitions and the triple-overlap cocycle.
   lem-galois-glue assembles H and its compatible charts over S.
8. Cover an arbitrary S-test by the inverse images of these base charts. Scheme-morphism
   gluing gives the global bijections and their inverses; uniqueness gives naturality.
9. The affine-local-target criterion proves H affine over S. Its finite presentations
   on the charts prove local finite presentation by target-open locality. Affine-morphism
   permanence gives quasi-compactness and separatedness, hence quasi-separatedness.
10. For any affine base open, its inverse image is affine. Apply the affine-open
    finite-presentation characterization again, and choose finite polynomial generators
    and finitely many ideal generators to obtain the final displayed spectrum.
-/
theorem exists_affine_fp_relativeHomScheme
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    [p.IsFiniteLocallyFree] [IsAffineHom q] [LocallyOfFinitePresentation q]
    [QuasiCompact q] [QuasiSeparated q] :
    ∃ H : Over S,
      IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom ∧
      QuasiCompact H.hom ∧ QuasiSeparated H.hom ∧
      ∃ e : ∀ T : Over S, (T ⟶ H) ≃
        ((Over.pullback T.hom).obj (Over.mk p) ⟶
          (Over.pullback T.hom).obj (Over.mk q)),
        (∀ (T T' : Over S) (a : T' ⟶ T) (g : T ⟶ H),
          (e T' (a ≫ g)).left ≫ pullback.fst q T'.hom =
            pullback.map p T'.hom p T.hom (𝟙 X) a.left (𝟙 S)
              (by simp) (by simp [a.w]) ≫
              (e T g).left ≫ pullback.fst q T.hom) ∧
        ∀ (U : S.Opens) (hU : IsAffineOpen U),
          ∃ (n m : ℕ) (r : Fin m → MvPolynomial (Fin n) Γ(S, U)),
            Nonempty (Over.mk (pullback.snd H.hom U.ι) ≅
              Over.mk (Spec.map (CommRingCat.ofHom
                (algebraMap Γ(S, U)
                  (MvPolynomial (Fin n) Γ(S, U) ⧸ Ideal.span (Set.range r)))) ≫
                hU.isoSpec.inv)) := by
  sorry

end AlgebraicGeometry.Scheme
