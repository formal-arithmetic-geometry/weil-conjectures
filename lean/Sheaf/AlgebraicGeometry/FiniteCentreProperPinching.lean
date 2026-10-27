module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine
import Sheaf.AlgebraicGeometry.FerrandSchemePushout
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Proper pinching along a finite centre

Source: Stacks Project, More on Morphisms, Tags 0E25, 0E26, 0E27;
More on Algebra, Tag 00IT; Properties, Tag 01ZY
(blueprint: lem-sfb-finite-centre-proper-pinching).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pinching a projective scheme over a Noetherian affine base along a finite centre
and a finite surjection gives a proper, finitely presented scheme and a finite surjection.
Source: Stacks Project, Tags 0E25, 0E26, 0E27, 00IT, 01ZY
(blueprint: lem-sfb-finite-centre-proper-pinching).

The section-ring pullback for every open expresses the structure-sheaf fibre product,
since limits of ring sheaves are computed on sections. In the simultaneous affine charts,
`pullback` is the ring of pairs with equal images, with coordinatewise ring operations;
the equations for the spectrum maps specify its projections. The last clause is the
pushout property in schemes after every open restriction. All schemes may be empty.

Proof plan, following the node:
1. Choose a finite projective-space embedding using def-kun-projective.
   Apply lem-kun-projective-implies-proper and
   lem-weil-pbc-projective-ample-invertible to get properness and an ample invertible L.
2. Apply lem-sc-ample-finite-set-affine to the finite image of Z; its points need not
   be closed. The resulting affine U contains every pinched fibre. By
   pqf-lem-finite-integral-lft, j is integral.
3. Apply lem-sfb-ferrand-scheme-pushout. It supplies the scheme pushout, its structure
   map, closed immersion b, cartesian square, sheaf pullback, affine charts, and
   pushout property under every open restriction.
4. The quotient-space description gives a(X) union b(T) = P. Surjectivity of j
   puts b(T) inside a(X), so a is surjective and c(Z) = b(T). The Ferrand complement
   isomorphism becomes X minus i(Z) isomorphic to P minus b(T).
5. On any affine W in P, a is integral and b is closed, hence both inverse images
   are affine by lem-weil-pbc-closed-immersion-integral-separated-uc. Finiteness of j
   makes the inverse image in Z affine. Write their rings A, E, D, with A onto D;
   the Ferrand open-restriction clause gives W = Spec(A times_D E).
6. Choose E-module generators d_k of D and lifts x_k in A. For x in A, write its
   image as sum beta(e_k)d_k and lift beta(e_k) to r_k in A. Then (r_k,e_k) lies in
   B = A times_D E, while h = x - sum r_k x_k is in ker(A to D), so (h,0) lies in B.
   Thus 1 and the x_k generate A as a B-module. This includes D = 0 with no d_k.
   The affine-local definition def-weil-finite-integral-morphism makes a finite.
7. By pqf-def-locnoeth the affine base is locally Noetherian. By
   lem-weil-pbc-finite-proper, Z and T are proper. The separatedness and finite-type
   clauses of lem-sfb-ferrand-scheme-pushout apply. Properness of X and surjectivity
   of a imply universal closedness of P by lem-weil-pbc-image-universally-closed;
   hence P is proper.
8. By pqf-lem-lft-fp-locnoeth, P is locally of finite presentation. Properness gives
   quasi-compactness, and lem-pc-separated-quasi-separated gives quasi-separatedness;
   these are exactly finite presentation in def-sbc-locally-finite-presentation.
   If Z is empty, surjectivity forces T empty and P = X. If X is empty, so are Z,T,P.
-/
theorem exists_finiteCentre_proper_pinching
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Z X T : Over (Spec (CommRingCat.of R))) (i : Z ⟶ X) (j : Z ⟶ T)
    [IsHProjective X.hom] [IsFinite Z.hom] [IsFinite T.hom]
    [IsClosedImmersion i.left] [IsFinite j.left] [Surjective j.left] [Finite Z.left] :
    IsProper X.hom ∧
      (∃ (L : X.left.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple X.left L hL) ∧
      (∃ U : X.left.Opens, IsAffineOpen U ∧ Set.range i.left ⊆ (U : Set X.left)) ∧
    ∃ (P : Over (Spec (CommRingCat.of R))) (a : X ⟶ P) (b : T ⟶ P),
      ∃ hs : IsPushout i.left j.left a.left b.left,
      IsProper P.hom ∧ LocallyOfFinitePresentation P.hom ∧
      QuasiCompact P.hom ∧ QuasiSeparated P.hom ∧
      IsFinite a.left ∧ Surjective a.left ∧ IsClosedImmersion b.left ∧
      IsPullback i.left j.left a.left b.left ∧
      (∀ W : P.left.Opens,
        IsPullback (a.left.app W) (b.left.app W) (i.left.app (a.left ⁻¹ᵁ W))
          (j.left.appLE (b.left ⁻¹ᵁ W) ((i.left ≫ a.left) ⁻¹ᵁ W)
            (le_of_eq (congrArg (fun f : Z.left ⟶ P.left ↦ f ⁻¹ᵁ W) hs.w)))) ∧
      (∃ (ι : Type u) (W : ι → P.left.Opens), iSup W = ⊤ ∧ ∀ k : ι,
        IsAffineOpen (W k) ∧ IsAffineOpen (a.left ⁻¹ᵁ W k) ∧
        IsAffineOpen (b.left ⁻¹ᵁ W k) ∧
        IsAffineOpen ((i.left ≫ a.left) ⁻¹ᵁ W k) ∧
        Function.Surjective (i.left.app (a.left ⁻¹ᵁ W k)) ∧
        ∃ e : (W k).toScheme ≅ Spec
            (pullback (i.left.app (a.left ⁻¹ᵁ W k))
              (j.left.appLE (b.left ⁻¹ᵁ W k) ((i.left ≫ a.left) ⁻¹ᵁ W k)
                (le_of_eq (congrArg (fun f : Z.left ⟶ P.left ↦ f ⁻¹ᵁ W k) hs.w)))),
          morphismRestrict a.left (W k) ≫ e.hom = (a.left ⁻¹ᵁ W k).toSpecΓ ≫
            Spec.map (pullback.fst _ _) ∧
          morphismRestrict b.left (W k) ≫ e.hom = (b.left ⁻¹ᵁ W k).toSpecΓ ≫
            Spec.map (pullback.snd _ _)) ∧
      (∃ (U : X.left.Opens) (V : P.left.Opens) (e : U.toScheme ≅ V.toScheme),
        (U : Set X.left) = (Set.range i.left)ᶜ ∧
        (V : Set P.left) = (Set.range b.left)ᶜ ∧
        e.hom ≫ V.ι = U.ι ≫ a.left) ∧
      (∀ V : P.left.Opens,
        IsPushout
          ((Over.pullback V.ι).map
            (Over.homMk i.left rfl : Over.mk (i.left ≫ a.left) ⟶ Over.mk a.left)).left
          ((Over.pullback V.ι).map
            (Over.homMk j.left hs.w.symm : Over.mk (i.left ≫ a.left) ⟶ Over.mk b.left)).left
          (pullback.snd a.left V.ι) (pullback.snd b.left V.ι)) := by
  sorry

end AlgebraicGeometry
