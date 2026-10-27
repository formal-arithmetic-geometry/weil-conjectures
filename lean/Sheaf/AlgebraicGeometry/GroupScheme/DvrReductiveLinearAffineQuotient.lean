module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FreeFlatGroupSpaceQuotient

/-! # A reductive group over a DVR has an affine linear homogeneous quotient

Source: Milne, Basic Theory of Affine Group Schemes, VIII, Aside 9.4, pp.125--126;
Alper, Adequate moduli spaces and geometrically reductive group schemes,
Corollary 9.7.7, p.528 (blueprint: lem-sfb-dvr-reductive-linear-affine-quotient).

The coset presheaf is the pointwise coequalizer of projection and right action.
Its arrow to the represented quotient has the sheafification universal property,
on the big fppf site after every scheme base change. All pulled-back maps are the
images of the original maps under the canonical pullback functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth affine finite-type group over a DVR with reductive geometric fibres
embeds in GL_n for n positive, with affine represented right-coset quotient.
The torsor's space is identified with GL_n, and its action is right multiplication
through the specified embedding. For every base change the actual pulled-back
projection and action retain the torsor square and the sheafification property.
The coequalizer in presheaves of sets is precisely the presheaf of right cosets.

Source: Milne, Basic Theory of Affine Group Schemes, VIII, Aside 9.4, pp.125--126;
Alper, Corollary 9.7.7 and Proposition 9.7.8, p.528
(blueprint: lem-sfb-dvr-reductive-linear-affine-quotient).

Proof:
1. Smoothness gives flatness and local finite presentation by
   sbc-lem-smooth-criterion. Affineness gives finite presentation and converts
   flatness to flatness of the coordinate algebra B. Multiplication, unit and
   inverse give its Hopf structure (def-sfb-affine-coordinate-hopf-algebra).
   Using lem-weil-pbc-fibre-product-affine-spectra and the tensor pushout property,
   apply lem-sfb-dvr-comodule-finite-free-lattice to the regular coaction and a
   finite set containing 1 and algebra generators. Its rank n is positive.
2. A basis gives matrix coefficients c_ij. Coassociativity, counit and antipode
   make their matrix invertible. The map from the GL_n coordinate algebra to B
   is surjective, since the basis vectors are linear combinations of c_ij and
   contain the algebra generators. Thus its spectrum is a closed group embedding.
3. Right multiplication, viewed as the left action h.l = l i(h)^(-1), is free.
   The surjective coordinate map makes the embedding a monomorphism by the affine
   fibre-product formula. Apply lem-sfb-free-flat-group-space-quotient to obtain
   Q as an algebraic space, with local fppf lifts and the torsor square.
4. The fibre hypotheses give invariant power lifting by
   lem-sfb-reductive-ring-invariant-power-lifting. Apply
   lem-sfb-power-reductive-free-affine-quotient to conclude Q is affine and the
   projection is finitely presented. These data form RepresentedRightTorsor.
5. After any scheme base change, sections of Q locally lift along the pulled-back
   projection. The pulled-back torsor square identifies two lifts exactly when
   they differ by H. Gluing their images into any sheaf gives the unique factor
   through Q, the universal property of def-weil-pbc-sheafification. The action,
   projection and torsor square themselves pull back, so these identifications
   commute with the quotient map as well as with its representing scheme. -/
theorem exists_dvr_reductive_linear_affine_quotient
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (H : Grp (Over (Spec (.of A))))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsReductive
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj H)) :
    ∃ (n : ℕ) (_ : 1 ≤ n)
      (i : H ⟶ Grp.mk (GeneralLinearGroup (ULift.{u} (Fin n)) A)),
      IsClosedImmersion i.hom.hom.left ∧
      ∃ (Q : Over (Spec (.of A))) (P : RepresentedRightTorsor H Q)
        (e : P.space ≅ GeneralLinearGroup (ULift.{u} (Fin n)) A),
        IsAffineHom Q.hom ∧
        (∀ (R : Over (Spec (.of A))) (p : R ⟶ P.space) (h : R ⟶ H.X),
          lift p h ≫ P.action ≫ e.hom = (p ≫ e.hom) * (h ≫ i.hom.hom)) ∧
        ∀ (T : Scheme.{u}) (f : T ⟶ Spec (.of A)),
          Flat ((Over.pullback f).map P.projection).left ∧
          Surjective ((Over.pullback f).map P.projection).left ∧
          LocallyOfFinitePresentation ((Over.pullback f).map P.projection).left ∧
          QuasiCompact ((Over.pullback f).map P.projection).left ∧
          QuasiSeparated ((Over.pullback f).map P.projection).left ∧
          IsPullback ((Over.pullback f).map (fst P.space H.X))
            ((Over.pullback f).map P.action)
            ((Over.pullback f).map P.projection) ((Over.pullback f).map P.projection) ∧
          Presheaf.IsSheaf (Scheme.fppfTopology.over T)
            (yoneda.obj ((Over.pullback f).obj Q)) ∧
          ∃ eta : coequalizer (yoneda.map ((Over.pullback f).map (fst P.space H.X)))
              (yoneda.map ((Over.pullback f).map P.action)) ⟶
                yoneda.obj ((Over.pullback f).obj Q),
            coequalizer.π _ _ ≫ eta = yoneda.map ((Over.pullback f).map P.projection) ∧
            ∀ Z : Sheaf (Scheme.fppfTopology.over T) (Type u),
              Function.Bijective
                (fun g : yoneda.obj ((Over.pullback f).obj Q) ⟶ Z.obj ↦ eta ≫ g) := by
  sorry

end AlgebraicGeometry
