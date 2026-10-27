module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange

/-! # Spreading a specified fpqc representation along affine inverse limits

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1 proof,
reductions 3 and 4, printed pp. 5-19--5-20; Stacks Project, Tags 01ZM, 023Q, 02KU.
(blueprint: lem-sfb-fpqc-representation-limit-spreading)
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A specified representation over the affine inverse limit spreads to a finite stage,
provided the fpqc sheaf has a separated finitely presented model on an affine fpqc cover.
The last equation identifies the two representations on every test scheme: the adjunction
transposes a map into the pullback, and `Over.mapComp` and `Over.mapCongr` identify its two
structure maps to S. In particular the isomorphism to Y respects the given representation.

Source: Raynaud, Un critère d'effectivité de descente, Theorem 4.1 proof,
reductions 3 and 4, printed pp. 5-19--5-20; Stacks Project, Tags 01ZM, 023Q, 02KU.
(blueprint: lem-sfb-fpqc-representation-limit-spreading)

Proof:
1. Set B_i = A ×_S T_i and C_i = A ×_S A ×_S T_i. They are affine and qcqs,
   with affine transitions, and their limits are B and C by the fibre-product universal
   property (def-pc-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-limit-affine-transition, lem-weil-pbc-qcqs-morphism-permanence).
2. Spread Y to a finitely presented V_i with a specified limit isomorphism by
   thm-pd-spreading-out (01ZM(1)). The representations give an isomorphism between
   V_i over B and P over B by lem-galois-yoneda-fully-faithful. Choose its orientation
   so that its composition with the representation of P equals that of Y.
3. Spread that isomorphism and its inverse by 01ZM(2), and the two inverse equations
   by 01ZM(3), passing to a common larger index (thm-pd-spreading-out). All models are
   finitely presented over B_i by lem-weil-pbc-qcqs-morphism-permanence.
4. The two local representations of P induce its overlap isomorphism by Yoneda.
   The two resulting maps from V_i over C_i agree over C by the chosen representation
   of Y. Spread this equation by 01ZM(3), obtaining actual overlap compatibility.
5. For every H over T_i, H ×_S A covers H by lem-weil-pbc-fpqc-covering-axioms.
   The local representation and the overlap equation identify the two covering
   equalizers. On the scheme side use lem-weil-pbc-fpqc-representable-descent (023Q);
   on the F side use the assumed sheaf axiom. These bijections are natural because
   their local restrictions commute and descent is unique. They give the representation.
6. B_i → T_i is flat and surjective by the fpqc covering axioms and definition,
   and quasi-compact since both schemes are affine (lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-qcqs-morphism-permanence). The model is separated over B_i by
   lem-weil-pbc-separated-base-change, hence over T_i by
   lem-weil-pbc-fpqc-descend-separated. Finite presentation was preserved throughout.
   Finally both representations agree over B by construction, so they agree over T
   by injectivity of the covering equalizer map. No transition or projection is
   assumed flat or surjective. -/
theorem exists_fpqc_representation_at_affine_limit_stage
    {S A : Scheme.{u}} [IsAffine S] [IsAffine A]
    (p : A ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
    (F : (Over S)ᵒᵖ ⥤ Type v)
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) F)
    (P : Over A) (rP : ((Over.map p).op ⋙ F).RepresentableBy P)
    [IsSeparated P.hom] [LocallyOfFinitePresentation P.hom]
    [QuasiCompact P.hom] [QuasiSeparated P.hom]
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) [∀ i : Iᵒᵖ, IsAffine (D.obj i).left]
    (c : Cone D) (hc : IsLimit c)
    (Y : Over c.pt.left) (rY : ((Over.map c.pt.hom).op ⋙ F).RepresentableBy Y)
    [IsSeparated Y.hom] [LocallyOfFinitePresentation Y.hom]
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom] :
    ∃ (i : Iᵒᵖ) (Yi : Over (D.obj i).left),
      IsSeparated Yi.hom ∧ LocallyOfFinitePresentation Yi.hom ∧
      QuasiCompact Yi.hom ∧ QuasiSeparated Yi.hom ∧
      ∃ rYi : ((Over.map (D.obj i).hom).op ⋙ F).RepresentableBy Yi,
        ∃ e : (Over.pullback (c.π.app i).left).obj Yi ≅ Y,
          ∀ (H : Over c.pt.left) (g : H ⟶ (Over.pullback (c.π.app i).left).obj Yi),
            rY.homEquiv (g ≫ e.hom) =
              F.map (((Over.mapComp (c.π.app i).left (D.obj i).hom).symm ≪≫
                Over.mapCongr ((c.π.app i).left ≫ (D.obj i).hom) c.pt.hom
                  (Over.w (c.π.app i))).app H).inv.op
                (rYi.homEquiv (((Over.mapPullbackAdj (c.π.app i).left).homEquiv H Yi).symm
                  g)) := by
  sorry

end AlgebraicGeometry
