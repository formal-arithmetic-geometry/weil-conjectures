module

public import Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Mathlib.AlgebraicGeometry.Gluing

/-! # The affine comparison for positive-copy relative Proj

Source: Stacks Project, Morphisms, Tag 0B3I (lemma-finite-projective), its explicit
positive-copy verification; Constructions, Tags 01M4, 01MB, 01NO and 01NQ
(blueprint: lem-trf-positive-copy-proj-affine-comparison).

The input uses the affine-basis presentation of the existing relative Proj construction.
Linear identifications of its homogeneous pieces with `positiveCopyPiece` specify precisely
the positive-copy algebra, including its multiplication and restriction maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The actual direct image of the structure sheaf, with its natural algebra structure.
Source: Stacks, Tag 0B3I (blueprint: lem-trf-positive-copy-proj-affine-comparison). -/
noncomputable def positiveCopyDirectImageAlgebra {T S : Scheme.{u}} (h : T ⟶ S) :
    S.CommAlgebraSheaf :=
  Under.mk (⟨h.c⟩ : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj T.sheaf)

namespace PositiveCopyProj

variable {S : Scheme.{u}} (E : S.CommAlgebraSheaf) (B : S.GradedAlgebraData)
    (e : ∀ (U : S.affineOpens) (n : ℕ),
      (positiveCopyPiece E n).val.obj (op U.1) ≃ₗ[Γ(S, U.1)] B.grading U n)

/-- The degree-one unit of the coefficient algebra, as a homogeneous element.
Source: Stacks, Tags 0B3I and 01M4
(blueprint: lem-trf-positive-copy-proj-affine-comparison). -/
noncomputable def chartUnit (U : S.affineOpens) : B.grading U 1 :=
  e U 1 (1 : E.right.obj.obj (op U.1))

/-- The fraction a[n+1]/t^(n+1), allowing t=0 and the zero coefficient algebra.
Source: Stacks, Tag 01M4
(blueprint: lem-trf-positive-copy-proj-affine-comparison). -/
noncomputable def fraction (U : S.affineOpens) (n : ℕ)
    (a : E.right.obj.obj (op U.1)) :
    HomogeneousLocalization.Away (B.grading U) (chartUnit E B e U).val :=
  HomogeneousLocalization.Away.mk (B.grading U) (chartUnit E B e U).property (n + 1)
    (e U (n + 1) a).val (by simp only [smul_eq_mul, mul_one]; exact (e U (n + 1) a).property)

end PositiveCopyProj

/-- Positive-copy relative Proj canonically recovers an affine morphism, with its full
single-chart description, coefficient formulas, affine restriction compatibility and
uniqueness. A ring equivalence together with the displayed scalar equation expresses the
R-algebra equivalence without introducing a second scalar structure on the localization.

Source: Stacks, Morphisms, Tag 0B3I (lemma-finite-projective), explicit positive-copy
verification; Constructions, Tags 01M4, 01MB, 01NO and 01NQ
(blueprint: lem-trf-positive-copy-proj-affine-comparison).

Proof: (1) Apply lem-trf-positive-copy-graded-quotient and
lemma-nagata-relative-proj-exists to obtain the compatible affine Proj charts. Affineness
of h identifies the coefficient algebra on V with the actual sections on h inverse V.
(2) For t=1[1], the identity a[n]^2=t a^2[2n-1] shows that a homogeneous prime containing
t contains the irrelevant ideal. Thus Proj C=D_+(t), including the zero algebra.
(3) Every degree-zero fraction has a positive-exponent representative, since r/1 equals
its structure-map image [1]/t. The localization relation makes two such fractions equal
exactly when their coefficients agree: their cross difference is (a-b)[m+n+k]. This
uses no injectivity of the base structure map (def-weil-ring-localization-away).
(4) Addition, multiplication, unit and scalars show that coefficient extraction is an
R-algebra equivalence with inverse a[1]/t. When A=0 the localization is the zero ring.
(5) Use prop-nagata-proj-standard-open, then Spec of the inverse coefficient equivalence,
then the canonical affine identification of h inverse V. The scalar formula proves that
this is over V (def-nagata-affine-proj and def-weil-affine-spectrum).
(6) Affine restriction sends a[m]/t^m to res(a)[m]/res(t)^m. Coefficient extraction and
its inverse commute with this map; functoriality of Spec gives both local naturality
squares. (7) Refine arbitrary overlaps by affine opens (lem-weil-pbc-affine-opens-basis).
The existence and equality clauses of lem-weil-pbc-scheme-morphism-gluing glue the maps
and their inverses. Their composites and their structural maps agree locally, hence
globally. The same equality clause proves uniqueness with the specified local formulas.
No finiteness, finite generation, separation or Noetherian assumption is used. -/
theorem existsUnique_positiveCopyProjAffineComparison
    {T S : Scheme.{u}} (h : T ⟶ S) [IsAffineHom h]
    [(positiveCopyDirectImageAlgebra h).toModule.IsQuasicoherent]
    (B : S.GradedAlgebraData)
    (e : ∀ (U : S.affineOpens) (n : ℕ),
      (positiveCopyPiece (positiveCopyDirectImageAlgebra h) n).val.obj (op U.1)
        ≃ₗ[Γ(S, U.1)] B.grading U n)
    (hzero : ∀ (U : S.affineOpens) (r : Γ(S, U.1)),
      (e U 0 r).val = algebraMap Γ(S, U.1) (B.obj U) r)
    (hmul : ∀ (U : S.affineOpens) (m n : ℕ)
      (a b : Γ(T, h ⁻¹ᵁ U.1)),
      (e U (m + n + 2) (a * b)).val =
        (e U (m + 1) a).val * (e U (n + 1) b).val)
    (hres : ∀ (U V : S.affineOpens) (i : U ≤ V) (n : ℕ)
      (a : (positiveCopyPiece (positiveCopyDirectImageAlgebra h) n).val.obj (op V.1)),
      B.res i (e V n a).val =
        (e U n ((positiveCopyPiece (positiveCopyDirectImageAlgebra h) n).val.map
          (homOfLE (X := S.Opens) i).op a)).val) :
    ∃ (α : ∀ U : S.affineOpens,
      HomogeneousLocalization.Away (B.grading U)
        (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e U).val
        ≃+* Γ(T, h ⁻¹ᵁ U.1))
      (θV : ∀ U : S.affineOpens, Proj (B.grading U) ≅ (h ⁻¹ᵁ U.1).toScheme)
      (ℓ : ∀ (U V : S.affineOpens) (_ : U ≤ V),
        HomogeneousLocalization.Away (B.grading V)
          (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e V).val →+*
        HomogeneousLocalization.Away (B.grading U)
          (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e U).val),
      (∀ U : S.affineOpens,
        Proj.basicOpen (B.grading U)
          (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e U).val = ⊤) ∧
      (∀ (U : S.affineOpens) (n : ℕ) (a : Γ(T, h ⁻¹ᵁ U.1)),
        α U (PositiveCopyProj.fraction (positiveCopyDirectImageAlgebra h) B e U n a) = a) ∧
      (∀ (U : S.affineOpens) (a : Γ(T, h ⁻¹ᵁ U.1)),
        (α U).symm a =
          PositiveCopyProj.fraction (positiveCopyDirectImageAlgebra h) B e U 0 a) ∧
      (∀ (U : S.affineOpens) (r : Γ(S, U.1)),
        α U (HomogeneousLocalization.fromZeroRingHom (B.grading U) _ (e U 0 r)) =
          h.app U.1 r) ∧
      (∀ U : S.affineOpens,
        (Proj.basicOpen (B.grading U)
          (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e U).val).ι ≫
            (θV U).hom =
          (Proj.basicOpenIsoSpec (B.grading U) _
            (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e U).property
            (by decide : 0 < (1 : ℕ))).hom ≫
          Spec.map (CommRingCat.ofHom (α U).symm.toRingHom) ≫
          (U.2.preimage h).isoSpec.inv) ∧
      (∀ (U V : S.affineOpens) (i : U ≤ V) (n : ℕ) (a : Γ(T, h ⁻¹ᵁ V.1)),
        ℓ U V i (PositiveCopyProj.fraction (positiveCopyDirectImageAlgebra h) B e V n a) =
          PositiveCopyProj.fraction (positiveCopyDirectImageAlgebra h) B e U n
            (T.presheaf.map (homOfLE (h.preimage_mono i)).op a)) ∧
      (∀ (U V : S.affineOpens) (i : U ≤ V)
        (x : HomogeneousLocalization.Away (B.grading V)
          (PositiveCopyProj.chartUnit (positiveCopyDirectImageAlgebra h) B e V).val),
        α U (ℓ U V i x) = T.presheaf.map (homOfLE (h.preimage_mono i)).op (α V x)) ∧
      (∀ (U V : S.affineOpens) (i : U ≤ V) (a : Γ(T, h ⁻¹ᵁ V.1)),
        ℓ U V i ((α V).symm a) =
          (α U).symm (T.presheaf.map (homOfLE (h.preimage_mono i)).op a)) ∧
      (∀ (U V : S.affineOpens) (i : U ≤ V),
        B.relProjFunctor.map (homOfLE i) ≫ (θV V).hom =
          (θV U).hom ≫ T.homOfLE (h.preimage_mono i)) ∧
      (∀ (U V : S.affineOpens) (i : U ≤ V),
        T.homOfLE (h.preimage_mono i) ≫ (θV V).inv =
          (θV U).inv ≫ B.relProjFunctor.map (homOfLE i)) ∧
      (∃! θ : B.relProj ≅ T,
        θ.hom ≫ h = B.relProjHom ∧
        ∀ U : S.affineOpens, B.relProjι U ≫ θ.hom = (θV U).hom ≫ (h ⁻¹ᵁ U.1).ι) := by
  sorry

end AlgebraicGeometry
