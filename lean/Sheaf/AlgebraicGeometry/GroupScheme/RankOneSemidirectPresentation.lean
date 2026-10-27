module

public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates
import Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections

/-! # The semidirect presentation of a rank-one reductive group

Source: Milne, Algebraic Groups (2017), Proposition 20.32, Theorem 20.33,
Corollary 20.34, pp.418--419, and 21.19, 21.23--21.24, pp.431--432.
(blueprint: lem-sfb-rank-one-semidirect-presentation)

The underlying scheme is the existing determinant-one scheme times the given torus.
Its group law is specified on all algebra points. The kernel is the actual categorical
kernel, with the specified isomorphism from the multiplicative group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.RankOnePresentation

/-- The matrix of a point of the existing special linear scheme, removing only the
universe lift on its two indices. Source: Milne, 20.32 and 21.24, pp.418,432
(blueprint: lem-sfb-rank-one-semidirect-presentation). -/
def matrix {F : Type u} [Field F] (A : CommAlgCat.{u} F)
    (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2) :
    Matrix (Fin 2) (Fin 2) A :=
  fun i j ↦ (LinearGroupSchemes.specialPoints F 2 A M).val ⟨i⟩ ⟨j⟩

/-- The matrix of conjugation by diag(α(t),1). The second Laurent value evaluates
α(t)⁻¹, so this formula also applies to nonreduced and zero algebras.
Source: Milne, 21.24, p.432
(blueprint: lem-sfb-rank-one-semidirect-presentation). -/
def conjugatedMatrix {F : Type u} [Field F]
    {T : Grp (Over (Spec (.of F)))} (α : RankOneRoots.Character T)
    (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ T.X)
    (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2) :
    Matrix (Fin 2) (Fin 2) A :=
  !![matrix A M 0 0,
      RankOneRoots.multiplicativeValue A (t ≫ α.hom.hom) * matrix A M 0 1;
      RankOneRoots.multiplicativeValue A ((t ≫ α.hom.hom)⁻¹) * matrix A M 1 0,
      matrix A M 1 1]

/-- The rank-one semidirect presentation, including its full scheme-theoretic kernel.
Root parametrizations are closed embeddings from Ga with the corresponding stable
Lie image. Thus they identify Ga with the root subgroups of the recorded theorem.
The two matrix restriction hypotheses say exactly that v induces these parametrizations.
The diagonal hypothesis identifies its restriction with the given coroot.

Source: Milne, Proposition 20.32, Theorem 20.33 and Corollary 20.34, pp.418--419;
Theorem 21.11 and 21.19, 21.23--21.24, pp.429--432.
(blueprint: lem-sfb-rank-one-semidirect-presentation).

Proof plan (the seven steps of the DAG node):
1. The root-parametrization conjugation formulas agree with conjugation by
   diag(α(t),1) on x+ and x-, and both fix the diagonal. For a matrix
   [[a,b],[c,e]], the opens D(a), D(c) cover since ae-bc=1. On these opens use
   M=x-(c/a)d(a)x+(b/a) and M=x+(a/c)w d(c)x+(e/c), respectively, where
   w=x+(-1)x-(1)x+(-1). Equality on this cover gives equivariance as morphisms.
2. Conjugation is an algebraic action. The displayed semidirect multiplication
   is associative, with identity (I,1) and inverse (C(t⁻¹)(M⁻¹),t⁻¹).
   SL2 has coordinates F[a,b,c,e]/(ae-bc-1); the torus has Laurent coordinates.
   Their product is affine of finite type. Equivariance makes π a homomorphism.
3. Put n=v(w). The identity C(t)(w)=d(α(t))w gives
   ntn⁻¹=t α∨(α(t)⁻¹). Its square is the identity since α∘α∨ is squaring.
   The regular-cocharacter Borel description gives B=P(α∨), with positive root α.
   Borel root-product coordinates give B=Uα⋊T. The Bruhat longest-cell chart
   identifies n with the longest Weyl element and gives B∩nBn⁻¹=T.
4. Translate that chart by n⁻¹ and use w⁻¹x+(z)w=x-(-z). Reordering B's
   factors gives the open immersion (z,t,y)↦u-(z)t u+(y), containing T.
5. Apply affine homomorphism flat image to π. Its closed image contains T,Uα,U-α.
   The rank-one tangent decomposition and root parametrizations show these smooth
   connected subgroups span Lie(H). Smooth-subgroup tangent generation makes the
   image H. Thus π's coordinate map is faithfully flat.
6. The opposite-Borel intersection implies n∉B over every algebraically closed
   extension. If a=0, the D(c) formula puts v(M) in nB, outside T. For any
   algebra A a nonunit a in a kernel point gives this contradiction after passing
   to an algebraic closure of a residue field. Thus the entire kernel lies in D(a).
7. In the open immersion of step 4, v(M)=t⁻¹ has the unique coordinates
   (0,t⁻¹,0). The D(a) formula gives b=c=0, e=a⁻¹ and α∨(a)=t⁻¹.
   Conversely these pairs lie in the kernel. They multiply by multiplying a;
   the invertible coordinate a is the regular inverse of k. This proves the
   isomorphism on arbitrary algebras, including infinitesimal kernel points. -/
theorem rank_one_semidirect_presentation
    {F : Type u} [Field F] [IsAlgClosed F]
    (H T : Grp (Over (Spec (.of F))))
    (hH : ReductiveTorusCentralizer.IsReductive H)
    (i : T ⟶ H) (hT : ReductiveTorusCentralizer.IsMaximalTorus i)
    (hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus F r))
    (aH : ModObj T.X H.X) (haH : aH.smul = RankOneRoots.adjointMap i)
    (α δ : RankOneRoots.Character T) (hδ : δ.hom.hom = α.hom.hom⁻¹)
    (hroots : ∀ χ : RankOneRoots.Character T,
      χ ∈ RankOneRoots.roots T H aH ↔ χ = α ∨ χ = δ)
    (uPlus uMinus : Grp.mk (StandardGroupSchemes.additive F) ⟶ H)
    (hPlus : IsClosedSubgroupScheme uPlus.hom.hom ∧
      @TorusCharacterTangent.IsStable F _ T H aH _ uPlus ∧
      (GrpObj.differential uPlus.hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T H aH α)
    (hMinus : IsClosedSubgroupScheme uMinus.hom.hom ∧
      @TorusCharacterTangent.IsStable F _ T H aH _ uMinus ∧
      (GrpObj.differential uMinus.hom.hom).toLinearMap.range =
        @TorusCharacterTangent.weightSpace F _ T H aH δ)
    (ν : RankOneRoots.Cocharacter T)
    (v : Grp.mk (LinearGroupSchemes.specialLinear F 2) ⟶ H)
    (hvPlus : ∀ (A : CommAlgCat.{u} F) (z : A)
      (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2),
      matrix A M = !![1, z; 0, 1] →
        M ≫ v.hom.hom = TorusCharacterTangent.additiveParameterPoint F z ≫ uPlus.hom.hom)
    (hvMinus : ∀ (A : CommAlgCat.{u} F) (z : A)
      (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2),
      matrix A M = !![1, 0; z, 1] →
        M ≫ v.hom.hom = TorusCharacterTangent.additiveParameterPoint F z ≫ uMinus.hom.hom)
    (hvDiag : ∀ (A : CommAlgCat.{u} F)
      (s : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F)
      (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2),
      matrix A M = !![RankOneRoots.multiplicativeValue A s, 0;
        0, RankOneRoots.multiplicativeValue A s⁻¹] →
        M ≫ v.hom.hom = s ≫ ν.hom.hom ≫ i.hom.hom) :
    ∃ (C : T.X ⊗ LinearGroupSchemes.specialLinear F 2 ⟶
        LinearGroupSchemes.specialLinear F 2)
      (E : Grp (Over (Spec (.of F))))
      (eE : LinearGroupSchemes.specialLinear F 2 ⊗ T.X ≅ E.X) (π : E ⟶ H),
      IsAffine E.X.left ∧
      LocallyOfFiniteType E.X.hom ∧
      QuasiCompact E.X.hom ∧
      (∀ (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ T.X)
        (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2),
        matrix A (lift t M ≫ C) = conjugatedMatrix α A t M) ∧
      (∀ (A : CommAlgCat.{u} F)
        (M N : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2)
        (t z : StandardGroupSchemes.affine F A ⟶ T.X),
        (lift M t ≫ eE.hom) * (lift N z ≫ eE.hom) =
          lift (M * (lift t N ≫ C)) (t * z) ≫ eE.hom) ∧
      eE.hom ≫ π.hom.hom = (fst _ _ ≫ v.hom.hom) * (snd _ _ ≫ i.hom.hom) ∧
      @Module.FaithfullyFlat Γ(H.X.left, ⊤)
        Γ(E.X.left, ⊤) _ _
        π.hom.hom.left.appTop.hom.toAlgebra.toModule ∧
      (∃ e : Grp.mk (StandardGroupSchemes.multiplicative F) ≅ Grp.mk (GrpObj.ker π.hom.hom),
        ∀ (A : CommAlgCat.{u} F)
          (s : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F),
          matrix A (s ≫ e.hom.hom.hom ≫ GrpObj.kerι π.hom.hom ≫ eE.inv ≫ fst _ _) =
            !![RankOneRoots.multiplicativeValue A s, 0;
              0, RankOneRoots.multiplicativeValue A s⁻¹] ∧
          s ≫ e.hom.hom.hom ≫ GrpObj.kerι π.hom.hom ≫ eE.inv ≫ snd _ _ = (s ≫ ν.hom.hom)⁻¹) ∧
      ∀ (A : CommAlgCat.{u} F) (t : StandardGroupSchemes.affine F A ⟶ T.X)
        (M : StandardGroupSchemes.affine F A ⟶ LinearGroupSchemes.specialLinear F 2),
        lift t M ≫ C ≫ v.hom.hom =
          (t ≫ i.hom.hom) * (M ≫ v.hom.hom) * (t ≫ i.hom.hom)⁻¹ := by
  sorry

end AlgebraicGeometry.RankOnePresentation
