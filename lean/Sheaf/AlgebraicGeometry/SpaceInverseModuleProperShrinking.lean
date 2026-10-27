module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Proper-support shrinking for an inverse-ring local model

Source: Stacks Project, spaces-flat.tex, Tag 0CXA, lemma-proper-support, proof;
more-algebra.tex, Tag 0CT7; spaces-more-morphisms.tex, Tag 0CWI
(blueprint: lem-sfb-space-inverse-module-proper-shrinking).

The index n represents the paper's level n + 1. An open subspace is presented by its
representable open immersion. The special fibre of W is canonically X_1 because W
contains the image of X_1. Proper support is expanded as the closed-carrier criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finitely presented module with proper special-fibre support has proper support
on some smaller open neighbourhood of that fibre.
Source: Stacks Project, spaces-flat.tex, Tag 0CXA, lemma-proper-support, proof;
more-algebra.tex, Tag 0CT7; spaces-more-morphisms.tex, Tag 0CWI
(blueprint: lem-sfb-space-inverse-module-proper-shrinking).

Proof:
1. Put I = ker(A to A_1). By lem-sfb-nil-ring-tower-limit-henselian, A/I is A_1
   and (A,I) is henselian. Nil kernels identify all underlying special-fibre subsets.
2. X_1 is quasi-compact by lem-sfb-space-quasicompact-affine-tests. Using
   lem-a1-space-etale-open-image, cover W by quasi-compact open images of affine
   etale charts and take a finite subcover of X_1. Their union W_0 contains X_1,
   is contained in W, and is separated and finite type over A. The empty union is allowed.
3. Restrict F to W_0. Its annihilator defines a closed carrier Z, by
   lem-sfb-space-module-proper-carrier-support. Finite generation shows that its point
   set is the module support; lem-sfb-space-etale-chart-support gives the geometric
   stalk interpretation. The closed immersion is proper by lem-sfb-space-closed-subspace-proper;
   lem-sfb-space-finite-type-composition makes Z finite type over A, and it is separated.
4. The special fibre of Z has point set equal to the support of F tensor_A A_1,
   by lem-a1-space-point-open-calculus and lem-sfb-space-finite-type-support-pullback.
   The hypothesis and lem-sfb-space-module-proper-carrier-support give a proper
   carrier of that support. The equal-point-set assertion of
   lem-sfb-space-proper-support-closed-operations makes the special fibre of Z proper.
   This step does not assert that annihilators commute with non-flat base change.
5. Apply lem-sfb-space-henselian-proper-clopen-lift to Z and its whole special fibre.
   Obtain Z = Z_1 disjoint-union Z_2 with Z_1 proper over A and all the special fibre
   in Z_1. Thus the closed subset Z_2 misses X_1.
6. Take W' = W_0 minus Z_2. It contains X_1. Restriction of the annihilator carrier
   is Z_1, using lem-sfb-space-finite-type-support-pullback and restriction of local
   annihilating sections. By lem-sfb-space-module-proper-carrier-support this gives
   proper support in exactly the stated closed-carrier sense. -/
theorem inverseModuleProperShrinking
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec c.pt))))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (W : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (j : W ⟶ X)
    (hopen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom)
    (hcontains : pointImage (properQuotFst f (CostructuredArrow.mk (yoneda.map
        (Over.homMk (Spec.map (c.π.app (op 0))) (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from (Spec (A 0))) ⟶
            Over.mk (specULiftZIsTerminal.from (Spec c.pt)))))).hom.hom ⊆
      pointImage j.hom.hom)
    (F : W.Modules) (hqc : F.IsQuasicoherent) (hfin : F.IsFinitePresentation)
    (hsupp : ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre (j ≫ f) (CostructuredArrow.mk (yoneda.map
        (Over.homMk (Spec.map (c.π.app (op 0))) (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from (Spec (A 0))) ⟶
            Over.mk (specULiftZIsTerminal.from (Spec c.pt)))))),
      IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd (j ≫ f) (CostructuredArrow.mk (yoneda.map
        (Over.homMk (Spec.map (c.π.app (op 0))) (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from (Spec (A 0))) ⟶
            Over.mk (specULiftZIsTerminal.from (Spec c.pt)))))) ∧
      ∃ G : Z.Modules, G.IsQuasicoherent ∧ G.IsFiniteType ∧
        Nonempty ((moduleDirectImage i).obj G ≅
          (moduleTensorPullback (properQuotFst (j ≫ f) (CostructuredArrow.mk (yoneda.map
        (Over.homMk (Spec.map (c.π.app (op 0))) (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from (Spec (A 0))) ⟶
            Over.mk (specULiftZIsTerminal.from (Spec c.pt))))))).obj F)) :
    ∃ (W' : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (k : W' ⟶ W),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) k.hom.hom ∧
      pointImage (properQuotFst f (CostructuredArrow.mk (yoneda.map
        (Over.homMk (Spec.map (c.π.app (op 0))) (specULiftZIsTerminal.hom_ext _ _) :
          Over.mk (specULiftZIsTerminal.from (Spec (A 0))) ⟶
            Over.mk (specULiftZIsTerminal.from (Spec c.pt)))))).hom.hom ⊆
        pointImage (k ≫ j).hom.hom ∧
      ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) (i : Z ⟶ W'),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
        MapIsProper (i ≫ k ≫ j ≫ f) ∧ ∃ G : Z.Modules,
          G.IsQuasicoherent ∧ G.IsFiniteType ∧
            Nonempty ((moduleDirectImage i).obj G ≅ (moduleTensorPullback k).obj F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
