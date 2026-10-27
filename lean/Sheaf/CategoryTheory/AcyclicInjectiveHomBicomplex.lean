module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex

/-!
# Acyclic-source, injective-target Hom bicomplex

Source: Stacks Project, Cohomology on Sites, Tags 07AA and 07AC; Homological Algebra,
Tags 0130 and 0132 (blueprint: lem-trf-acyclic-injective-hom-bicomplex).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The reindexed commuting Hom bicomplex has exact rows and acyclic finite-diagonal total.
Source: Stacks Project, Tags 07AA and 07AC, with Homological Algebra, Tags 0130 and 0132
(blueprint: lem-trf-acyclic-injective-hom-bicomplex).

Proof:
1. Precomposition by the differential of K and postcomposition by that of J are additive.
   Their squares vanish and they commute by associativity. Extend by zero outside the
   quadrant. The two cross terms in the signed total differential cancel, and each
   diagonal has only finitely many nonzero terms.
2. For q nonnegative and r = b-p with p positive, a map h annihilating d_K^{r-1}
   descends through K^r / ker d_K^r = im d_K^r by acyclicity. Injectivity of J^q extends
   this descended map from im d_K^r to K^{r+1}, giving h = g composed with d_K^r.
   This uses the cokernel in module sheaves, rather than surjectivity on sections.
3. At p = 0, K^{b+1} is zero and acyclicity makes d_K^{b-1} an epimorphism.
   Hence h composed with d_K^{b-1} = 0 implies h = 0. Negative rows are zero.
4. The second spectral sequence has zero first page by row exactness. All subsequent
   pages and stable entries vanish. The associated graded pieces of the image
   filtration on total cohomology are consequently zero. Its finite bounds F^0 = H
   and F^{n+1} = 0 imply H = 0 by descending induction. Negative total degrees vanish.
   No augmentation or cohomological property of J is used.

The additive equivalences identify every nonnegative term with its prescribed Hom
abelian group, and the next two clauses specify both differentials on every element.
The zero-object clause specifies the remaining terms and therefore the boundary maps.
Mathlib's `total (ComplexShape.up ℤ)` is the stated diagonal coproduct with differential
`d_I + (-1)^p d_II`. -/
theorem exists_acyclic_injective_hom_bicomplex
    {C : Type u} [Category.{v} C] (P : Precoverage C)
    (_hP : P.IsSiteForCoverings) (R : Sheaf P.toGrothendieck CommRingCat.{max u v w})
    (K J : CochainComplex
      (ringedSiteModules.{max u v w}
        ((sheafCompose P.toGrothendieck
          (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R)) ℤ)
    (b : ℤ) (_hK : K.Acyclic) (_hKb : ∀ r : ℤ, b < r → IsZero (K.X r))
    (_hJ : ∀ q : ℤ, q < 0 → IsZero (J.X q))
    (_hI : ∀ q : ℤ, Injective (J.X q)) :
    ∃ D : HomologicalComplex₂ AddCommGrpCat.{max u v w}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      ∃ e : ∀ p q : ℕ, ((D.X (p : ℤ)).X (q : ℤ)) ≃+
          (K.X (b - (p : ℤ)) ⟶ J.X (q : ℤ)),
        (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((D.X p).X q)) ∧
        (∀ (p q : ℕ) (x : (D.X (p : ℤ)).X (q : ℤ)),
          e (p + 1) q (((D.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).f (q : ℤ)) x) =
            K.d (b - ((p + 1 : ℕ) : ℤ)) (b - (p : ℤ)) ≫ e p q x) ∧
        (∀ (p q : ℕ) (x : (D.X (p : ℤ)).X (q : ℤ)),
          e p (q + 1) (((D.X (p : ℤ)).d (q : ℤ) ((q + 1 : ℕ) : ℤ)) x) =
            e p q x ≫ J.d (q : ℤ) ((q + 1 : ℕ) : ℤ)) ∧
        (∀ q : ℤ, (D.flip.X q).Acyclic) ∧
        (∀ (p q : ℕ), 0 < p →
          ∀ h : K.X (b - (p : ℤ)) ⟶ J.X (q : ℤ),
            K.d (b - (p : ℤ) - 1) (b - (p : ℤ)) ≫ h = 0 →
              ∃ g : K.X (b - (p : ℤ) + 1) ⟶ J.X (q : ℤ),
                K.d (b - (p : ℤ)) (b - (p : ℤ) + 1) ≫ g = h) ∧
        (∀ (q : ℕ) (h : K.X b ⟶ J.X (q : ℤ)), K.d (b - 1) b ≫ h = 0 → h = 0) ∧
        (D.total (ComplexShape.up ℤ)).Acyclic := by
  sorry

end CategoryTheory
