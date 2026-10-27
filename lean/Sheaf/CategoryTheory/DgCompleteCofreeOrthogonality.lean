module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Sheaf.CategoryTheory.DgCompleteDualFreeFiltration
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Complete dual-free DG modules are right orthogonal to acyclic modules

Source: Stacks Project, dga.tex, Tag 09KS, lemma-property-I-K-injective
(blueprint: lem-sfb-dg-complete-cofree-orthogonality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- Every chain map from an acyclic right DG module to a complete dual-free
filtered module has an action-preserving homotopy to zero.

Source: Stacks Project, dga.tex, Tag 09KS, lemma-property-I-K-injective
(blueprint: lem-sfb-dg-complete-cofree-orthogonality).

Proof plan:
1. The character dual of an acyclic complex is acyclic. Q/Z is divisible
(the m-th root of q modulo Z is q/m modulo Z). For a dual cocycle lambda in
 degree r, define beta(d x)=(-1)^r lambda(x). Acyclicity makes beta well
 defined. Extend beta from im d to the next term using
 lem-per-divisible-group-hom-extension, namely
 Module.Baer.extension_property_addMonoidHom and Module.Baer.of_divisible.
 Its extension mu satisfies d(mu)=lambda.
2. Apply lem-sfb-dg-shifted-character-dual-hom (Stacks 09K4) to conclude that
 every map from C to A-dual[k] is null-homotopic. For a product choose such
 homotopies coordinatewise, including the empty product. Transport by each
 layer coordinate equivalence to obtain the same assertion for every layer.
3. Write Q_p=I/F_p and let g_p be the projection of g. Construct compatible
 degree-minus-one right-linear homotopies h_p of g_p. Start at Q_0=0.
 Lift h_p by the graded section of Q_(p+1) -> Q_p, obtaining h-tilde.
 The error e=g_(p+1)-d h-tilde-h-tilde d has zero projection and commutes
 with d. It is right-linear because its two d_A terms cancel. Exactness
 therefore factors e through the actual layer F_p/F_(p+1).
4. Step 2 gives a right-linear homotopy k_p for this layer-valued error.
 Set h_(p+1)=h-tilde+j_p k_p. Its boundary is g_(p+1), and its projection
 remains h_p because q_p j_p=0. Thus all h_p are compatible.
5. For each homogeneous c, completeness supplies the unique element h(c)
 projecting to every h_p(c). Uniqueness gives additivity and right linearity.
 Projecting d h+h d=g to each Q_p gives the already proved equations;
 uniqueness in completeness reflects equality. This is the required actual
 homotopy; no boundedness or infinite-sum convergence is assumed. -/
theorem exists_rightLinearHomotopy_of_completeDualFreeFiltration
    (A : Algebra.{u}) (I : RightModule A) (_F : CompleteDualFreeFiltration A I)
    (C : RightModule A) (hC : ((underlying A).obj C).Acyclic) (g : C ⟶ I) :
    ∃ h : Homotopy ((underlying A).map g) 0,
      ∀ (p q : ℤ) (c : ((underlying A).obj C).X p) (a : A.X.X q),
        HEq (h.hom (p + q) (p + q - 1) (act A C p q c a))
          (act A I (p - 1) q (h.hom p (p - 1) c) a) := by
  sorry

end CategoryTheory.DgAlgebra
