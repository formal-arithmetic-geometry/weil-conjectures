/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Topology.Compactness.Compact
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Yoneda
import Sheaf.AlgebraicGeometry.FppfAffineRefinement
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The homomorphism theorem for finite-type group schemes

Source: Milne, Algebraic Groups (2017), Theorem 5.39, p.108;
Theorem 5.28 and Corollary 5.27, p.105; Example 5.71, p.117
(blueprint: lem-sfb-algebraic-group-homomorphism-factorization).

The existing `IsFppfGroupQuotient` retains the kernel square and the quotient map:
its pointwise coequalizer is the coset presheaf, with the universal arrow to the
represented fppf sheaf. Affine tests give the stated quotient of algebra-valued points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A homomorphism of separated finite-type group schemes factors through its
fppf quotient by its scheme-theoretic kernel and then a closed immersion.

Source: Milne, Algebraic Groups (2017), Theorem 5.39, p.108;
Theorem 5.28 and Corollary 5.27, p.105; Example 5.71, p.117
(blueprint: lem-sfb-algebraic-group-homomorphism-factorization).

Proof plan, following the six steps of the DAG node:
1. By lem-sc-kernel-subgroup, the pullback kernel is a closed subgroup with
   points equal to the kernel on points. Conjugating a kernel point preserves
   its image 1, so it is normal. Closed subsets of a quasi-compact space are
   quasi-compact (lem-weil-pbc-closed-in-quasi-compact); on an affine chart its
   coordinate ring is a quotient of a finite-type algebra, hence finite type.
2. Apply lem-sfb-algebraic-group-homogeneous-quotient to this closed subgroup.
   It gives a separated finite-type quotient and a flat, surjective, finitely
   presented projection. Two points have the same image exactly when their
   ratio is a kernel point, and quotient points lift fpqc-locally.
3. Lift two quotient points locally to a,b and define their product by q(ab).
   Normality makes this independent of the lifts: replacing a,b by an,bm
   changes ab by the right kernel factor (b⁻¹nb)m. Inversion is independent
   by the same calculation. Base change the covers using
   lem-galois-fpqc-covering-base-change and glue by
   lem-weil-pbc-fpqc-representable-descent. Yoneda
   (lem-galois-yoneda-fully-faithful) gives the group-scheme operations.
   All group laws hold on lifts and descend uniquely; q is a homomorphism.
4. Define i(x) by f(a) on a local lift of x. Kernel points do not change f(a),
   so representable descent glues these values, naturally in the test scheme.
   Yoneda gives i and iq=f; local multiplication shows i is a homomorphism.
   If i(x)=i(y), lift both on a common base-changed cover. Their ratio lies
   in the kernel, so the coset criterion gives x=y locally, hence globally.
5. Apply lem-sfb-algebraic-group-monomorphism-closed-immersion to i. The
   quotient is separated and finite type, and step 4 gives injectivity on
   all algebra-valued points. The coset criterion also says q(a)=1 exactly
   for kernel points. Yoneda and the pullback universal property identify
   its scheme-theoretic kernel with the original pullback kernel.
6. On affine tests, cosets map injectively to the quotient points. Pull back
   q along any quotient point (lem-trf-fppf-covering-base-change), then use
   lem-pc-fppf-affine-refinement to lift it on an affine fppf cover. Thus the
   coset map is locally surjective. Representable fpqc descent makes the
   target a sheaf. Any map from the coset presheaf to a sheaf extends by
   evaluating on these local lifts and gluing: equality of quotient images
   makes the cosets, hence their values, agree on overlaps. Refinements give
   independence and uniqueness. This is def-weil-pbc-sheafification, as
   packaged by IsFppfGroupQuotient; its torsor coordinates are (g,n) ↦ (g,gn).
   The finite presentation of q includes quasi-compactness and
   quasi-separatedness, not merely local finite presentation. -/
theorem algebraicGroup_homomorphism_factorization
    {k : Type u} [Field k] (G H : Grp (Over (Spec (.of k))))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsSeparated H.X.hom] [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    (f : G ⟶ H) :
    IsClosedSubgroupScheme (GrpObj.kerι f.hom.hom) ∧
    IsNormalSubgroupScheme (GrpObj.kerι f.hom.hom) ∧
    LocallyOfFiniteType (GrpObj.ker f.hom.hom).hom ∧
    QuasiCompact (GrpObj.ker f.hom.hom).hom ∧
    ∃ (I : Grp (Over (Spec (.of k)))) (q : G ⟶ I) (i : I ⟶ H),
      IsSeparated I.X.hom ∧ LocallyOfFiniteType I.X.hom ∧ QuasiCompact I.X.hom ∧
      q ≫ i = f ∧ IsClosedImmersion i.hom.hom.left ∧
      Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧
      QuasiCompact q.hom.hom.left ∧ QuasiSeparated q.hom.hom.left ∧
      IsFppfGroupQuotient (Grp.ofHom (GrpObj.kerι f.hom.hom)) q := by
  sorry

end AlgebraicGeometry
