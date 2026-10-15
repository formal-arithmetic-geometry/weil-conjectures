/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import Sheaf.Paper.CondensedPointBasisEvaluation
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.ProfinitePointPullback

/-!
# Local matrix refinement for one finite presentation

This is the matrix and rank argument from the parent local-triviality theorem,
with one fixed presentation member isolated as a separately provable obligation.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A finite presentation on one pro-etale object admits a finite-free refinement.

Source: RefactorInstruction.tex, Section 4, finite-matrix refinement;
Bhatt--Scholze, Definition 6.8.3 (blueprint: lem-weil-pbc-condensed-qbar-lfp-matrix-refinement).
Proof:
1. Write A_T for the bounded-image coefficient ring on T. The coefficient comparison
   (lem-weil-pbc-profinite-point-pullback) identifies f^* A_X with A_Y. Unpack hP as
   a cokernel of a map A_Y^m -> A_Y^n. Since hf makes Y an object of X_proet, use
   lem-weil-pbc-proetale-affine-wcontractible-covering-family to cover it by affine
   objects U weakly contractible on X_proet. Restriction preserves the presentation:
   inverse image preserves finite colimits by lem-weil-pbc-site-pullback-abelian-exact,
   and forgetfulness preserves cokernels by lem-weil-pbc-module-sheaves-colimits-forgetful.
   The monoidal comparisons identify the restricted free modules and their coefficients.
   A map between finite free module sheaves is a finite matrix of sections, by applying
   it to the global unit basis sections.
2. On each U, lem-weil-pbc-condensed-point-basis-evaluation identifies these entries
   with bounded-image continuous functions on the profinite quotient pi_0(U). Each
   entry takes values in a finite extension of Q_l. Taking their finite compositum,
   using def-weil-finite-subextension-directed-set, gives one finite field E for all
   entries on U. For an empty matrix choose E = Q_l. Thus the matrix comes from E
   coefficient sections. Apply only the coefficient-realization clause of
   lem-weil-pbc-condensed-lfp-local-triviality with the original noetherian base X,
   evaluated at the site object U. It identifies the E sections with continuous
   functions |U| -> E. Naturality of basis evaluation in the inclusion E -> Qbar_l
   identifies their images with the original entries. This comparison is natural
   under restriction, so the E sections on any open W of U are C(|W|, E), still
   using base X. Neither U nor W is assumed noetherian.
3. Let S = f(|Y|), with its subspace topology. For x in S, pull P to a geometric
   representative Spec K -> X above x and evaluate at Spec K. By
   lem-weil-pbc-geometric-field-proetale-evaluation and the coefficient comparisons,
   the coefficient ring is Qbar_l and this evaluation preserves cokernels and finite
   free modules. Choose y above x and an algebraic closure of its residue field.
   Pulling hP to that geometric point gives a finite-dimensional Qbar_l-vector space.
   Its dimension r(x) is independent of the choice: an algebraic closure of kappa(x)
   embeds over kappa(x) into every algebraically closed representative, and the
   extension comparison of the geometric-evaluation node preserves evaluation.
   For u in U above x, evaluation of the restricted presentation is therefore the
   cokernel of B_U(u), and r(x) = n - rank_E(B_U(u)). Evaluation of a coefficient
   function is its value at u by the naturality in steps 1 and 2. The rank is unchanged
   on extending E to Qbar_l, since a minor is nonzero in one field exactly when it is
   nonzero in the other. The original presentation need not exist outside S, and no
   rank function on all of X is asserted.
4. The maps U -> Y -> X are flat: hf supplies flatness of f and the refinement maps
   are weakly etale. Given a specialization x_g -> x_s in X and u_s in U above x_s,
   flat going-down (lem-sc-flat-going-down, def-weil-flat-morphism) gives a
   generalization u_g of u_s above x_g. Explicitly, apply going-down to the flat local
   map O_(X,x_s) -> O_(U,u_s), the prime corresponding to x_g and the maximal ideal
   upstairs. Each continuous E-valued matrix entry has the same value at u_g and u_s:
   continuous maps preserve specialization and E is Hausdorff. The lift puts x_g in S;
   the rank formula then gives r(x_g) = r(x_s). Since the U cover Y, the same lifting
   shows that S is stable under generalization.
5. The subspace S is noetherian: an ascending chain of its opens is obtained by
   intersecting S with an ascending chain of finite unions of opens of X, which
   stabilizes. Its irreducible components have generic points in S. Indeed, for any
   nonempty irreducible closed subset Z of S, its closure in X is irreducible and has
   a generic point eta by lem-sc-scheme-sober.
   Choose z in Z; eta generalizes z, so eta lies in S by step 4. Since Z is closed in S,
   closure_X(Z) intersect S = Z, giving eta in Z and closure_S({eta}) = Z.
   Apply lem-sc-noetherian-finite-irreducible-components to S. Step 4 makes r constant
   on each component, since its generic point generalizes every point of it.
   Intersecting components have equal ranks. Each rank level in S and its complement
   are therefore finite unions of closed components, hence are clopen in S. Their
   inverse images in U are clopen because U -> X factors continuously through S.
   These inverse images give an open cover of U; no assertion that S is open in X
   or that the rank levels extend to clopen subsets of X is needed.
6. On a nonempty piece V of U over the rank level r = a, the matrix has constant
   rank s = n - a, with s <= min(m,n). If s > 0, the nonvanishing loci of its s by s
   minors are open, since E minus {0} is open, and cover V by the rank criterion.
   Fix such a locus W and permute rows and columns so that B = [[D,C],[F,H]], with D
   the chosen invertible s by s block. Its inverse
   adj(D)/det(D) has continuous E-valued entries on W. By the coefficient realization
   of step 2 these are actual E coefficient sections, hence A_W sections; all inverses
   stay in the same finite field. Invertible block row and column operations give
   [[D^(-1),0],[-F D^(-1),1]] B [[1,-D^(-1) C],[0,1]]
     = [[1,0],[0,H - F D^(-1) C]].
   Pointwise rank s forces the Schur complement to vanish: any nonzero entry would
   give a nonzero (s+1) by (s+1) minor in this block diagonal matrix. Each entry is
   thus the zero continuous function, hence the zero E coefficient section. Mapping
   this equality to A_W and using the explicit invertible operations identifies the
   cokernel with A_W^(n-s) = A_W^a. This is an isomorphism of module sheaves, rather
   than an inference of isomorphism from the fibres.
7. If s = 0, every entry is the zero E-valued function, hence the matrix is zero as
   a matrix of coefficient sections. Its cokernel is A_V^n; use V itself as the minor
   locus, with no inverse. This also handles m = 0 or n = 0, with the appropriate
   empty blocks and free rank n. Omit empty rank pieces and minor loci. If Y is empty,
   take its empty covering. Otherwise the weakly contractible cover, the open rank
   pieces, and the open minor covers compose to a pro-etale cover of Y by
   def-weil-pbc-proetale-site. Exact restriction preserves the cokernel on every
   piece. The coefficient and inverse-image composition comparisons identify its
   pullback with (CondensedRing.upperStar Qbar_l (C.f i >> f)).obj P, giving precisely
   the displayed finite-free isomorphisms. All cokernels are ordinary; no derived
   completeness assumption is used. -/
theorem exists_condensedQbar_finiteFree_refinement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (f : Y ⟶ X) (hf : WeaklyEtale f)
    (P : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hP : Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} f).obj (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
      (((upperStar Ab.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).obj P)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
      ∃ r : ℕ, Nonempty
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (C.f i ≫ f)).obj P ≅
          Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (C.X i)) r) := by
  sorry

end AlgebraicGeometry.ProEtale
