module

public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.AlgebraicGeometry.SplitLocalSpecialKernelLifting
import Sheaf.AlgebraicGeometry.RelativeTorusMonomorphismClosed
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nakayama

/-! # Generic closedness rigidity for a given torus homomorphism

Source: Lan, Structures of Semi-Abelian Schemes, Propositions 3.3.1.5 and 3.3.1.7,
and section 3.1.1; Faltings--Chai I, Propositions 2.7 and 2.9.
(blueprint: lem-sfb-torus-hom-generic-closed-rigidity)

The map is given over the entire base. Its generic-fibre map is its actual pullback.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A given homomorphism from a torus is closed if its generic-fibre map is closed.

Source: Lan, Propositions 3.3.1.5 and 3.3.1.7 and section 3.1.1;
Faltings--Chai I, Propositions 2.7 and 2.9. The local-kernel argument is assembled
from Conrad, Reductive group schemes, Remark B.1.2, Corollary B.2.7 and Theorem 5.3.5.
(blueprint: lem-sfb-torus-hom-generic-closed-rigidity)

Proof:
1. At s in S take the Noetherian local domain R = O_{S,s}. Pull an fppf splitting
   cover of P back to Spec R using lem-trf-fppf-covering-base-change. Localize a
   finite-presentation affine chart at a point over the closed point. This gives
   a nonzero flat Noetherian local R-algebra B splitting P; Noetherianity uses
   lem-weil-pbc-finite-type-over-noetherian and lem-weil-pbc-localization-noetherian.
   Lem-sfb-split-local-special-kernel-lifting produces a closed subgroup D_B(M)
   killed by f_B, with special fibre equal to the special-fibre kernel.
2. Write F = kappa(eta) and C = B tensor_R F. Flatness makes B torsion-free over R,
   so B injects into C and C is nonzero (def-weil-pbc-flat-ring-map). The map f_C
   is closed by lem-weil-pbc-closed-immersion-base-change, so D_C(M) is trivial.
   If m is nonzero in M, the group-algebra basis makes e_m-e_0 a nonzero element
   of the augmentation ideal, a contradiction. Thus M=0. Descent of the zero
   augmentation ideal through the residue-field extension uses
   lem-sfb-field-extension-tensor-injective. Every fibre kernel is trivial.
3. The total kernel K is closed in the affine S-scheme P: the unit of G is closed
   by lem-weil-pbc-section-separated-closed-immersion and closedness survives base
   change. Over a Noetherian affine Spec A, write K=Spec E, with E Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. Its augmentation splits E=A direct-sum J.
   Step 2 says J tensor_A kappa(p)=0. At q over p this gives J_q=p E_q J_q.
   The ideal J_q is finitely generated; lem-weil-pbc-nakayama-jacobson gives J_q=0.
   Localization at all primes detects zero, so J=0 and K is the identity group.
4. For every S-scheme T, equality f(x)=f(y) puts x y^{-1} in the trivial K(T).
   Thus f is monic on all test schemes, including nonreduced ones. Apply
   lem-sfb-relative-torus-monomorphism-closed to obtain the claimed closed immersion. -/
theorem torusHom_generic_closed_rigidity
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hnormal : ∀ s : S,
      IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s))
    (P G : Grp (Over S)) [IsCommMonObj P.X] [IsCommMonObj G.X]
    [Smooth P.X.hom] [IsAffineHom P.X.hom]
    [LocallyOfFinitePresentation P.X.hom] [QuasiCompact P.X.hom]
    [QuasiSeparated P.X.hom] (hP : IsRelativeTorus P.X)
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (hG : HasSemiabelianGeometricFibres G)
    (f : P ⟶ G)
    (hgeneric : IsClosedImmersion
      (((Over.pullback (S.fromSpecResidueField (genericPoint S))).map f.hom.hom).left)) :
    IsClosedImmersion f.hom.hom.left := by
  sorry

end AlgebraicGeometry
