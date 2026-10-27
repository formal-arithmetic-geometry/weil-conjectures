module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Schematicity under a finite locally free cover open in an affine scheme

Source: Stacks Project, Properties of Spaces, Tag 07S6,
proposition-finite-flat-equivalence-global and the paragraph following its proof
(blueprint: lem-sfb-finite-locally-free-open-affine-cover).

The covering scheme may be any open of an affine scheme, without quasi-compactness.
Surjectivity is expressed on the existing field-valued point classes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space covered by a finite locally free scheme open in an affine scheme
is represented by a scheme over its base.

Source: Stacks Project, Properties of Spaces, Tag 07S6,
proposition-finite-flat-equivalence-global and the following paragraph; Properties,
Tag 01ZY, case (2) (blueprint: lem-sfb-finite-locally-free-open-affine-cover).

Proof:
1. Represent the kernel pair R = U ×_X U using the scheme test U → X. Its diagonal,
   exchange and pairwise composition make it an equivalence-relation groupoid. Both
   projections are finite locally free by hp and surjective by their diagonal section.
2. By lem-sfb-space-fppf-covering-calculus the represented pullbacks of p are fppf
   coverings. Local lifts of a test section of X glue invariant maps out of U into
   any fppf sheaf, so X is the sheafification of U/R, by def-weil-pbc-sheafification.
3. Identify U with its open image in Spec A. Each orbit is finite and nonempty.
   Choose principal opens inside U around its finitely many points, using
   lem-weil-pbc-spec-localization-away-basic-open. By lem-weil-pbc-prime-avoidance
   their generated ideal contains f avoiding every orbit prime. Then D(f) contains
   the orbit and lies in their union, hence in U. It is affine by clause (0) of
   lem-weil-pbc-affine-ideals-closed-subscheme; no finite cover of U is required.
4. By lem-sfb-locally-free-groupoid-invariant-affine choose invariant affine opens
   W covering U. Their restricted relations equal U ×_X W and are finite over W,
   hence affine by def-weil-finite-integral-morphism.
5. Apply lem-a1-finite-flat-affine-relation-quotient to each restricted relation.
   Its affine quotient M represents W/R_W and maps to X by the quotient property.
6. The inclusion W → U is etale by lem-weil-pbc-open-immersion-etale. Apply
   lem-trf-etale-relation-finding-opens to identify each M → X as a representable
   open immersion, using the quotient identifications in steps 2 and 5.
7. On a scheme test T → X, these opens cover T: after the surjective fppf pullback
   T ×_X U → T the assertion follows from the W covering U. The fppf sheaf X is
   also a Zariski sheaf, since open covers are fppf. Thus lem-pc-schemes-criterion
   gives an S-scheme representing X. If U is empty, surjectivity makes X empty;
   the empty open family gives the empty S-scheme. -/
theorem exists_scheme_of_finiteLocallyFree_openAffineCover
    {S : Scheme.{u}} (X : AlgebraicSpace S) (U : Over S)
    (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsRepresentableWith (fun _ _ q ↦ q.left.IsFiniteLocallyFree) p)
    (hsurj : pointImage p = Set.univ)
    (A : CommRingCat.{u}) (j : U.left ⟶ Spec A) [IsOpenImmersion j] :
    ∃ V : Over S, Nonempty (yoneda.obj V ≅ X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
