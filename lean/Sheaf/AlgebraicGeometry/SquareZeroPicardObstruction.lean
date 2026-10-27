module

public import Sheaf.AlgebraicGeometry.SquareZeroPicardObstructionMap
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility

/-! # Exactness of the square-zero Picard obstruction sequence

Source: Stacks Project, More on Morphisms, Tag 0C6R,
lemma-picard-group-first-order-thickening, middle and final displayed rows
(blueprint: lem-sfb-square-zero-picard-obstruction).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The canonical obstruction vanishes on a line-bundle class exactly when the class
extends to the thickening. Picard groups use additive notation here solely to express
exactness with the additive ordinary module cohomology target. The coefficient on Z is
j*I = I/I², the defining ideal with its quotient O_Z-action.

Source: Stacks Project, More on Morphisms, Tag 0C6R, middle and final rows
(blueprint: lem-sfb-square-zero-picard-obstruction).

Proof:
1. A first order thickening is a homeomorphism on underlying spaces. Since I²=0,
   the O_X-action on I factors through O_Z; tensor pullback identifies j*I with this
   O_Z-module, and its pushforward with I (def-sbc-first-order-thickening and
   def-sbc-closed-immersion-ideal-sheaf).
2. The units sequence is short exact: a ↦ 1+a identifies the additive ideal with its
   kernel, (1+a)(1+b)=1+a+b and (1+a)⁻¹=1-a. Lift a unit and its inverse locally to u,v;
   if uv=1+a, then v(1-a) inverts u. This gives local, not global, surjectivity
   (def-sc-zariski-units-restriction and def-weil-closed-immersion).
3. The abelian-sheaf long exact sequence gives image H¹(u_j) = kernel boundary
   (def-sc-topological-abelian-cohomology).
4. Hilbert 90 identifies Pic with H¹ of units. The canonical closed-immersion
   cohomology comparisons and the module/abelian comparison identify H² of the ideal
   with ordinary H²(Z,j*I). Their composite with the boundary is exactly the defined
   squareZeroPicardObstruction. Restriction compatibility identifies Pic.map j with
   H¹(u_j) under these identifications (thm-sc-hilbert-90,
   lem-sc-cohomology-closed-immersion-pushforward,
   lem-sc-module-abelian-zariski-cohomology and
   lem-sc-picard-h1-restriction-compatibility). Pic.map uses the equivalent pullback;
   uniqueness of left adjoints identifies it with tensorPullback.
5. Transport exactness through these isomorphisms: δ(L)=0 iff its H¹-units class is
   in the image from X, iff L is the restriction of a Picard class on X. No Noetherian,
   properness, reducedness, or dimension hypothesis occurs. -/
theorem exact_picard_squareZeroPicardObstruction {Z X : Scheme.{u}} (j : Z ⟶ X)
    (hj : IsFirstOrderThickening j) :
    Function.Exact (fun L : Additive X.Pic => Additive.ofMul (Pic.map j L.toMul))
      (squareZeroPicardObstruction j hj) := by
  sorry

end AlgebraicGeometry.Scheme
