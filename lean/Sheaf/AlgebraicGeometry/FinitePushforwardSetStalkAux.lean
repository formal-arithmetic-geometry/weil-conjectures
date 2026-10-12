module

public import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.Mathlib.RingTheory.Henselian

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-sets-finite-pushforward-stalk-map-bijective)
The substantive restriction-of-germs bijection in the finite pushforward stalk formula,
assuming finiteness of the geometric fibre.

Source: Stacks Project, Proposition 59.55.2, Tag 03QP (1), first display and its
proof. The proof identifies the pushforward stalk with sections of the inverse image
on the strict henselization. A finite base change is affine and its finite algebra is
a product of henselian local factors; the separably closed residue field makes every
factor strictly henselian. The resulting clopen pieces form a disjoint etale cover,
so the sheaf condition identifies sections on the whole base change with the product
of sections on the pieces. Sections on each piece identify with its stalk, and
inverse-image stalks identify with the stalks of `H`. Matching the unique geometric
point of each factor with the finite geometric fibre, then checking a representative
germ, gives exactly the displayed restriction map. -/
 theorem finite_pushforward_set_stalk_map_bijective_of_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (H : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (hfin : Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) :
    Function.Bijective
        (fun a : (Scheme.pointSmallEtale y).sheafFiber.obj
            ((f.Etale.sheafPushforwardContinuous (Type (u + 1))
              Y.smallEtaleTopology X.smallEtaleTopology).obj H) ↦
          fun t : {x : Spec (.of Ω) ⟶ X // x ≫ f = y} ↦
            (colimit.pre
              ((CategoryOfElements.π (Scheme.pointSmallEtale t.1).fiber).op ⋙ H.obj)
              (Etale.baseChangeNbhd f y t).op) a) := by
  sorry

end AlgebraicGeometry
