module

public import Sheaf.AlgebraicGeometry.ThickeningSystemPushforward
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

/-- A lifted adjacent transition becomes invertible after tensor pullback.
Source: Stacks, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting-termwise).

Proof: The morphism i_n is a closed immersion because its composite with j_(n+1)
is the closed immersion j_n and j_(n+1) is a monomorphism. Its kernel is the
pullback of J^(n+1) along j_(n+1). The unit quotient theorem identifies
pushforward of i_n^* G with G modulo this kernel. The ideal-power pushforward
comparison identifies its further pushforward with the quotient of H_(n+1)
by J^(n+1), using eG. The displayed transition equation and the adjunction
identity say that the pushforward of the adjoint of u is the map induced by
the transition of H on that quotient, followed by eF.inv. The adic condition
on H says that this induced map is invertible. Finally the fully faithful
closed pushforward j_n reflects isomorphisms, so the adjoint of u is invertible.
This is a single adjacent quotient comparison, with both coherent terms and
u supplied as inputs; it asserts no existence of an inverse system. -/
theorem thickeningSystemPushforward_adjacent_isIso
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (H : CoherentFormalModule X J) (n : ℕ)
    (F : (T n).Modules) (G : (T (n + 1)).Modules)
    (hF : RingedSpace.IsCoherent (T n).toRingedSpace F)
    (hG : RingedSpace.IsCoherent (T (n + 1)).toRingedSpace G)
    (eF : (Scheme.Modules.pushforward (j n)).obj F ≅ H.obj.obj (op n))
    (eG : (Scheme.Modules.pushforward (j (n + 1))).obj G ≅ H.obj.obj (op (n + 1)))
    (u : G ⟶ (Scheme.Modules.pushforward (i n)).obj F)
    (hu : (Scheme.Modules.pushforward (j (n + 1))).map u ≫
        (thickeningPushforwardComparison j hi n).hom.app F ≫ eF.hom =
      eG.hom ≫ H.obj.map (homOfLE (Nat.le_succ n)).op) :
    IsIso ((ai n).homEquiv G F |>.symm u) := by sorry

end
end AlgebraicGeometry
