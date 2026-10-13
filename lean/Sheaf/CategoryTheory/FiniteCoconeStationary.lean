module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- Finite diagonal tails force eventual stationarity of the cycle and boundary towers.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-stationary).

Proof: Write T for the canonical tower. For every natural t, its subobjects satisfy
Z_t(p,q) = f(p,q)^{-1}(im incomingAlphaIter t (p+2) (q-1)) and
B_t(p,q) = im(initialG(p,q) restricted to ker(alphaIter t p q)).
These identities are proved simultaneously by induction on t. At zero the incoming
iterate is an identity, giving the whole E-object, and the outgoing iterate has zero
kernel, giving zero boundaries. For the successor, use the tower pullback formulas:
the derived D inclusion identifies its D-object with the image of the incoming alpha;
the derived f commutation identifies the lifted cycle condition with membership in
the next incoming image. The derived g commutation identifies the pulled-back image
of the incoming differential with the initial g-image of the next outgoing kernel.
Exactness at D supplies the kernel/image identifications, and the epimorphic tower
projection with kernel B_t makes these equalities of subobjects of the initial E.
Fix p,q and choose the upper bound b on diagonal p+q+1 and the lower bound a on
diagonal p+q. Choose r natural with p+2+r >= b and p-r <= a. For every t >= r,
the source of incomingAlphaIter t (p+2) (q-1) is zero, so Z_t = ker(f(p,q)).
The iterated cocone equation says alphaIter t p q followed by the cocone map at
p-t equals the cocone map at p, after the canonical index transports. The map at
p-t is an isomorphism, hence ker(alphaIter t p q) is the kernel of the cocone map
at p. Thus B_t is its image under initialG, independently of t. Both formulas
also hold at r, proving the required simultaneous stationarity. -/
theorem finiteCocone_stationary
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))) :
    ∀ p q : ℤ, ∃ r : ℕ, ∀ t : ℕ, r ≤ t →
      X.cycleBoundaryTower.Z t p q = X.cycleBoundaryTower.Z r p q ∧
      X.cycleBoundaryTower.B t p q = X.cycleBoundaryTower.B r p q := by sorry

end CategoryTheory.BigradedExactCouple
