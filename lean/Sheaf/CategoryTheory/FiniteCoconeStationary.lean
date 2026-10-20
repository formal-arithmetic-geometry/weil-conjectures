module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.FiniteBoundaryAlphaKernel
import all Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries
import Sheaf.CategoryTheory.FiniteCycleFormula
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

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
      X.cycleBoundaryTower.B t p q = X.cycleBoundaryTower.B r p q := by
  intro p q
  obtain ⟨a, _, ha, _⟩ := hA (p + q)
  obtain ⟨_, b, _, hb⟩ := hA (p + q + 1)
  let r := max (p - a).toNat (b - p - 2).toNat
  have hcycles (t : ℕ) (ht : r ≤ t) :
      X.cycleBoundaryTower.Z t p q = kernelSubobject (X.f p q) := by
    have hbound : b ≤ p + 2 + (t : ℤ) := by dsimp [r] at ht; omega
    have hsrc : IsZero (X.D (p + 2 + (t : ℤ)) (q - 1 - (t : ℤ))) := by
      convert hb (p + 2 + t) hbound using 1
      congr 1
      omega
    rw [finiteCycle_formula X t p q,
      hsrc.eq_zero_of_src (X.incomingAlphaIter t (p + 2) (q - 1)),
      imageSubobject_zero]
    apply le_antisymm
    · apply le_kernelSubobject
      have hw := (Subobject.isPullback (X.f p q) ⊥).w
      rw [← hw]
      simp
    · apply Subobject.le_of_factors
      apply pullback_factors
      rw [kernelSubobject_arrow_comp]
      exact Subobject.factors_zero
  have hboundaries (t : ℕ) (ht : r ≤ t) :
      X.cycleBoundaryTower.B t p q =
        (Subobject.«exists» (X.initialG p q)).obj
          (kernelSubobject (eqToHom (by congr 1; omega) ≫ (A (p + q)).ι p)) := by
    have hbound : p - (t : ℤ) ≤ a := by dsimp [r] at ht; omega
    have := ha (p - t) hbound
    have hker : kernelSubobject (X.alphaIter t p q) =
        kernelSubobject (eqToHom (by congr 1; omega) ≫ (A (p + q)).ι p) := by
      have hh := congrArg
        (fun f : X.D p q ⟶ (A (p + q)).obj ↦ kernelSubobject f)
        (alphaIter_cocone X (p + q) (A (p + q)) t p q rfl)
      simpa only [← Category.assoc, kernelSubobject_comp_mono] using hh
    rw [finiteBoundary_alphaKernel X t p q, hker]
  refine ⟨r, ?_⟩
  intro t ht
  exact ⟨(hcycles t ht).trans (hcycles r le_rfl).symm,
    (hboundaries t ht).trans (hboundaries r le_rfl).symm⟩

end CategoryTheory.BigradedExactCouple
