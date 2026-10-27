module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
import Sheaf.RingTheory.FilteredColimitFiniteData
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Simple residue roots lift at a henselian stage

Source: Stacks Project, Algebra, Tag 04GI, `lemma-colimit-henselian`, polynomial and
simple-root descent in the proof (blueprint: lem-sfb-henselian-colimit-stage-root).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace CommRingCat

/-- A monic polynomial and its simple residue root over a local ring colimit descend
simultaneously to a henselian stage, where the residue root lifts to an actual root.
The maps `ρ` are specified on every residue representative, so they are exactly the
canonical induced maps, not additional choices. The hypothesis `hrescolim` is the
universal property of the residue-field diagram in commutative rings. Its compatibility
condition is tested on residue representatives; the residue maps are surjective, so this
is precisely compatibility with the induced residue-field transition maps.

Source: Stacks Project, Algebra, Tag 04GI, `lemma-colimit-henselian`, proof from the
monic polynomial and simple residue root through the stage solution.
(blueprint: lem-sfb-henselian-colimit-stage-root).

Proof for stage 3:
1. If n = 0, monicity gives f = 1, contradicting its residue root. Thus n > 0.
2. By lemma-nagata-filtered-colimit-finite-data, descend the finitely many coefficients
   below degree n to one stage p. Adjoin the leading term T^n to obtain a monic lift
   of degree n. The given colimit is canonically isomorphic to the chosen colimit,
   so that finite-data theorem applies to the specified cocone as well.
3. By lem-pc-filtered-colimit-commrings-elementwise (1), the assumed residue colimit
   supplies a representative of a₀ at some stage q. Directedness moves both the
   polynomial and residue root to a common stage i. The cocone equalities preserve
   their prescribed images, monicity and degree.
4. The canonical map ρ i reflects zero: a residue representative mapping to zero has
   image in the colimit maximal ideal, hence belongs to the stage maximal ideal by
   hlegs. Evaluation and formal differentiation commute with coefficient maps.
   Thus the descended polynomial vanishes at the residue root, and its derivative
   there is nonzero, since its image is nonzero. These calculations work in every
   characteristic.
5. Apply lem-weil-pbc-henselian-local-root-lifting, the simple-root criterion for the
   henselian local ring at i. It gives aᵢ with fᵢ(aᵢ) = 0 and residue a₀ᵢ, completing
   all the required clauses. -/
theorem exists_monic_simple_root_stage
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [∀ i : I, HenselianLocalRing (F.obj i)]
    (hlocal : ∀ (i j : I) (hij : i ≤ j),
      (maximalIdeal (F.obj j)).comap (F.map (homOfLE hij)).hom = maximalIdeal (F.obj i))
    (c : Cocone F) (hc : IsColimit c) [IsLocalRing c.pt]
    (hlegs : ∀ i : I, (maximalIdeal c.pt).comap (c.ι.app i).hom = maximalIdeal (F.obj i))
    (ρ : ∀ i : I, ResidueField (F.obj i) →+* ResidueField c.pt)
    (hρ : ∀ (i : I) (x : F.obj i), ρ i (residue (F.obj i) x) = residue c.pt (c.ι.app i x))
    (hrescolim : ∀ (B : CommRingCat.{u}) (β : ∀ i : I, ResidueField (F.obj i) →+* B),
      (∀ (i j : I) (hij : i ≤ j) (x : F.obj i),
        β j (residue (F.obj j) (F.map (homOfLE hij) x)) = β i (residue (F.obj i) x)) →
      ∃! g : ResidueField c.pt →+* B, ∀ i : I, g.comp (ρ i) = β i)
    (n : ℕ) (f : Polynomial c.pt) (hf : f.Monic) (hdegree : f.natDegree = n)
    (a₀ : ResidueField c.pt) (hroot : (f.map (residue c.pt)).eval a₀ = 0)
    (hsimple : (f.derivative.map (residue c.pt)).eval a₀ ≠ 0) :
    ∃ (i : I) (fᵢ : Polynomial (F.obj i)) (a₀ᵢ : ResidueField (F.obj i)) (aᵢ : F.obj i),
      fᵢ.Monic ∧ fᵢ.natDegree = n ∧ fᵢ.map (c.ι.app i).hom = f ∧ ρ i a₀ᵢ = a₀ ∧
      (fᵢ.map (residue (F.obj i))).eval a₀ᵢ = 0 ∧
      (fᵢ.derivative.map (residue (F.obj i))).eval a₀ᵢ ≠ 0 ∧
      fᵢ.eval aᵢ = 0 ∧ residue (F.obj i) aᵢ = a₀ᵢ := by
  sorry

end CommRingCat
