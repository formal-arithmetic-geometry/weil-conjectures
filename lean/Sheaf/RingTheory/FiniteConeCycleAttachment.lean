module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# Attaching supplied finite free cone cycles

Source: Stacks Project, Tag 064U, descending induction step.
(blueprint: lem-pc-ring-finite-cone-cycle-attachment).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Attach a given finite free family of cone cycles that generates its cohomology.

Source: Stacks Project, Tag 064U, proof of (2) implies (1), induction step.
(blueprint: lem-pc-ring-finite-cone-cycle-attachment).

Proof: Put D = mappingCone f. Compose q with the cycle inclusion into D^(n-1)
and project to F^n and C^(n-1), obtaining a and c. The cycle condition gives
 d_F a = 0 and f a + d_C c = 0. Define G to have P in degree n-1, F^i in
all degrees i >= n, and zero below n-1. Its new differential is a and its
other differentials are those of F. Define g by -c in degree n-1 and f in
the retained degrees. The two cycle equations prove the complex and chain-map
identities. Define j by the identities in degrees at least n and the unique
maps from the zero terms of F below n. Thus j composed with g equals f and
j is invertible in each retained degree. The new term lies below or at b
because n <= b+1; P and the retained terms are finite free, as are zero terms.
In degrees at least n-1, the new cone has the same terms and outgoing maps as
D. Its boundaries in degree n-1 are the old boundaries plus the image of
q in cycles (up to a harmless sign); boundaries in higher degrees do not change.
Consequently its degree-(n-1) homology is the cokernel of q followed by the
homology projection, which is zero by hq, and its higher homology is that of D.
Transfer these homology computations to Q using homologyFunctorFactors. Empty
families and the zero ring are included: an epimorphism from zero forces the
obstruction homology to be zero. No finiteness or choice of generators is
asserted here: the actual module P and cycle map q are inputs. -/
theorem exists_finiteFree_cone_cycle_attachment (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C F : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ C) (b n : ℤ)
    (hn : n ≤ b + 1) (hlow : F.IsStrictlyGE n) (hupp : F.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hvan : ∀ i : ℤ, n ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f))))
    (P : ModuleCat.{v} R) [Module.Free R P] [Module.Finite R P]
    (q : P ⟶ (CochainComplex.mappingCone f).cycles (n - 1))
    (hq : Epi (q ≫ (CochainComplex.mappingCone f).homologyπ (n - 1))) :
    ∃ (G : CochainComplex (ModuleCat.{v} R) ℤ) (g : G ⟶ C) (j : F ⟶ G),
      G.IsStrictlyGE (n - 1) ∧ G.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (G.X i) ∧ Module.Finite R (G.X i)) ∧
      (∀ i : ℤ, n - 1 ≤ i → IsZero
        ((homologyFunctor (ModuleCat.{v} R) i).obj
          (Q.obj (CochainComplex.mappingCone g)))) ∧
      j ≫ g = f ∧ (∀ i : ℤ, n ≤ i → IsIso (j.f i)) := by sorry

end DerivedCategory
