module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal
import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # Pseudo-coherent reconstruction over a ring tower with nil kernels

Source: Stacks Project, More on Algebra, Tag 0CQF,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent (all levels pseudo-coherent branch),
and Derived Categories, Tag 0H9J, remark-functoriality-derived-limit.
(blueprint: lem-sfb-nil-ring-pseudocoherent-derived-limit).

The natural-number index zero denotes the source's first level. A limiting ring cone
presents the ring of compatible tuples, with its projection homomorphisms.
`IsDerivedBaseChange` is the existing universal-arrow formulation of the assertion
that the scalar-extension adjunct of the specified arrow is an isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Restrict a varying-ring derived transition to the vertex of a ring cone.
The comparison is the canonical identity-on-elements scalar-restriction comparison,
not an independently chosen morphism.
Source: Stacks Project, Tag 0CQF, the tower regarded in D(A).
(blueprint: lem-sfb-nil-ring-pseudocoherent-derived-limit). -/
def nilRingRestrictedDerivedStep
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A.obj (Opposite.op n))))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (derivedRestrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).obj (K n))
    (n : ℕ) :
    (derivedRestrictScalars (c.π.app (Opposite.op (n + 1))).hom).obj (K (n + 1)) ⟶
      (derivedRestrictScalars (c.π.app (Opposite.op n)).hom).obj (K n) :=
  (derivedRestrictScalars (c.π.app (Opposite.op (n + 1))).hom).map (t n) ≫
    (derivedRestrictScalarsCompIso
      (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op).symm)).hom.app (K n)

/-- Pseudo-coherent complexes reconstruct from a surjective ring tower with nil kernels,
including the scalar-extension adjuncts of the given derived-limit projections.
Source: Stacks Project, Tag 0CQF, all levels pseudo-coherent branch; Tag 0H9J.
(blueprint: lem-sfb-nil-ring-pseudocoherent-derived-limit).

Proof:
1. Choose a bounded-above finite-free model P_0 of K_0 with a marking and cutoff b.
Every element x of the transition kernel is nilpotent, so the finite geometric sum
in -x inverts 1+x. Surjectivity identifies the kernel quotient with the next ring.
2. Apply lem-sfb-jacobson-marked-free-complex-lift inductively, preserving b and the
markings, to lift P_n to P_(n+1). The normalized coefficient adjunction of
lem-pur-sheaf-ring-derived-coefficient-adjunction identifies the resulting maps
with the specified t_n, since bounded-above free complexes are K-flat by
lem-pc-module-bounded-flat-kflat.
3. Lift finite bases along the transitions. Finite Nakayama
(lem-sc-finite-module-surjective-mod-ideal) makes the lifted basis map surjective;
projectivity splits it. Its kernel is finite as a summand of a finite free module,
and its reduction is zero, so a second Nakayama application kills the kernel.
The compatible bases identify each term of P = lim P_n with a finite free module
over c.pt. Its differential is componentwise, P vanishes above b, and the actual
maps P tensor A_n -> P_n are chain isomorphisms on these bases.
4. Apply lem-weil-pbc-surjective-module-complex-tower-limit to P_n. Their markings
intertwine the product transition endomorphisms. Rotate the two Roos triangles,
apply TR3 to the product isomorphisms, and rotate back. This gives Q(P) -> L
commuting with all specified projections. It is invertible by
lemma-weil-pbc-r-lim-levelwise-isomorphism, so L is pseudo-coherent.
5. The bounded-above finite-free P is K-flat. Thus lem-pur-derived-change-of-rings
computes its derived scalar extension by its ordinary tensor complex.
6. Naturality and the representative normalization of the coefficient adjunction
identify the adjunct of each projection, after the isomorphism Q(P) -> L, with
the marking composed with Q(P tensor A_n -> P_n) and the K-flat comparison.
All factors are invertible. This proves IsDerivedBaseChange for each actual
projection, not merely the existence of unrelated reduction isomorphisms. -/
theorem nilRingPseudoCoherentDerivedLimit
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (hsurj : ∀ n : ℕ, Function.Surjective (A.map (homOfLE (Nat.le_succ n)).op).hom)
    (hnil : ∀ (n : ℕ) (x : A.obj (Opposite.op (n + 1))),
      (A.map (homOfLE (Nat.le_succ n)).op).hom x = 0 → IsNilpotent x)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A.obj (Opposite.op n))))
    (hpc : ∀ n : ℕ, DerivedCategory.IsPseudoCoherent (K n))
    (t : ∀ n : ℕ, K (n + 1) ⟶
      (derivedRestrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).obj (K n))
    (ht : ∀ n : ℕ, IsDerivedBaseChange (t n))
    [HasProduct (C := DerivedCategory (ModuleCat.{u} c.pt)) (fun n : ℕ ↦
      (derivedRestrictScalars (c.π.app (Opposite.op n)).hom).obj (K n))]
    (L : DerivedCategory (ModuleCat.{u} c.pt))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (derivedRestrictScalars (c.π.app (Opposite.op n)).hom).obj (K n))
    (δ : (∏ᶜ fun n : ℕ ↦
      (derivedRestrictScalars (c.π.app (Opposite.op n)).hom).obj (K n)) ⟶ L⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (nilRingRestrictedDerivedStep A c K t) L p δ) :
    DerivedCategory.IsPseudoCoherent L ∧
      ∀ n : ℕ, IsDerivedBaseChange
        (f := (c.π.app (Opposite.op n)).hom) (K' := K n)
        (p ≫ Pi.π (C := DerivedCategory (ModuleCat.{u} c.pt)) (fun m : ℕ ↦
          (derivedRestrictScalars (c.π.app (Opposite.op m)).hom).obj (K m)) n) := by
  sorry

end ModuleCat
