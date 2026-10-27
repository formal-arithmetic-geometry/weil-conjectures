module

public import Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # The proper Hilbert presheaf for algebraic spaces

Source: Stacks Project, quot.tex, situation-hilb preceding Tag 0D00
(blueprint: def-sfb-space-proper-hilbert-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A B : AlgebraicSpace S}

/-- Closed-subspace classes whose structural maps are proper, flat and finitely presented.
Source: Stacks, situation-hilb (blueprint: def-sfb-space-proper-hilbert-functor). -/
abbrev ProperHilbertFamily (a : A ⟶ B) (T : ProperQuotTest B) :=
  {C : ClosedSubspace (properQuotFibre a T) //
    MapIsProper (C.val.arrow ≫ properQuotSnd a T) ∧
    MapIsFlat (C.val.arrow ≫ properQuotSnd a T) ∧
    ProperQuotFinitePresentation (C.val.arrow ≫ properQuotSnd a T)}

/-- Inverse image exists and determines a unique closed-subspace class.
Source: Stacks, situation-hilb and Tag 03MB
(blueprint: def-sfb-space-proper-hilbert-functor).
Proof: the closed-ideal correspondence constructs the inverse-image subspace, whose ideal
is the image of the pulled-back ideal. Base-change stability of properness, flatness and
finite presentation gives its three admissibility properties. Any two cartesian squares
have a unique isomorphism over the ambient space by their universal properties; they
therefore define the same subobject. This proves existence and uniqueness, including for
non-flat base changes and empty subspaces. -/
theorem properHilbertPullback_existsUnique (a : A ⟶ B)
    {T' T : ProperQuotTest B} (h : T' ⟶ T) (C : ProperHilbertFamily a T) :
    ∃! D : ProperHilbertFamily a T',
      ∃ k : (D.val.val : AlgebraicSpace S) ⟶ (C.val.val : AlgebraicSpace S),
        IsPullback k D.val.val.arrow C.val.val.arrow (properQuotFibreMap a h) := by
  sorry

/-- Inverse image, determined uniquely as a closed-subspace class by its cartesian square.
Source: Stacks, situation-hilb (blueprint: def-sfb-space-proper-hilbert-functor). -/
def properHilbertMap (a : A ⟶ B) {T' T : ProperQuotTest B} (h : T' ⟶ T)
    (C : ProperHilbertFamily a T) : ProperHilbertFamily a T' :=
  (properHilbertPullback_existsUnique a h C).exists.choose

/-- Identity inverse image fixes each closed-subspace class.
Source: Stacks, situation-hilb (blueprint: def-sfb-space-proper-hilbert-functor).
Proof: the fibre map for an identity test map is identity by its two projections.
The identity square is cartesian, so uniqueness in properHilbertPullback_existsUnique
identifies its closed-subspace class with the given class. -/
theorem properHilbertMap_id (a : A ⟶ B) (T : ProperQuotTest B) :
    properHilbertMap a (𝟙 T) = id := by
  sorry

/-- Successive inverse images equal inverse image under the composite on subspace classes.
Source: Stacks, situation-hilb (blueprint: def-sfb-space-proper-hilbert-functor).
Proof: paste the two cartesian inverse-image squares. Fibre maps compose by their two
projections. The resulting cartesian square and the square for the composite determine
the same closed-subspace class by properHilbertPullback_existsUnique. -/
theorem properHilbertMap_comp (a : A ⟶ B) {T'' T' T : ProperQuotTest B}
    (h : T'' ⟶ T') (k : T' ⟶ T) :
    properHilbertMap a (h ≫ k) = properHilbertMap a h ∘ properHilbertMap a k := by
  sorry

/-- The presheaf of proper flat finitely presented closed subspaces, with inverse images
as its transitions. Source: Stacks, situation-hilb
(blueprint: def-sfb-space-proper-hilbert-functor). -/
def properHilbertFunctor (a : A ⟶ B) : (ProperQuotTest B)ᵒᵖ ⥤ Type (u + 1) where
  obj T := ProperHilbertFamily a T.unop
  map h := TypeCat.ofHom (properHilbertMap a h.unop)
  map_id T := congrArg TypeCat.ofHom (properHilbertMap_id a T.unop)
  map_comp h k := congrArg TypeCat.ofHom (properHilbertMap_comp a k.unop h.unop)

end AlgebraicGeometry.AlgebraicSpace
