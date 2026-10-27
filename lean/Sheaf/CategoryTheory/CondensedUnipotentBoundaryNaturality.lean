module

public import Sheaf.CategoryTheory.CondensedUnipotentClass
import Sheaf.CategoryTheory.CondensedRestrictionMateNormalization
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Positive unipotent boundaries and their naturality

Source: the current six-functors direct-images proof, paragraph (3), dense-lattice input;
returned restriction-calculus steps 11–12, expanded in the node's eight proof steps.
The auxiliary calculation is agent-formulated; an exact external reference is wanted.
General boundary references: Stacks, derived.tex, Tags 0151 and 0152.
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).

The action, biproduct, endpoint maps, positive lift, class and normalized comparisons
are the existing constructions. Every equation below is an equation of actual maps;
no continuous-cochain acyclicity or flatness of coefficient maps is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction (inflate)
open CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

variable {A A' : CondensedBar.Ring.{u}}
variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The triangular action gives a short exact sequence and its positive defect.
The connecting class is the imported `characterClass`, defined from this sequence.
Source: direct-images paragraph (3); Stacks Tags 0151, 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof: (1) additivity of a gives the action law; multiplication and naturality give
linearity and base-change compatibility. The inclusion and projection are equivariant;
the underlying biproduct sequence is split exact and forgetting detects exactness.
(2) apply the canonical single-object short-exact boundary and derived invariants,
compose with the normalized cup unit, and shift down using the signed comparison.
(3) the two coordinates of j(0,1)-(0,1) are a(j) and zero, so the cocycle is +a.
These are the node's first three proof steps, using the recorded action infrastructure,
canonical SES triangle, cup and unipotent-class definitions. -/
theorem unipotentBoundary_positive (a : Character A G) :
    (extensionSequence a).ShortExact ∧
    (∀ (S : Profinite.{u}) (g : C(S, G))
      (z : sections A (extension a).module S),
      first (A := A) S ((extension a).act S g z) =
        first (A := A) S z + a.app S g * second (A := A) S z ∧
      second (A := A) S ((extension a).act S g z) = second (A := A) S z) ∧
    (∀ (S : Profinite.{u}) (g : C(S, G)),
      @Sub.sub (sections A (extension a).module S) inferInstance
        ((extension a).act S g (extensionOneSection a S)) (extensionOneSection a S) =
        ((biprod.inl : Mod.regular A.X ⟶ Mod.regular A.X ⊞ Mod.regular A.X).hom.hom.app
          (op S)) (a.app S g)) := by
  sorry

/-- Restriction identifies the full extension by the identity underlying map, preserving
both endpoint maps and the underlying splitting, and identifies the canonical boundaries.
Source: direct-images paragraph (3), Stacks Tags 0151, 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 4): after restriction the matrix entry is a(u(h)), so the identity on the
biproduct intertwines the actions and fixes i, p and t. Exact restriction and the
canonical SES triangle image lemma identify the last arrows with precisely the
single-object and signed shift comparisons displayed here. -/
theorem unipotentBoundary_restriction (v : H →ₜ* G) (a : Character A G) :
    (∃ e : (inflate v).obj (extension a) ≅ extension (a.restrict v),
      e.hom.val = 𝟙 (Mod.regular A.X ⊞ Mod.regular A.X) ∧
      (inflate v).map (extensionInclusion a) ≫ e.hom =
        extensionInclusion (a.restrict v) ∧
      e.hom ≫ extensionProjection (a.restrict v) =
        (inflate v).map (extensionProjection a) ∧
      (biprod.inr : Mod.regular A.X ⟶ Mod.regular A.X ⊞ Mod.regular A.X) ≫
        e.hom.val = biprod.inr) ∧
    (groupDerived A v).map (extensionExact a).singleδ ≫
      ((groupDerived A v).commShiftIso (1 : ℤ)).hom.app (coefficient A G) ≫
      ((coefficientRestriction (A := A) v).hom)⟦(1 : ℤ)⟧' =
    (coefficientRestriction (A := A) v).hom ≫
      (extensionExact (a.restrict v)).singleδ := by
  sorry

/-- The two-coordinate coefficient map is a morphism of the full short exact sequences,
including the underlying splitting. The underlying comparison is the specified one for
scalar restriction, so no arbitrary map of extensions is substituted.
Source: direct-images paragraph (3), Stacks Tags 0151, 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 6): apply phi to both coordinates. Multiplicativity gives equivariance,
additivity gives linearity after scalar restriction, and naturality gives compatibility
with profinite base change. Direct substitution gives each endpoint and splitting square.
Scalar restriction is exact for every ring map, with no flatness requirement. -/
theorem unipotentBoundary_scalarSequence (φ : A ⟶ A') (a : Character A G) :
    ∃ f : extension a ⟶ (scalarAction (G := G) φ).functor.obj
        (extension (a.coefficients φ)),
      f.val ≫ (scalarAction φ).underlying.hom.app (extension (a.coefficients φ)) =
        biprod.desc
          (regularScalar φ ≫ (scalarModules φ).map
            (biprod.inl : Mod.regular A'.X ⟶ Mod.regular A'.X ⊞ Mod.regular A'.X))
          (regularScalar φ ≫ (scalarModules φ).map
            (biprod.inr : Mod.regular A'.X ⟶ Mod.regular A'.X ⊞ Mod.regular A'.X)) ∧
      extensionInclusion a ≫ f = regularScalarAction (G := G) φ ≫
        (scalarAction φ).functor.map (extensionInclusion (a.coefficients φ)) ∧
      f ≫ (scalarAction φ).functor.map (extensionProjection (a.coefficients φ)) =
        extensionProjection a ≫ regularScalarAction (G := G) φ ∧
      (biprod.inr : Mod.regular A.X ⟶ Mod.regular A.X ⊞ Mod.regular A.X) ≫
        f.val ≫ (scalarAction φ).underlying.hom.app (extension (a.coefficients φ)) =
      regularScalar φ ≫ (scalarModules φ).map
        (biprod.inr : Mod.regular A'.X ⟶ Mod.regular A'.X ⊞ Mod.regular A'.X) := by
  sorry

/-- The scalar connecting square commutes in the ordinary derived action category,
with its actual coefficient arrow and canonical scalar shift comparison.
Source: direct-images paragraph (3), Stacks Tags 0151, 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 6): the preceding morphism of extensions gives boundary naturality.
The exact-functor SES image lemma identifies the scalar-restricted boundary with the
localized boundary of the scalar-restricted sequence. Insert its single and shift
comparisons; the endpoint maps become the specified coefficient arrow. -/
theorem unipotentBoundary_scalarBoundary (φ : A ⟶ A') (a : Character A G) :
    (extensionExact a).singleδ ≫ (coefficientArrow (G := G) φ)⟦(1 : ℤ)⟧' =
    coefficientArrow (G := G) φ ≫
      (scalarDerived φ G).map (extensionExact (a.coefficients φ)).singleδ ≫
      ((scalarDerived φ G).commShiftIso (1 : ℤ)).hom.app (coefficient A' G) := by
  sorry

/-- The normalized coefficient comparison commutes with the invariant connecting square.
Source: direct-images paragraph (3)
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 7): apply F_J to the scalar boundary square. Naturality of the normalized
comparison d_J and its signed shift compatibility identify the two resulting composites.
This is the connecting square before composing with the invariant unit. -/
theorem unipotentBoundary_coefficientConnecting (φ : A ⟶ A') (a : Character A G) :
    (derived A G).map (extensionExact a).singleδ ≫
      ((derived A G).commShiftIso (1 : ℤ)).hom.app (coefficient A G) ≫
      (coefficientCupMap (G := G) φ)⟦(1 : ℤ)⟧' =
    coefficientCupMap (G := G) φ ≫
      (scalarBase φ).map ((derived A' G).map (extensionExact (a.coefficients φ)).singleδ ≫
        ((derived A' G).commShiftIso (1 : ℤ)).hom.app (coefficient A' G)) ≫
      ((scalarBase φ).commShiftIso (1 : ℤ)).hom.app (cohomology A' G) := by
  sorry

/-- The normalized restriction and coefficient arrows preserve the positive class.
Source: direct-images paragraph (3), Stacks Tags 0151, 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 5): the restriction mate's last-arrow square and cup-unit equation,
composed with the restriction boundary identity, give equality of shifted classes;
shift down. (Step 7) apply derived invariants to the scalar boundary square. Naturality
and shift compatibility of d_J and the coefficient cup-unit equation give the same
identity after applying invariants; shift down with the canonical scalar comparison.
The resulting equations are actual derived arrows, not just cohomology classes. -/
theorem unipotentBoundary_naturality (v : H →ₜ* G) (φ : A ⟶ A') (a : Character A G) :
    characterClass a ≫ groupCupMap (A := A) v = characterClass (a.restrict v) ∧
    characterClass a ≫ coefficientCupMap (G := G) φ =
      (baseRingArrow φ)⟦(-1 : ℤ)⟧' ≫
        ((scalarBase φ).commShiftIso (-1 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor (Modules A') 0).obj (Mod.regular A'.X)) ≫
        (scalarBase φ).map (characterClass (a.coefficients φ)) := by
  sorry

/-- A zero character has zero canonical boundary and zero class, including the trivial
group and zero ring cases.
Source: direct-images paragraph (3), Stacks Tag 0152
(blueprint: lem-sfb-condensed-unipotent-boundary-naturality).
Proof (step 8): for zero a the second inclusion is equivariant. Map the split sequence
with zero first endpoint and identity projection to this extension, using t in the
middle. Its boundary has zero target; boundary naturality forces this boundary to be
zero. Additivity of derived invariants forces its class to be zero. A trivial group
forces every a to vanish by the character identity law; a zero ring has only zero
sections. No continuous-cochain acyclicity assertion is used. -/
theorem unipotentBoundary_zero (a : Character A G) (ha : ∀ S g, a.app S g = 0) :
    (extensionExact a).singleδ = 0 ∧ characterClass a = 0 := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
