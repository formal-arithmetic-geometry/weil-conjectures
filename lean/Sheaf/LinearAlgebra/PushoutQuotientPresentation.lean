module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Explicit quotient presentation of a module pushout

The binary direct sum is represented by the product module, with its standard linear
inclusions. All pairs have finite support, so this is the binary instance of the direct sum.

Source: Stacks, Tag 0AUM, `lemma-domination-universally-injective`, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation)
-/

@[expose] public section

universe u v w x t

namespace LinearMap

section Construction

variable {R : Type u} [CommRing R]
variable {P : Type v} {Q : Type w} {Q' : Type x}
variable [AddCommGroup P] [AddCommGroup Q] [AddCommGroup Q']
variable [Module R P] [Module R Q] [Module R Q']

/-- The relation map `x ↦ (b x, -a x)` into the binary direct sum.
Source: Stacks, Tag 0AUM, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation) -/
def pushoutRelation (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') : P →ₗ[R] Q' × Q :=
  b.prod (-a)

/-- The explicit pushout carrier, the binary direct sum modulo the relation image.
Source: Stacks, Tag 0AUM, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation) -/
abbrev PushoutQuotient (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :=
  (Q' × Q) ⧸ LinearMap.range (pushoutRelation a b)

/-- The quotient projection onto the explicit pushout.
Source: Stacks, Tag 0AUM, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation) -/
def pushoutQuotientMap (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :
    Q' × Q →ₗ[R] PushoutQuotient a b :=
  (LinearMap.range (pushoutRelation a b)).mkQ

/-- The leg `j y = π (y, 0)` from `Q'` to the explicit pushout.
Source: Stacks, Tag 0AUM, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation) -/
def pushoutQuotientInl (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :
    Q' →ₗ[R] PushoutQuotient a b :=
  (pushoutQuotientMap a b).comp (LinearMap.inl R Q' Q)

/-- The leg `k z = π (0, z)` from `Q` to the explicit pushout.
Source: Stacks, Tag 0AUM, first proof paragraph.
(blueprint: lem-trf-module-pushout-quotient-presentation) -/
def pushoutQuotientInr (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :
    Q →ₗ[R] PushoutQuotient a b :=
  (pushoutQuotientMap a b).comp (LinearMap.inr R Q' Q)

end Construction

/-- The quotient presentation, its universal property, and the unique comparison to any
chosen pushout, with both legs fixed.

Source: Stacks, Tag 0AUM, `lemma-domination-universally-injective`, first proof paragraph,
expanded into its quotient and colimit universal properties.
(blueprint: lem-trf-module-pushout-quotient-presentation)

Proof plan:
1. Componentwise linearity makes the image of `(b, -a)` a submodule. The quotient-module
   construction gives a surjective projection with exactly that kernel
   [def-weil-pbc-direct-sum-modules, def-weil-pbc-quotient-module].
2. The coordinate inclusions followed by the projection give `j` and `k`. The relation
   `(b x, -a x)` vanishes in the quotient, giving `j b = k a`. Every pair splits into its
   two coordinates, giving `π (y, z) = j y + k z` [the same two definition nodes].
3. For compatible `u, v`, the linear map `(y, z) ↦ u y + v z` kills the relation image.
   The quotient-induced-map lemma descends it to `T / ⊥`; the canonical singleton-coset
   identification `T / ⊥ ≃ₗ[R] T` gives `h` and its displayed evaluation formula
   [lem-weil-pbc-quotient-module-induced-map].
4. Setting either coordinate to zero gives the leg equations. Any other map with those
   equations has the same value on every pair, hence is equal by surjectivity of the
   projection [def-weil-pbc-quotient-module].
5. A cocone on the finite span is precisely a pair of maps with equal composites from
   `P`. Steps 2--4 are its colimit universal property [def-weil-pbc-category-colimit].
6. For another pushout, the two universal properties give maps in both directions fixing
   the legs. Uniqueness makes their composites identities; hence the forward map is a
   linear equivalence. The same uniqueness proves uniqueness of that equivalence
   [def-weil-pbc-category-colimit]. -/
theorem pushout_quotient_presentation
    {R : Type u} [CommRing R] {P Q Q' : Type v}
    [AddCommGroup P] [AddCommGroup Q] [AddCommGroup Q']
    [Module R P] [Module R Q] [Module R Q']
    (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :
    Function.Surjective (pushoutQuotientMap a b) ∧
    LinearMap.ker (pushoutQuotientMap a b) = LinearMap.range (pushoutRelation a b) ∧
    (pushoutQuotientInl a b).comp b = (pushoutQuotientInr a b).comp a ∧
    (∀ (T : Type t) [AddCommGroup T] [Module R T]
      (u : Q' →ₗ[R] T) (v : Q →ₗ[R] T), u.comp b = v.comp a →
      ∃ h : PushoutQuotient a b →ₗ[R] T,
        h.comp (pushoutQuotientInl a b) = u ∧
        h.comp (pushoutQuotientInr a b) = v ∧
        (∀ h' : PushoutQuotient a b →ₗ[R] T,
          h'.comp (pushoutQuotientInl a b) = u →
          h'.comp (pushoutQuotientInr a b) = v → h' = h) ∧
        ∀ (y : Q') (z : Q), h (pushoutQuotientMap a b (y, z)) = u y + v z) ∧
    CategoryTheory.IsPushout (ModuleCat.ofHom a) (ModuleCat.ofHom b)
      (ModuleCat.ofHom (pushoutQuotientInr a b))
      (ModuleCat.ofHom (pushoutQuotientInl a b)) ∧
    (∀ (Q'' : Type v) [AddCommGroup Q''] [Module R Q'']
      (c : Q →ₗ[R] Q'') (b' : Q' →ₗ[R] Q''),
      CategoryTheory.IsPushout (ModuleCat.ofHom a) (ModuleCat.ofHom b)
        (ModuleCat.ofHom c) (ModuleCat.ofHom b') →
      ∃! e : PushoutQuotient a b ≃ₗ[R] Q'',
        e.toLinearMap.comp (pushoutQuotientInl a b) = b' ∧
        e.toLinearMap.comp (pushoutQuotientInr a b) = c) := by
  sorry

end LinearMap
