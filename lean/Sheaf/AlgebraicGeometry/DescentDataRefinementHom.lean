module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Descent of morphisms along a refinement

Source: Rydh, Submersions and effective descent of etale morphisms, Proposition (5.6),
printed p.19, supporting Hom-only refinement argument
(blueprint: lem-sfb-descent-data-refinement-hom).

The base category is the full subcategory of quasi-separated schemes. A singleton family
in Mathlib's `Pseudofunctor.DescentData` encodes descent for one morphism. Universal
Hom descent is expressed using all cartesian base-change squares in schemes; this is
independent of the choice of the fibre product. No topology or object-effectivity is assumed.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restriction of descent data along `a` is fully faithful if `a ≫ b` universally
satisfies descent for morphisms. Source: Rydh, Proposition (5.6), printed p.19,
supporting Hom refinement input (blueprint: lem-sfb-descent-data-refinement-hom).

Proof (the explicit argument of the DAG, not a separately stated result in Rydh):
1. Put `p = a ≫ b` and `W = U ×[S] Y`, with projections `t, q`. Fibre products and
   the graph `s = (id, a)` exist by `def-pc-fibre-product`. The quasi-separatedness
   clauses (1)--(3) of `lem-weil-pbc-qcqs-morphism-permanence`, together with
   `def-weil-quasi-separated-morphism`, keep all products in the base category.
   Universal Hom descent gives unique lifting of compatible arrows along every
   base change of `p`, and in particular injectivity on arrows between pullbacks.
2. Given two `b`-data `(A, alpha), (B, beta)` and an arrow `z` between their
   restrictions, define on `W` the arrow
   `h = beta_(at,q) * t^*z * alpha_(at,q)^{-1}` from `q^*A` to `q^*B`.
   Here products mean composition, with the pseudofunctor comparisons inserted.
3. On `W ×[Y] W = U ×[S] U ×[S] Y`, compatibility says
   `beta_12 * z_1 = z_2 * alpha_12`. The two cocycle identities give
   `h_2 = beta_2y * beta_12 * z_1 * alpha_12^{-1} * alpha_2y^{-1} = h_1`.
   Universal descent at `V = Y` supplies a unique `f` with `q^*f = h`.
   Pulling back along `s` and using the diagonal identities gives `a^*f = z`.
4. On `Z = Y ×[S] Y`, test the datum equation for `f` after the base change
   `U ×[S] Z → Z` of `p`. Both sides become
   `beta_u2 * z_u * alpha_u1^{-1}` by the cocycles. Injectivity gives the equation.
5. Any other compatible lift `g` satisfies `q^*g = h = q^*f`, by its datum
   equation on `W`. Injectivity at `V = Y` gives `g = f`. Thus every Hom map is
   bijective. Pullback already defines the functor and preserves the datum
   equations. Only descent isomorphisms were inverted, so fibre arrows need
   not be invertible; neither surjectivity of `a` nor effectiveness was used. -/
theorem fullyFaithful_descentData_refinement
    (G : Pseudofunctor
      (LocallyDiscrete
        (ObjectProperty.FullSubcategory
          (fun X : Scheme.{u} ↦ QuasiSeparatedSpace X))ᵒᵖ) Cat.{v, w})
    {U Y S : ObjectProperty.FullSubcategory
      (fun X : Scheme.{u} ↦ QuasiSeparatedSpace X)}
    (a : U ⟶ Y) (b : Y ⟶ S)
    (h : ∀ (V W : ObjectProperty.FullSubcategory
        (fun X : Scheme.{u} ↦ QuasiSeparatedSpace X))
      (s : V ⟶ S) (t : W ⟶ U) (q : W ⟶ V),
      IsPullback t.hom q.hom (a.hom ≫ b.hom) s.hom →
        Nonempty (G.toDescentData (fun _ : Unit ↦ q)).FullyFaithful) :
    Nonempty (Pseudofunctor.DescentData.pullFunctor G
      (f := fun _ : Unit ↦ b) (f' := fun _ : Unit ↦ a ≫ b)
      (p := 𝟙 S) (α := fun _ : Unit ↦ ()) (p' := fun _ : Unit ↦ a)
      (fun _ : Unit ↦ (Category.comp_id (a ≫ b)).symm)).FullyFaithful := by
  sorry

end AlgebraicGeometry
