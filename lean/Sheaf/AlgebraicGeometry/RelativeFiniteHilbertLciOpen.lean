module

public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CategoryTheory.Sites.Precoverage

/-! # The open unramified-lci part of the relative finite Hilbert stack

Source: Stacks Project, criteria.tex, Tag 06CL (lemma-lci-locus-stack-in-groupoids),
and examples-stacks.tex, Tag 05WB (lemma-hilbert-d-stack)
(blueprint: lem-sfb-relative-finite-hilbert-lci-open).

The existing full subcategory `Lci` is equipped with its inherited projection and
inclusion. The statement retains the representing equivalence, compatibility with
the projection to the test scheme, and the universal factorization criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelativeFiniteHilbert

variable {S : Scheme.{u}} {X : BasedCategory.{v₁, w₁} (Over S)}
  {Y : BasedCategory.{v₂, w₂} (Over S)}

/-- The existing full unramified-lci subcategory with its inherited projection to
`Sch/S`. This adds no objects or arrows to `Lci`.
Source: Stacks 06CL, construction before the lemma
(blueprint: lem-sfb-relative-finite-hilbert-lci-open). -/
def lciGroupoid (F : BasedFunctor X Y) (d : ℕ+)
    (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y)
    (hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (hflat : FlatLfp R) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (fun A : RelativeFiniteHilbert F d ↦ IsLciObject A (R A.T A.y)) ⋙
      base : Lci (d := d) hX hY hF R hflat ⥤ Over S)

/-- The canonical full inclusion `j_d : L_d(F) → H_d(F)` over the scheme base.
Source: Stacks 06CL, displayed inclusion
(blueprint: lem-sfb-relative-finite-hilbert-lci-open). -/
def lciInclusion (F : BasedFunctor X Y) (d : ℕ+)
    (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y)
    (hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (hflat : FlatLfp R) :
    BasedFunctor (lciGroupoid F d hX hY hF R hflat) (groupoid F d hX hY) where
  toFunctor := ObjectProperty.ι _
  w := rfl

/-- Both finite Hilbert groupoids are fppf stacks, and the unramified-lci full
subcategory is represented over every Hilbert object by an open subscheme of its
base. The representing equivalence is compatible with the actual base projection;
the last clause identifies precisely which base changes belong to `L_d(F)`.
Source: Stacks Project, criteria.tex, Tag 06CL; examples-stacks.tex, Tag 05WB
(blueprint: lem-sfb-relative-finite-hilbert-lci-open).

Proof:
1. Descend the finite locally free degree-d covers by
   lem-sfb-finite-locally-free-fppf-descent. Their pullbacks cover the descended
   scheme by lem-trf-fppf-covering-base-change. Stack descent in Y and X glues y
   and x, and the isomorphism sheaf in Y glues the comparison. Descend arrows by
   the same cover-descent theorem and the two isomorphism sheaves. This proves
   fppf descent for H_d(F), including the fibred-groupoid condition.
2. On a test scheme, both the pullback of X_y and the representative for the
   pulled-back y classify a map to the new base, an X-object, and its comparison
   with y. Their natural identifications give the same space and induced map;
   use lem-trf-space-fibre-products-etale-covers. The Hilbert comparison square
   also identifies these maps under isomorphisms of Hilbert objects.
3. The source cover is finite locally free, hence flat, locally finitely presented
   and closed by lem-weil-pbc-finite-closed-map-finite-fibres. The representative
   projection is flat and locally finitely presented by hflat. Apply
   lem-sfb-space-closed-source-unramified-base-open and
   lem-sfb-space-relative-lci-parameter-open, using the specified two-chart
   interpretation of each property. Intersect their two parameter opens. A base
   map factors through the intersection exactly when its pulled-back induced
   map is both unramified and lci.
4. The relative fibre of the full inclusion over A has objects consisting of an
   lci object and an identification with the pullback of A. Each fibre is empty
   or contractible by fullness. Step 3 identifies it naturally with the functor
   of points of the intersection open, compatibly with its projection to A.T.
   This gives the equivalence and projection identity in the conclusion.
5. A descent datum in L_d descends in H_d by step 1. All cover maps factor through
   its open from step 3; joint surjectivity forces that open to be the entire
   base. Thus the descended object is in L_d. Fullness gives arrow descent and
   uniqueness. Neither surjectivity of F nor algebraicity of X or Y is used.
-/
theorem lci_open (F : BasedFunctor X Y) (d : ℕ+)
    (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y)
    (hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (hflat : FlatLfp R) :
    IsFppfModuliStack (groupoid F d hX hY) ∧
    IsFppfModuliStack (lciGroupoid F d hX hY hF R hflat) ∧
    ∀ A : RelativeFiniteHilbert F d,
      ∃ (W : Over S) (i : W ⟶ A.T), IsOpenImmersion i.left ∧
        (∃ e : BasedFunctor (discreteModuli (yoneda.obj W))
            (relativeFiber (F := lciInclusion F d hX hY hF R hflat) A),
          e.toFunctor.IsEquivalence ∧
            ∀ z : (discreteModuli (yoneda.obj W)).obj,
              eqToHom (e.w_obj z).symm ≫
                relativeProjection (F := lciInclusion F d hX hY hF R hflat) A (e.obj z) =
                yoneda.preimage (z.hom ≫ yoneda.map i)) ∧
        ∀ (T' : Over S) (g : T' ⟶ A.T),
          IsLciObject (A.pullback hX.1 hY.1 g)
              (R T' (A.pullback hX.1 hY.1 g).y) ↔
            ∃ f : T' ⟶ W, f ≫ i = g := by
  sorry

end AlgebraicGeometry.RelativeFiniteHilbert
