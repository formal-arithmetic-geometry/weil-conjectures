module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Open diagonal of an unramified algebraic space over a scheme

Source: Stacks Project, spaces-morphisms.tex, Tags 05W1(1) and 03ZK(7), with scheme
target (blueprint: lem-sfb-unramified-space-open-diagonal).

Representability by open immersions is tested on every scheme over the base. The
pullback and its diagonal are formed in presheaves, hence on all test schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space unramified over a scheme has representable open diagonal.
Source: Stacks Project, Tag 05W1(1), with scheme target; the chartwise unramified
hypothesis is Tag 03ZK(7) (blueprint: lem-sfb-unramified-space-open-diagonal).

Proof:
1. Put P = A ×_T A. For any scheme b : Z → P, its pullback W along the diagonal
   is the equality functor of the two induced maps Z → A. It is also the pullback
   of the absolute diagonal of A along their pair, so is a scheme by
   def-trf-algebraic-space. The projection h : W → Z is a monomorphism on all test
   schemes, since its accompanying point of A is determined uniquely. Choose an
   etale surjective scheme atlas q : U → A, using def-trf-algebraic-space.
2. The hypothesis gives unramified U → T. Its diagonal d : U → U ×_T U is open
   by def-weil-unramified-morphism, hence etale by
   lem-weil-pbc-etale-composition-cancellation(1). Use def-pc-fibre-product.
3. The map v = q ×_T q : U ×_T U → P is representable etale. On a test scheme
   C → P its pullback is C₁ ×_C C₂, where Cᵢ = C ×_A U for the two projections.
   Both Cᵢ → C are etale by def-trf-algebraic-space. Base change and composition
   (lem-weil-pbc-etale-base-change-finite-limits(1) and
   lem-weil-pbc-etale-composition-cancellation(2)) give etaleness of the product.
4. Set C = Z ×_P (U ×_T U) and E = C ×_(U ×_T U) U. Scheme fibre products exist
   by def-pc-fibre-product. Base change of d followed by C → Z is etale by the
   same base-change and composition results. On every test scheme, E consists of
   pairs (z,u) with b(z) = (q(u),q(u)), so E = Z ×_P U for the composite Δq.
5. Inserting or forgetting x = q(u) identifies E with W ×_A U, naturally on
   every test scheme. Thus p : E → W is surjective etale by the atlas clause of
   def-trf-algebraic-space.
6. Apply lem-trf-etale-descent-through-source-cover to E → W → Z. The first
   arrow is surjective etale and the composite is etale, so h is etale. This
   requires no quasi-compactness, separation or Noetherian hypotheses.
7. By def-weil-etale-morphism, h is flat and locally of finite presentation.
   Together with its monicity, lem-pe-flat-lfp-monomorphism-open makes h an open
   immersion. By def-weil-open-immersion its source is isomorphic over Z to an
   open subscheme. Since Z and b were arbitrary, this is the asserted
   IsRepresentableWith condition, including nonreduced and empty test schemes. -/
theorem unramified_space_open_diagonal {S : Scheme.{u}} (T : Over S)
    (A : AlgebraicSpace S) (f : A.obj.obj ⟶ yoneda.obj T)
    (hf : ∀ (V : Over S) (a : yoneda.obj V ⟶ A.obj.obj), IsEtale a →
      IsUnramified (yoneda.preimage (a ≫ f)).left) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (pullback.diagonal f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
