module

public import Sheaf.CategoryTheory.GroupoidStackificationMap
public import Sheaf.CategoryTheory.GroupoidTwoFiberCone
import Sheaf.CategoryTheory.LargeSetSheafification

/-! # Stackification commutes with two-fibre products

Source: Stacks Project, Tag 04Y2, via Tag 04Y1
(blueprint: lem-sfb-stackification-two-fibre-products).

All four stackifications are arbitrary maps satisfying the recorded local description.
The extensions `fa`, `ga` of `iY f`, `iY g` with their comparisons `ef`, `eg`, and the
two-fibre product `q` of `fa` and `ga`, are arbitrary as well: the result holds for every
such choice, so a citer may use its own extensions and its own two-fibre product.
The cone on `W` specifies the stackified projections and their comparison. The cone
comparison to `q` expresses compatibility of the equivalence with those data. The map
`k` and its comparison specify the functor induced by the original stackification maps;
`rho` identifies its extension with the equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w

open CategoryTheory Opposite
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

/-- Stackification preserves the two-fibre product, with its projections and 2-cell.

Source: Stacks Project, Tag 04Y2, via Tag 04Y1
(blueprint: lem-sfb-stackification-two-fibre-products).

The extensions `fa`, `ga` with comparisons `ef`, `eg` and the two-fibre product `q` are
arbitrary; such extensions exist by the extension property of
`lem-sfb-groupoid-stackification-local-description`.

Proof: let `fa`, `ga` be the given extensions of `iY f` and `iY g`. Their two-fibre
product `Q` is a stack by `lem-sfb-stack-groupoid-two-fibre-products`.
Its canonical map `k` sends `(x,z,alpha)` to `(iX x,iZ z,eg⁻¹ iY(alpha) ef)`.
Extend it across `iP` to `h`.
For pairs of original objects, the isomorphism presheaf of their two-fibre product
is the fibre product of the two factor isomorphism presheaves over the middle one.
The arrow-sheafification property and `lem-weil-pbc-sheafification-sets-exact` identify
the two resulting sheaves. Both maps to the factors are the sheafifications of those
of `k`, so this identification is precisely the map induced by `h`.
For arbitrary objects of `W`, choose common local representatives using the local-image
property. The preceding identification proves local full faithfulness. Unique lifts
of arrows agree after further restriction and glue by the isomorphism sheaf axiom;
hence `h` is fibrewise fully faithful.
For `(xi,zeta,gamma)` in `Q`, choose local lifts of `xi` and `zeta`. The transported
comparison `gamma` is locally an original arrow by
`lem-weil-pbc-large-set-sheafification`. Thus the triple is locally in the image of
`k`, hence of `h`. The criterion `lem-sfb-stack-fully-faithful-local-equivalence`
gives a pullback-compatible inverse and the two invertible modifications.
Extend the projections and comparison to `W` by the same local-representative
argument: conjugate the components on original objects by local representative
isomorphisms. Changes of representative are locally original arrows by the
arrow-sheafification property, so naturality makes these components agree on
refinements. The target morphism sheaves glue them uniquely. The same uniqueness
proves naturality, compatibility with pullback, and the equation for the comparison
2-cell. This gives the cone `r` and the two cone comparisons. The extension of `k`
is identified with `h` by `rho`.
No pullbacks in the base are needed: intersections and transitivity of covering
sieves provide all common refinements, including empty covering sieves. -/
theorem stackification_twoFiberProducts
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    {X Y Z P Xa Ya Za W : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {f : StrongTrans X Y} {g : StrongTrans Z Y}
    (p : GroupoidTwoFiberCone f g P) (hp : p.IsTwoFiberProduct)
    (iX : StrongTrans X Xa) (iY : StrongTrans Y Ya) (iZ : StrongTrans Z Za)
    (iP : StrongTrans P W)
    (hX : IsGroupoidStackification J iX) (hY : IsGroupoidStackification J iY)
    (hZ : IsGroupoidStackification J iZ) (hP : IsGroupoidStackification J iP)
    (fa : StrongTrans Xa Ya) (ga : StrongTrans Za Ya)
    (ef : StrongTrans.Iso (StrongTrans.vcomp iX fa) (StrongTrans.vcomp f iY))
    (eg : StrongTrans.Iso (StrongTrans.vcomp iZ ga) (StrongTrans.vcomp g iY))
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    (q : GroupoidTwoFiberCone fa ga Q) (hq : q.IsTwoFiberProduct) :
    Q.IsStack J ∧
      ∃ (r : GroupoidTwoFiberCone fa ga W)
        (er : GroupoidTwoFiberCone.Comparison p r iP iX iY iZ ef eg)
        (h : StrongTrans W Q) (hinv : StrongTrans Q W),
        Nonempty (StrongTrans.Iso (StrongTrans.vcomp h hinv) (StrongTrans.id W)) ∧
        Nonempty (StrongTrans.Iso (StrongTrans.vcomp hinv h) (StrongTrans.id Q)) ∧
        Nonempty (GroupoidTwoFiberCone.SameComparison r q h) ∧
        ∃ k : StrongTrans P Q,
          Nonempty (StrongTrans.Iso (StrongTrans.vcomp iP h) k) ∧
          Nonempty (GroupoidTwoFiberCone.Comparison p q k iX iY iZ ef eg) := by
  sorry

/-- An already stacked factor can use itself and the identity as its stackification.

Source: Stacks Project, Tag 04Y2 and the local description of Tag 02ZP
(blueprint: lem-sfb-stackification-two-fibre-products).

Proof: its isomorphism presheaves are already sheaves, so their sheafification units
are isomorphisms and supply the arrow comparison with the identity. Every object
is in the identity's image on the maximal covering sieve. A functor into a stack
extends across the identity as itself, with the unitor as the comparison. -/
theorem groupoid_stackification_identity
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (hA : ∀ T : C, IsGroupoid (A.obj (.mk (op T)))) (hstack : A.IsStack J) :
    IsGroupoidStackification J (StrongTrans.id A) := by
  sorry

end CategoryTheory.Pseudofunctor
