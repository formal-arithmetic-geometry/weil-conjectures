/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSetStalk
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits

/-! # Conservative geometric stalks on an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 04JY, 04K0, 04K1 and 04K5;
Sites, Tags 00Y8 and 00YL
(blueprint: lem-sfb-space-etale-conservative-geometric-points).

The existing `pointedSetStalk` is literally the colimit of sections over the opposite
of `PointedEtale`; its action on maps is the induced colimit map. We use this actual
construction, including its existing germ maps, without choosing new stalk data.
Coefficients and all small colimit shapes lie in the containing universe
`max (u + 1) w`; schemes and geometric fields lie in universe `u`.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Geometric stalks preserve finite limits and all small colimits, detect mono/epi/iso,
and jointly detect equality of parallel sheaf maps. The final clause treats the empty
space explicitly: all its scheme charts are empty, and any two sheaves are isomorphic.
Here `pointedSetStalk` is the already defined pointed-neighbourhood colimit, not an
abstract point functor supplied as an extra hypothesis.

Source: Stacks Project, Properties of Spaces, Tags 04JY, 04K0, 04K1 and 04K5;
Sites, Tags 00Y8 and 00YL
(blueprint: lem-sfb-space-etale-conservative-geometric-points).

Proof, following the ten steps of the node:
1. Fix \bar x and use [lem-sfb-space-pointed-etale-neighbourhoods-cofiltered]. Restrictions
define D_F:\mathcal N_{\bar x}^{op}\to\mathbf{Set}; a sheaf map acts on each representative
section, and hence on the colimit, giving the stalk functor. The cited neighbourhood lemma
supplies a small filtered opposite index. For any finite diagram of sheaves,
[lem-weil-pbc-site-sheaf-sets-limits-sectionwise] computes its limit at U as the limit of
section sets. Applying [lem-weil-pbc-filtered-colimits-commute-finite-limits] therefore
identifies the stalk of this limit with the limit of the stalks, including the empty diagram.
This proves finite-limit preservation.

2. For a set A put L(U)=\operatorname{Hom}_X(\operatorname{Spec}\Omega,U) and
P_A(U)=\operatorname{Map}(L(U),A), with restriction by precomposition. This is a sheaf: for a
covering \{U_i\to U\}, every l\in L(U) lifts to an l_i\in L(U_i) by
[lem-weil-pbc-etale-cover-geometric-point-lift], since the covering is a jointly surjective
etale family of schemes. Matching functions glue by a(l)=a_i(l_i); two choices give a lift to
U_i\times_U U_j by [def-pc-fibre-product], so matching makes this independent of choices and
unique. This verifies exactly the sheaf condition, even when L(U) is empty. The universal
property of the colimit gives inverse natural bijections \operatorname{Map}(F_{\bar
x},A)\cong\operatorname{Hom}(F,P_A): send b to s\mapsto(l\mapsto b([U,l,s])); send \alpha to
[U,l,s]\mapsto\alpha_U(s)(l). Naturality of \alpha says the latter respects each restriction
relation. Thus the stalk functor is left adjoint to A\mapsto P_A.

3. Apply [lem-weil-pbc-left-adjoint-preserves-colimits] to the adjunction in step 2. For every
small diagram admitting a colimit in the sheaf category, its image cocone is a colimit cocone of
sets. This proves preservation of all small colimits in the categorical sense, without
substituting an objectwise presheaf colimit for the sheaf colimit.

4. If a:F\to G is mono, its diagonal d:F\to F\times_G F is invertible: the two projections agree
since their composites with a agree, and either projection is inverse to d. By step 1, d_{\bar
x} is the diagonal F_{\bar x}\to F_{\bar x}\times_{G_{\bar x}}F_{\bar x}, so it is bijective.
The diagonal of a set map is bijective exactly when that map is injective. Thus every a_{\bar x}
is injective. The required sheaf fibre product exists by the cited limits node.

5. Conversely assume every a_{\bar x} injective. If s,t\in F(U) have a(s)=a(t), choose for each
u\in U an algebraic closure of \kappa(u) and its geometric point \bar u of U, using
[lem-pc-algebraic-closure-exists-unique] and [def-weil-geometric-point]. Compose to \bar x on X.
The germs of s,t in F_{\bar x} are equal. By [lem-weil-pbc-filtered-colimit-sets-elementwise](3)
and the cofiltered-neighbourhood node, they become equal on some pointed refinement V\to U. This
is etale by [lem-trf-space-chartwise-etale-permanence], since both V,U are etale over X, and its
image contains u. The family of all such refinements is a covering of U by
[def-trf-algebraic-space]; it is a set in the fixed small-site universe. Sheaf separatedness
gives s=t. Thus all component maps of a are injective, which makes a mono: equality after a of
two natural transformations is equality at each section. For U empty the empty covering gives
the same separatedness argument.

6. If a is epi, [lem-weil-pbc-site-sheaf-sets-epi-locally-surjective] supplies local lifts of
every t\in G(U). Given a stalk element, represent it by (U,\bar u,t) using
[lem-weil-pbc-filtered-colimit-sets-elementwise] and the cofiltered-neighbourhood node. Choose a
covering \{U_i\to U\} and sections lifting t|_{U_i}. By
[lem-weil-pbc-etale-cover-geometric-point-lift], \bar u lifts to some U_i with the same field.
The corresponding lifted section represents a preimage of the original stalk element. Hence
a_{\bar x} is surjective.

7. Assume instead all a_{\bar x} surjective, and take t\in G(U). For each u\in U, choose \bar u
using the algebraic-closure and geometric-point nodes as in step 5 and put \bar x=\bar u\to X.
Choose a preimage in F_{\bar x} of the germ of t. The elementwise filtered-colimit node
represents it on a pointed neighbourhood V and represents equality of its image with t on a
common pointed refinement W\to V,U. Thus there is s\in F(W) with a(s)=t|_W. The map W\to U is
etale by the permanence node and hits u. All such refinements form a covering by the small-site
covering definition. For empty U take the empty covering. This gives local surjectivity, hence a
is epi by the cited epi characterization.

8. An isomorphism gives bijective stalk maps by functoriality. Conversely bijective stalks give
both sectionwise injectivity (step 5) and local surjectivity (step 7). For t\in G(U) choose
local lifts s_i\in F(U_i). On U_i\times_U U_j their images are both the restriction of t, so
sectionwise injectivity makes the lifts agree. The sheaf condition glues them uniquely to s\in
F(U) with a(s)=t; this equality is checked on the covering by separatedness of G. Thus every
component of a is bijective. The component inverses are natural by applying the naturality
identity of a and cancelling its bijective components. Hence a is an isomorphism.

9. For maps a,b:F\to G agreeing on all stalks, let e:E\to F be their equalizer, which exists by
[lem-weil-pbc-site-sheaf-sets-limits-sectionwise]. Step 1 identifies e_{\bar x} with the
equalizer of the equal maps a_{\bar x},b_{\bar x}, hence a bijection. Step 8 makes e invertible;
from ae=be obtain a=b.

10. If X=\varnothing, every scheme U\to X is empty, and the empty family covers it by the
jointly-surjective covering definition in [def-trf-algebraic-space]. The sheaf equalizer
condition in [def-weil-pbc-sites-and-cohomology] forces F(U) to be a singleton, since both
products indexed by the empty covering are singletons. Every sheaf is therefore uniquely
isomorphic to the singleton sheaf and every morphism is invertible; parallel morphisms agree.
There are no geometric points, so all the stalkwise tests are vacuous, as required.
-/
theorem etaleGeometricStalks_conservative {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ S)
      (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      PreservesFiniteLimits (X.pointedSetStalk.{u, w} x) ∧
        PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}
          (X.pointedSetStalk.{u, w} x)) ∧
    (∀ (F G : Sheaf X.etaleTopology (Type (max (u + 1) w))) (α : F ⟶ G),
      (Mono α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        Function.Injective ((X.pointedSetStalk x).map α)) ∧
      (Epi α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        Function.Surjective ((X.pointedSetStalk x).map α)) ∧
      (IsIso α ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        Function.Bijective ((X.pointedSetStalk x).map α))) ∧
    (∀ (F G : Sheaf X.etaleTopology (Type (max (u + 1) w))) (α β : F ⟶ G),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (b : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        (X.pointedSetStalk x).map α = (X.pointedSetStalk x).map β) → α = β) ∧
    ((∀ U : X.EtaleSite, IsEmpty ((X.etaleForget).obj U)) →
      ∀ F G : Sheaf X.etaleTopology (Type (max (u + 1) w)), Nonempty (F ≅ G)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
