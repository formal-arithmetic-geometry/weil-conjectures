/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import WeilConjectures.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Recognizing an algebraic space from an étale sheaf and a scheme atlas

Source: Stacks Project, bootstrap.tex, Tag 0BH4
(lemma-spaces-etale-locally-representable), scheme-atlas specialization
(blueprint: lem-sfb-etale-sheaf-space-atlas-bootstrap).

The input presheaf is assumed to satisfy only étale descent. Its atlas pullbacks
are algebraic spaces, with étaleness and surjectivity stated on scheme charts.
The conclusion supplies fppf descent for the very same presheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale sheaf with a scheme atlas whose pullbacks are surjective étale algebraic
spaces is an algebraic space in the fppf convention. The square in `hatlas` represents
`h_T ×_F h_U`; its projection is `p`. The universal chart clause states étaleness,
and the existential clause supplies a surjective étale chart surjective onto `T`.
Source: Stacks Project, bootstrap.tex, Tag 0BH4, scheme-atlas specialization
(blueprint: lem-sfb-etale-sheaf-space-atlas-bootstrap).

Proof:
1. Apply `hatlas` to `T = U` and the image under `q` of the identity. The resulting
   space `R` represents pairs of maps to `U` with equal `q`-images. Swapping the pair
   shows both projections are chartwise étale. The pair map to `U ×_S U` is a
   monomorphism and an equivalence relation; diagonal pairs give projection sections
   (def-pc-fibre-product).
2. The pair map is chartwise locally of finite type: for a chart `V → R`, its first
   projection to `U` is étale, hence locally finitely presented and locally of finite
   type (def-weil-etale-morphism, def-sbc-locally-finite-presentation,
   def-weil-finite-type-morphism). Around an arbitrary affine target open in `U ×_S U`,
   shrink to a principal open mapping into an affine open of the first `U`. Shrink a
   finite-type affine chart of `V` to a principal open inside its inverse image.
   If its rings factor as `A → B_b → C` with `C` finitely generated over `A`, the same
   generators and `1/b` generate `C` over `B`. This requires no separation of `U/S`.
3. Apply lem-sfb-space-lft-monomorphism-separated-lqf to this monomorphism, then
   lem-a1-separated-locally-qf-space-representable over the scheme `U ×_S U`, to
   represent `R` by a scheme, retaining its projections and functor of points.
4. The identity chart makes both scheme projections étale. Their sections make
   them surjective. Apply lem-trf-etale-relation-quotient: the fppf quotient `Q` is
   an algebraic space, its atlas has étale-local lifts, and its kernel pair is `R`.
   Thus two maps to `U` have equal images in `Q` exactly when their `q`-images agree.
5. The fppf sheaf `Q` is an étale sheaf because étale covers are fppf covers
   (def-pc-fppf-site, def-weil-etale-morphism). Lift a section of `Q` étale-locally
   to `U`; the kernel-pair identity makes its `q`-images agree on overlaps. Étale
   descent in `F` gives a section of `F`.
6. On a common fibre-product refinement, two choices differ by an `R`-pair, so
   their `q`-images agree. Uniqueness of gluing proves independence and naturality,
   giving `φ : Q → F` with `φπ = q` (def-weil-pbc-etale-site).
7. If two sections of `Q` have the same `φ`-image, choose local atlas lifts on a
   common refinement. Equality of their `q`-images makes an `R`-pair, so their
   `Q`-images agree. Separatedness of the étale sheaf `Q` gives injectivity.
8. For `a ∈ F(T)`, choose the chart in `hatlas` whose composite to `T` is surjective
   étale. The pullback square gives a local lift to `U`, hence to `Q`. Its two
   restrictions to the overlap agree by injectivity from step 7. Descent for `Q`
   glues a preimage of `a`; separatedness of `F` proves its image is `a`, also for
   empty schemes (def-trf-algebraic-space, def-pc-fibre-product).
9. Thus `φ` is a natural isomorphism. Transport fppf gluing from `Q` to `F`.
   Transport its representable diagonal and surjective étale scheme atlas as well;
   these are exactly the clauses of def-trf-algebraic-space. -/
theorem etale_sheaf_space_atlas_bootstrap {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (U : Over S) (q : yoneda.obj U ⟶ F)
    (hatlas : ∀ (T : Over S) (a : F.obj (op T)),
      ∃ (P : AlgebraicSpace S) (p : P.obj.obj ⟶ yoneda.obj T)
        (r : P.obj.obj ⟶ yoneda.obj U),
        IsPullback r p q (yonedaEquiv.symm a) ∧
        (∀ (V : Over S) (c : yoneda.obj V ⟶ P.obj.obj),
          IsEtale c → Etale (yoneda.preimage (c ≫ p)).left) ∧
        ∃ (V : Over S) (c : yoneda.obj V ⟶ P.obj.obj),
          IsEtale c ∧ IsSurjective c ∧
            Surjective (yoneda.preimage (c ≫ p)).left) :
    ∃ hfppf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F,
      IsAlgebraicSpace ⟨F, hfppf⟩ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
