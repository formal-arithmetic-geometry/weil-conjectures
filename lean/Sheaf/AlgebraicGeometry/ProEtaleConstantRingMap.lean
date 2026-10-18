/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# The canonical inverse-image map for finite pro-etale coefficients

Source: Weil conjectures blueprint, sec-proper-base-change/sk-thm-properbasechange,
order 1235; Stacks Project, Tags 04B3, 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

The coefficient objects are the recorded sheafifications of continuous functions on
connected components. The direct-image map is constructed on these functions by
precomposition with the fibre-product projection and then extended by sheafification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Pull a continuous function back to the fibre product and take its sheafified section.
This sends a constant `a` to its constant scalar section on the fibre product.
Source: blueprint order 1235, definition of rho; Stacks Tag 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map). -/
noncomputable def finiteCoefficientDirectImageApp (W : V.ProEtᵒᵖ) :
    (finiteCoefficientPresheaf V Λ).obj W ⟶
      ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ)).obj.obj W :=
  RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨(pullback.fst W.unop.hom f).continuous.connectedComponentsMap,
          (pullback.fst W.unop.hom f).continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl } ≫
    (toSheafify (Scheme.ProEt.topology U) (finiteCoefficientPresheaf U Λ)).app
      ((Scheme.proEtaleBaseChange f).op.obj W)

/-- The fibre-product section maps commute with restriction.
Source: blueprint order 1235, construction of rho; Stacks Tag 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

Proof: the first projection commutes with base change of every arrow of the site.
Apply its map on connected components and precompose a continuous function. The two
resulting functions agree pointwise; naturality of the sheafification unit gives the
claimed equality after sheafification. -/
theorem finiteCoefficientDirectImageApp_naturality
    {W W' : V.ProEtᵒᵖ} (a : W ⟶ W') :
    (finiteCoefficientPresheaf V Λ).map a ≫ finiteCoefficientDirectImageApp f Λ W' =
      finiteCoefficientDirectImageApp f Λ W ≫
        ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (finiteCoefficientRingSheaf U Λ)).obj.map a := by
  sorry

/-- The presheaf map underlying rho: pull functions back along the first projection.
On each open fibre it is the specified constant section, so its value is precisely
what the open-fibre gluing construction gives.
Source: blueprint order 1235, definition of rho; Stacks Tags 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map). -/
noncomputable def finiteCoefficientDirectImagePresheafMap :
    finiteCoefficientPresheaf V Λ ⟶
      ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ)).obj where
  app := finiteCoefficientDirectImageApp f Λ
  naturality _ _ a := finiteCoefficientDirectImageApp_naturality f Λ a

/-- The ring-sheaf map rho, obtained by the sheafification universal property.
Source: blueprint order 1235, definition of rho; Stacks Tags 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map). -/
noncomputable def finiteCoefficientDirectImageMap :
    finiteCoefficientRingSheaf V Λ ⟶
      (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientDirectImagePresheafMap f Λ)

/-- The canonical map c_f is the ring-sheaf adjunct of rho.
Source: blueprint order 1235, definition of c_f; Stacks Tag 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map). -/
noncomputable def finiteCoefficientInverseImageMap :
    (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj
      (finiteCoefficientRingSheaf V Λ) ⟶ finiteCoefficientRingSheaf U Λ :=
  ((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientDirectImageMap f Λ)

/-- The canonical comparison from constant-presheaf sheafification preserves constants.
Source: blueprint order 1235, constant-sheaf identification; Stacks Tag 0H7J
(blueprint: prop-weil-pbc-proetale-constant-ring-map). -/
noncomputable def finiteCoefficientConstantComparison (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of Λ) ⟶
      finiteCoefficientRingSheaf T Λ :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientScalarMap T Λ)

/-- Constant sections give the unique constant-sheaf identification.
Source: blueprint order 1235, constant-sheaf identification; Stacks Tags 04B3 and 0H7J
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

Proof: for each continuous function to the discrete ring, its open fibres cover the
scheme by pro-etale objects, using weakly-etale localization. Glue the corresponding
constant sections of the constant sheaf. Distinct fibres intersect in the empty object,
where every ring sheaf has a unique section by the empty-cover axiom. On simultaneous
fibres addition and multiplication are the ring operations on constants, so this is a
ring map. Naturality and uniqueness follow from restriction to the fibre covers.
Extend by sheafification; the two composites are identities since they fix constants
and hence all functions locally. Uniqueness follows from the same argument and the
sheafification universal property. -/
theorem finiteCoefficientConstantComparison_isIso (T : Scheme.{u}) :
    IsIso (finiteCoefficientConstantComparison Λ T) ∧
      ∀ e : (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of Λ) ⟶
          finiteCoefficientRingSheaf T Λ,
        toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ)) ≫ e.hom =
          finiteCoefficientScalarMap T Λ → e = finiteCoefficientConstantComparison Λ T := by
  sorry

/-- The canonical coefficient inverse-image map is an isomorphism, for finite rings
without a commutativity hypothesis and for arbitrary scheme morphisms.
Source: blueprint order 1235; Stacks Tags 04B3, 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

Proof: (1) the empty cover forces sections of any ring sheaf on the empty object to
form the zero ring, so constants there need not be distinct. (2) A continuous function
on connected components is equivalently a continuous function on the scheme; its
open fibres are pro-etale objects by weakly-etale localization and form a cover.
(3) Glue the images of its constant values to identify ring-sheaf maps from the
coefficient sheaf to G with ring maps from Lambda to G(T). Ring operations and
restriction are checked on simultaneous fibre covers. (4) The same argument identifies
the coefficient sheaf uniquely with the constant-presheaf sheafification. These are
`def-weil-pbc-proetale-site`, `def-weil-pbc-proetale-modules`,
`lem-weil-proetale-weakly-etale-localization`, `def-weil-pbc-sheafification` and
`def-weil-pbc-constant-sheaf`.
(5) Apply the ring-sheaf adjunction of `def-weil-proetale-inverse-image` and evaluate
direct image at the terminal object.
Both Hom functors are ring maps from Lambda to G(U). Precomposition by c_f is the
identity under these bijections, by the defining normalization of rho on constants.
(6) Surjectivity with target the source of c_f supplies a left inverse; injectivity
with target its codomain gives the other inverse identity. This also covers U empty. -/
theorem finiteCoefficientInverseImageMap_isIso :
    IsIso (finiteCoefficientInverseImageMap f Λ) := by
  sorry

end ProEtale

namespace ProEtale

/-- For commutative coefficients the constant-preserving identifications carry c_f
exactly to the structure map of the recorded pro-etale inverse-image construction.
The equality is written as a commuting square, avoiding any arbitrary choice of inverse.
Source: blueprint order 1235, final comparison; Stacks Tags 0H7J and 09A5
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

Proof: on constants both direct-image maps send a to the constant section a on the
fibre product. The fibre-cover argument and the sheafification universal property
make these maps equal after the canonical identifications. Taking adjuncts gives
the displayed square. The identifications are uniquely constant-preserving by
finiteCoefficientConstantComparison_isIso, so this is the claimed structure map. -/
theorem finiteCoefficientInverseImageMap_constant
    {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).map
        (finiteCoefficientConstantComparison Λ V) ≫ finiteCoefficientInverseImageMap f Λ =
      Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} (RingCat.of Λ) ≫
        finiteCoefficientConstantComparison Λ U := by
  sorry

/-- On an empty source both coefficient sheaves are zero ring sheaves and the canonical
map is their unique morphism (and, by the preceding theorem, an isomorphism).
Source: blueprint order 1235, empty-source clause; Stacks Tag 04B3
(blueprint: prop-weil-pbc-proetale-constant-ring-map).

Proof: any object over an empty scheme is empty. The empty family covers it, so the
sheaf axiom gives precisely one section for each of the two ring sheaves. Thus each
section ring is the zero ring. Two sheaf maps agree on all these singleton section
rings, hence are equal. The general isomorphism assertion applies without change. -/
theorem finiteCoefficientInverseImageMap_empty
    {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] [IsEmpty U] :
    (∀ W : U.ProEtᵒᵖ,
      Subsingleton (((Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf V Λ)).obj.obj W) ∧
      Subsingleton ((finiteCoefficientRingSheaf U Λ).obj.obj W)) ∧
    ∀ c : (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf V Λ) ⟶ finiteCoefficientRingSheaf U Λ,
      c = finiteCoefficientInverseImageMap f Λ := by
  sorry

end ProEtale

end AlgebraicGeometry
