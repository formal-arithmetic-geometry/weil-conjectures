/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Sheaf.Algebra.Homology.StrictScalarHomChain
import Sheaf.Algebra.Homology.SliceModuleSheafification
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Slice-normalized scalar adjunction for product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03DH and 04IX;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction).

The interfaces below reuse the existing scalar extension, tensor and actual Hom
product projections. They specify the ordinary slice adjunctions and precisely
the nu/theta portion of the scalar-Hom comparison, without its evaluation square.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.StrictScalarHom

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection tensorSection evaluate homMap

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- The normalized ordinary scalar adjunction, including its inverse on generators.
Source: Stacks 03CZ and 03CY
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure NormalizedOrdinaryAdjunction {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) where
  /-- Sheafified sectionwise scalar extension, with its prescribed maps. -/
  extension : Extension.{c, v, u} φ
  /-- The ordinary adjunction supplies mutually inverse, composition-natural bijections. -/
  adjunction : extension.functor ⊣
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  /-- The forward formula at every object. -/
  forward : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g : extension.functor.obj M ⟶ L) (V : Cᵒᵖ) (x : M.val.obj V),
    (adjunction.homEquiv M L g).val.app V x =
      g.val.app V ((eqToHom (extension.obj_eq M).symm).val.app V
        (scalarExtensionSection φ M V 1 x))
  /-- The inverse is the S-linear extension of s tensor x mapping to s h(x). -/
  inverse : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj L)
    (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V),
    ((adjunction.homEquiv M L).symm h).val.app V
        ((eqToHom (extension.obj_eq M).symm).val.app V
          (scalarExtensionSection φ M V s x)) = s • (@id (L.val.obj V) (h.val.app V x))
  /-- Additivity of the bijection, in addition to its inverse and naturality laws. -/
  additive : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g h : extension.functor.obj M ⟶ L),
    adjunction.homEquiv M L (g + h) =
      adjunction.homEquiv M L g + adjunction.homEquiv M L h

/-- The two normalized chain isomorphisms, with both directions of theta specified.
Source: Stacks 03CY, 03CZ and 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure ScalarHomAdjunctionChains {R S : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} (E : Extension.{c, v, u} φ) where
  /-- Identity on the tensor generators, natural as a chain isomorphism. -/
  nu : tensor.{c, v, u} φ ≅ E.complex ⋙ restriction.{c, v, u} φ
  /-- The generator normalization of nu. -/
  nu_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((nu.app A).hom.f n).val.app V) (tensorSection.{c, v, u} φ A n V s x) =
      E.section A n V s x
  /-- An R-linear chain isomorphism of the actual unbounded product Hom complexes. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    (restriction.{c, v, u} φ).obj (homComplex (R := S) (E.complex.obj P) N) ≅
      homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)
  /-- Forward theta, using the actual product projection and slice identity. -/
  theta_forward : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := S) (E.complex.obj P) N).X n).val.obj V)
    (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
        ((((theta P N).hom.f n).val.app V) g) x =
      evaluate.{c, v, u} (E.complex.obj P) N n i k h V g (E.section P i V 1 x)
  /-- Inverse theta on every local tensor generator, for an arbitrary product family. -/
  theta_inverse : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)).X n).val.obj V)
    (s : S.obj.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} (E.complex.obj P) N n i k h V
        ((((theta P N).inv.f n).val.app V) f) (E.section P i V s x) =
      s • (@id ((N.X k).val.obj V)
        (evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V f x))
  /-- Naturality contravariantly in P and covariantly in N, before localization. -/
  theta_natural : ∀ (P P' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (a : P' ⟶ P) (b : N ⟶ N'),
    (restriction.{c, v, u} φ).map (homMap.{c, v, u} (E.complex.map a) b) ≫
        (theta P' N').hom =
      (theta P N).hom ≫ homMap.{c, v, u} a ((restriction.{c, v, u} φ).map b)

variable [∀ W : C, (J.over W).HasSheafCompose
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{max c v u}]

/-- The normalized adjunction on every slice, with comparisons under further restriction.
Source: Stacks 03CZ, 03CY, 03DH and 04IX
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure SliceScalarHomAdjunction {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) where
  /-- Ordinary scalar extension on the original site. -/
  ordinary : NormalizedOrdinaryAdjunction.{c, v, u} φ
  /-- Ordinary adjunction for arbitrary module sheaves on each slice. -/
  slices : ∀ W : C, NormalizedOrdinaryAdjunction.{max c v, v, u}
    ((J.overPullback CommRingCat.{max c v u} W).map φ)
  /-- The unit-normalized comparison between restricted and slice extension. -/
  overIso : ∀ W : C,
    ordinary.extension.functor ⋙
        overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) W ≅
      overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) W ⋙
        (slices W).extension.functor
  /-- The comparison sends the sheafification image of s tensor x to itself. -/
  over_pure : ∀ (W : C)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Over W) (s : S.obj.obj (op V.left)) (x : M.val.obj (op V.left)),
    ((overIso W).hom.app M).val.app (op V)
        ((eqToHom (ordinary.extension.obj_eq M).symm).val.app (op V.left)
          (scalarExtensionSection φ M (op V.left) s x)) =
      (eqToHom ((slices W).extension.obj_eq (M.over W)).symm).val.app (op V)
        (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} W).map φ)
          (M.over W) (op V) s x)
  /-- Further slice restriction also commutes naturally with scalar extension. -/
  furtherIso : ∀ {V W : C} (a : V ⟶ W),
    (slices W).extension.functor ⋙
        overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) a ≅
      overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a ⋙
        (slices V).extension.functor
  /-- Normalization for arbitrary module sheaves on the slice, not only global ones. -/
  further_pure : ∀ {V W : C} (a : V ⟶ W)
    (M : ringedSiteModules.{max c v u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over W))
    (Z : Over V) (s : S.obj.obj (op Z.left))
    (x : M.val.obj (op ((Over.map a).obj Z))),
    ((furtherIso a).hom.app M).val.app (op Z)
        ((eqToHom ((slices W).extension.obj_eq M).symm).val.app
          (op ((Over.map a).obj Z))
            (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} W).map φ)
              M (op ((Over.map a).obj Z)) s x)) =
      ((eqToHom ((slices V).extension.obj_eq
        ((overMap.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).obj M)).symm).val.app
          (op Z))
        (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} V).map φ)
          ((overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).obj M)
          (op Z) s x)
  /-- The normalized natural chain isomorphisms for the global extension. -/
  chains : ScalarHomAdjunctionChains.{c, v, u} ordinary.extension

/-- Slice scalar adjunction and its natural unbounded product-Hom chain isomorphism.
Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03DH and 04IX;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction).

Proof:
1. On each slice, the forgetful functor is continuous and cocontinuous: covering
   sieves are the same arrows with their maps to the base object. The module
   sheafification comparison of lem-weil-pbc-slice-module-sheafification therefore
   identifies scalar extension with restricted scalar extension, preserving its unit.
2. Apply lem-pur-sheaf-ring-coefficient-ordinary-adjunction on each slice. The inverse
   of g mapping to g(1 tensor x) sends s tensor x to s h(x): this is balanced,
   additive and S-linear, commutes with restrictions, and extends uniquely through
   module sheafification. Both composites are identities on generators and hence
   on sheaves, by the tensor and sheafification universal properties.
3. Evaluation on generators shows additivity, R-linearity and compatibility with
   precomposition, postcomposition and further slice restriction. The inverse has
   the same compatibilities by uniqueness. This uses def-pur-sheaf-hom and the
   sectionwise description of def-pur-localized-ringed-site.
4. T(A) and UEA have the same abelian sheafification of the tensor presheaf.
   Uniqueness of the extended R-action gives nu, identity on generators. The
   differential sends s tensor x to s tensor dx on both sides, giving a natural
   chain isomorphism, by def-pur-sheaf-tensor-product and module sheafification.
5. Apply the normalized slice bijection in each integer-indexed product coordinate
   of def-pur-hom-complex. The two displayed formulas are inverse R-linear maps
   of sheaves. No extension functor is applied to an infinite product.
6. On a degree-n family and coordinate i, theta(dg)(x) equals
   d_N(g(1 tensor x)) - (-1)^n g(1 tensor d_P(x)), which is d(theta(g))(x).
   Equality on every slice and coordinate proves the chain-map equation. The
   inverse is a chain map by cancellation, with the exact 0A8X sign convention.
7. For a:P' to P and b:N to N', both naturality composites evaluate to
   b(g(1 tensor a(x))). Product projections detect equality. These constructions
   allow arbitrary unbounded complexes, with no flatness or K-injectivity. -/
theorem exists_sliceScalarHomChainAdjunction
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Nonempty (SliceScalarHomAdjunction.{c, v, u} φ) := by
  sorry

end SheafOfModules.StrictScalarHom
