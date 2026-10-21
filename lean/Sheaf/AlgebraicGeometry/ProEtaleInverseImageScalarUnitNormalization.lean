/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Scalar-unit normalization of the specified pro-etale inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2 and 03EL, Section 03EK;
Sites, Tag 00YV (blueprint: lem-pur-inverse-image-scalar-unit-normalization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules MonoidalCategory
open scoped ChangeOfRings
open CanonicalRingedTensorComparisonOnSmallSites
namespace SheafOfModules
universe c v d z w
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] monoidalCategory

variable {C : Type c} {D : Type d} [Category.{v} C] [Category.{z} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{w}) (RI : Sheaf JD CommRingCat.{w})
  (uInv : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
  (AI : AlgebraicInverseImage uInv R RI) (g : C ⥤ D)

/-- The comparison normalized by the identity-scalar-extension isomorphism.
This is exactly a inverse, followed by mu, followed by a tensor a.
Source: Stacks Project, Tag 03EL and the scalar-unit cancellation of Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def CanonicalRingedTensorComparisonOnSmallSites.normalizedHom
    (T : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI))
    (ho : ∀ M, T.obj M = changeOfRings.{z, d, w} (𝟙 RI) (AI.modules.obj M))
    (k : CanonicalRingedTensorComparisonOnSmallSites R RI RI uInv AI (𝟙 RI) T ho)
    (a : T ≅ AI.modules)
    (M N : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    AI.modules.obj ((monoidalCategory.{v, c, w} R).tensorObj M N) ⟶
      (monoidalCategory.{z, d, w} RI).tensorObj (AI.modules.obj M) (AI.modules.obj N) :=
  a.inv.app ((monoidalCategory.{v, c, w} R).tensorObj M N) ≫ (k.mu M N).hom ≫
    (monoidalCategory.{z, d, w} RI).tensorHom (a.hom.app M) (a.hom.app N)

/-- The full section equation for a supplied unit-section operation. The theorem below
supplies the specified pro-etale adjunction unit, rather than an arbitrary section map.
Factoring this formula over abstract sites avoids unfolding concrete sites repeatedly.
Source: Stacks Project, Tag 03EL and Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def scalarUnitComparisonNormalized
    (η : ∀ (M : SheafOfModules.{w} ((sheafCompose JC
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (V : C),
      M.val.obj (op V) → (AI.modules.obj M).val.obj (op (g.obj V)))
    (T : SheafOfModules.{w} ((sheafCompose JC
        (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI))
    (ho : ∀ M, T.obj M = changeOfRings.{z, d, w} (𝟙 RI) (AI.modules.obj M))
    (a : T ≅ AI.modules) : Prop :=
  ∀ (k : CanonicalRingedTensorComparisonOnSmallSites R RI RI uInv AI (𝟙 RI) T ho)
    (M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) (V : C)
    (s : M.val.obj (op V)) (t : N.val.obj (op V)),
    (normalizedHom R RI uInv AI T ho k a M N).val.app (op (g.obj V))
      (η ((monoidalCategory.{v, c, w} R).tensorObj M N) V
        (ringedComparisonPure R M N (op V) s t)) =
    ringedComparisonPure RI (AI.modules.obj M) (AI.modules.obj N) (op (g.obj V))
      (η M V s) (η N V t)

end SheafOfModules

namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] monoidalCategory
-- Keep the specified abbrev folded while elaborating section rings. This affects
-- local elaboration only; the declaration and its mathematical value are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] proEtaleSheafInverseImage

/-- The specified set-unit section, viewed through an algebraic presentation's
underlying-sheaf identification. This is evaluation of the existing unit and isomorphism.
Source: Stacks Project, Tag 03D2 and Sites Tag 00YV
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
noncomputable def proEtaleAlgebraicUnitSection {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (AI : AlgebraicInverseImage (proEtaleSheafInverseImage h (Type (u + 1))) R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
    (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1}
    RingCat.{u + 1})).obj R)) (V : Y.ProEt) (s : M.val.obj (op V)) :
    (AI.modules.obj M).val.obj (op ((proEtaleBaseChange h).obj V)) :=
  (AI.moduleUnderlying.inv.app M).hom.app (op ((proEtaleBaseChange h).obj V))
    (((proEtaleSheafAdjunction h (Type (u + 1))).unit.app
      ((toSheaf.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u
    + 1})).obj R) ⋙ sheafCompose (ProEt.topology Y)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M)).hom.app (op V) s)

/-- The full certificate in the scalar-unit normalization statement. Its fields retain
all specified functors, unit identifications, scalar formulas and the universally quantified
comparison formula. No data are selected from a mere existence theorem.
Source: Stacks Project, Tags 03D2, 03EL and Section 03EK
(blueprint: lem-pur-inverse-image-scalar-unit-normalization). -/
structure ProEtaleScalarUnitNormalization {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) where
  algebraic : AlgebraicInverseImage (proEtaleSheafInverseImage h (Type (u + 1))) R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
  modules_eq : algebraic.modules = proEtaleModuleInverseImage h R
  ring_unit : ∀ (V : Y.ProEt) (r : R.obj.obj (op V)), algebraic.ringUnderlying.hom.hom.app (op
    ((proEtaleBaseChange h).obj V)) (((proEtaleSheafAdjunction h (Type (u + 1))).unit.app
    ((sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj R)).hom.app
    (op V) r) = ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app (op V) r
  module_unit : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (V : Y.ProEt) (s : M.val.obj (op V)), (eqToHom
    (congrArg (fun (F : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤ ringedSiteModules.{u + 1} ((sheafCompose
    (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))) ↦ F.obj M) modules_eq)).val.app
    (op ((proEtaleBaseChange h).obj V)) (proEtaleAlgebraicUnitSection h R algebraic M V s) =
    (((pullbackPushforwardAdjunction (proEtaleModelRingUnit h R)).unit.app ((proEtaleModuleToModel
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj
    M)).val.app (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V))) s
  scalar : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤ ringedSiteModules.{u + 1} ((sheafCompose
    (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R))
  scalar_obj : ∀ M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R), scalar.obj M = changeOfRings.{u, u + 1, u + 1}
    (𝟙 ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M)
  scalar_map : ∀ (M N : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : M ⟶ N), scalar.map f = eqToHom (scalar_obj
    M) ≫ changeOfRingsHom.{u, u + 1, u + 1} (𝟙 ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M) (algebraic.modules.map f) ≫ eqToHom
    (scalar_obj N).symm
  multiplication : scalar ≅ algebraic.modules
  multiply_pure : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (W : X.ProEtᵒᵖ) (b : ((proEtaleSheafInverseImage
    h CommRingCat.{u + 1}).obj R).obj.obj W) (m : (algebraic.modules.obj M).val.obj W),
    (multiplication.hom.app M).val.app W ((eqToHom (scalar_obj M).symm).val.app W
    (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)).obj)).unit.app (changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M))).app W
    (b ⊗ₜ[((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W, RingHom.id _] m)))
    = b • m
  insert_one : ∀ (M : ringedSiteModules.{u + 1} ((sheafCompose (ProEt.topology Y) (forget₂
    CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (W : X.ProEtᵒᵖ) (m : (algebraic.modules.obj
    M).val.obj W), (multiplication.inv.app M).val.app W m = ((eqToHom (scalar_obj M).symm).val.app
    W (((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((proEtaleSheafInverseImage h
    CommRingCat.{u + 1}).obj R)).obj)).unit.app (changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)) (algebraic.modules.obj M))).app W
    ((1 : ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W)
    ⊗ₜ[((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R).obj.obj W, RingHom.id _] m)))
  normalized : scalarUnitComparisonNormalized.{u + 1, u, u + 1, u, u + 1}
    (C := Y.ProEt) (D := X.ProEt) (JC := ProEt.topology Y) (JD := ProEt.topology X)
    R
    ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R)
    (proEtaleSheafInverseImage h (Type (u + 1))) algebraic (proEtaleBaseChange h)
    (proEtaleAlgebraicUnitSection h R algebraic) scalar scalar_obj multiplication

/-- The specified module inverse image has its canonical algebraic presentation, and
identity scalar extension cancels every normalized ringed tensor comparison.
Source: Stacks Project, Tags 03D2 and 03EL, Section 03EK, and Sites Tag 00YV
(blueprint: lem-pur-inverse-image-scalar-unit-normalization).

Proof:
1. Finite-limit preservation of the set inverse image transports ring and module
operations. Their graph equations follow by applying the binary-product comparison
and checking both projections. Use the specified module functor itself; the canonical
underlying identifications are fixed by their ring and module adjunction-unit formulas.
This uses lem-weil-pbc-left-exact-site-inverse-image-tensor and the specified inverse image.
2. The bilinear universal property (lem-pc-sites-sheaf-tensor-bilinear-universal)
constructs multiplication a on identity scalar extension. Insertion q sends m to 1 tensor m;
balancing gives its linearity. All pure tensors pass through module sheafification.
3. Multiplication after insertion is the identity because 1 acts as the identity.
Insertion after multiplication is the identity on pure tensors by balancing, hence on
the whole sheaf tensor by injectivity of the same universal property.
4. Linearity of I(f) gives naturality of multiplication and insertion. Tensor generation
and sheafification uniqueness give the functor laws of T and its specified morphisms.
5. For any normalized comparison, q_one identifies its q with a inverse. Use the product
of the underlying sheaves of M and N as the test sheaf in its generalized pure equation.
Evaluate at the unit image of (s,t); unit naturality for the two projections and the pure
pairing gives the three original unit sections. Apply a tensor a and cancel a after q
on both factors. This gives the final formula, without assuming target sheaf sections
are globally generated by the original unit images. -/
theorem proEtaleInverseImage_scalarUnit_normalization
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    Nonempty (ProEtaleScalarUnitNormalization h R) := by
  sorry

end AlgebraicGeometry.Scheme
