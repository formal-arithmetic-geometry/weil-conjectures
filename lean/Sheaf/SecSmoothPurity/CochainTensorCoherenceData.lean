/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: def-pur-cochain-tensor-coherence-data).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.

The landed side comparison has shared source/target site sizes. The fresh
`SheafOfModules.CochainTensorComparison` namespace generalizes its identical
normalizations to independent site sizes. `ofLanded` retains each of its fields
on the existing range. The published generic signed total maps are reused.
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false

namespace SheafOfModules.CochainTensorComparison


set_option backward.isDefEq.respectTransparency false

universe u

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (blueprint: def-pur-cochain-tensor-coherence-data).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
noncomputable abbrev ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  cochainModulesPreadditive R

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(blueprint: def-pur-cochain-tensor-coherence-data). -/
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
        (changeOfRingsPresheaf c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))

/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data).
Proof: apply the ordinary comparison theorem to the given inverse-image lift.
Its generalized-element normalization gives q and mu. Scalar-extension pure tensors
generate after sheafification, giving uniqueness of q. Bilinear generalized pure tensors
generate the sheaf tensor, giving uniqueness of mu; proof irrelevance handles the laws.
Unlike SheafOfModules.canonicalRingedTensorComparison_existsUnique, the explicit
binders below allow five independent universes uC, vC, uD, vD and u. The published
statement requires C,D : Type u with Category.{u} on both sites. -/
theorem canonicalRingedTensorComparison_existsUnique
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := sorry

/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(blueprint: def-pur-cochain-tensor-coherence-data).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j.
Unlike SheafOfModules.canonicalRingedTensorComparison_unit, the explicit binders
below retain independent uC, vC, uD, vD and coefficient/module universe u. -/
theorem canonicalRingedTensorComparison_unit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := sorry

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC
      (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  exact tensorPullbackTotal L k.mu k.naturality P Q

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :=
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (tensorPullbackTotal_isIso L k.mu k.naturality V am P Q)


end SheafOfModules.CochainTensorComparison

universe s h
namespace SheafOfModules.CochainTensorComparison

/-- The landed side comparison supplies these data whenever its shared sizes apply.
This fieldwise map preserves q, the insertion and pure formulas, and mu exactly.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def ofLanded
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    [EssentiallySmall.{max s h} C] [EssentiallySmall.{max s h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (R : Sheaf JC CommRingCat.{max s h}) (S RI : Sheaf JD CommRingCat.{max s h})
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat RingCat)).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat RingCat)).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (k : CanonicalTensorPullbackOfUniverses.CanonicalRingedTensorComparison.{s, h}
      R S RI uInv I c L hobj) :
    CanonicalRingedTensorComparison.{s, h, s, h, max s h} R S RI uInv I c L hobj where
  q := k.q
  q_one := k.q_one
  mu := k.mu
  naturality := k.naturality
  pure := k.pure

end SheafOfModules.CochainTensorComparison

namespace CategoryTheory.CochainPullback
set_option autoImplicit false

/-- Module sheaves, using Mathlib's category verbatim.
Source: Stacks 03DA (blueprint: def-pur-cochain-tensor-coherence-data). -/
abbrev Modules {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Integer-indexed cochain sheaves; there is no boundedness restriction.
Source: Stacks 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
abbrev Complex {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) := CochainComplex (Modules R) ℤ

/-- Underlying sheaves of sets of module sheaves.
Source: Stacks 03DA (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable abbrev underlying {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) : Modules R ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The inverse-image adjunction and its actual scalar-extension presentation.
The equalities `hobj` and `hmap` specify the pullback functor on objects and maps;
they are presentation data rather than an arbitrary additive functor.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data). -/
structure RingedPullback (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w}) where
  uInv : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  uPush : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : uInv ⊣ uPush
  finiteLimits : PreservesFiniteLimits uInv
  RI : Sheaf K CommRingCat.{w}
  I : SheafOfModules.AlgebraicInverseImage uInv R RI
  coefficient : RI ⟶ S
  L : Modules R ⥤ Modules S
  hobj : ∀ M, L.obj M = SheafOfModules.changeOfRings coefficient (I.modules.obj M)
  hmap : ∀ {M N} (f : M ⟶ N), L.map f = eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom coefficient (I.modules.obj M) (I.modules.map f) ≫
      eqToHom (hobj N).symm
  V : Modules S ⥤ Modules R
  moduleAdj : L ⊣ V
  [additive : L.Additive]

attribute [instance] RingedPullback.additive

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- Every algebraically presented ringed geometric morphism has the module
functor and adjunction used in RingedPullback; these are presentation data.
Source: Stacks 03D2, 03CY and 03D7
(blueprint: def-pur-cochain-tensor-coherence-data).
Proof: transport module operations along the left-exact inverse image. Extend
scalars by the existing sheafified tensor construction, on maps by id tensor h.
Transpose module homomorphisms through the set adjunction and the tensor
universal property, followed by module sheafification. The resulting natural
hom bijection gives the right adjoint and adjunction. Left adjoints between
abelian categories are additive. No flatness or site-universe equality is used. -/
theorem ringedPullbackPresentation_exists
    (uInv : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (uPush : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (RI : Sheaf K CommRingCat.{w})
    (I : SheafOfModules.AlgebraicInverseImage uInv R RI) (c : RI ⟶ S) :
    ∃ (L : Modules R ⥤ Modules S)
      (hobj : ∀ M, L.obj M = SheafOfModules.changeOfRings c (I.modules.obj M)),
      (∀ {M N : Modules R} (b : M ⟶ N), L.map b = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫
          eqToHom (hobj N).symm) ∧
      ∃ V : Modules S ⥤ Modules R, Nonempty (L ⊣ V) ∧ L.Additive := sorry

/-- The normalized module comparison, generalized to independently sized sites.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data). -/
abbrev Comparison (f : RingedPullback R S) :=
  SheafOfModules.CochainTensorComparison.CanonicalRingedTensorComparison
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj

/-- Termwise pullback on all cochain complexes.
Source: Stacks 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable abbrev pull (f : RingedPullback R S) :=
  f.L.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The direct-sum total comparison, with insertion of 1 and contraction as inverse.
Its constituent maps are exactly the normalized module comparison in the dependency.
Source: Stacks 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def comparison (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) : (pull f).obj (P ⊗ Q) ≅ (pull f).obj P ⊗ (pull f).obj Q :=
  (k.totalIso R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.V f.moduleAdj P Q).symm

/-- The unit isomorphism uniquely fixed by the module pure-tensor formula.
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def moduleUnit (f : RingedPullback R S) (k : Comparison f) :
    f.L.obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules S) :=
  Classical.choose (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)

/-- The termwise lift of the normalized unit map, from R[0] to S[0].
Source: Stacks 03EL (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def unit (f : RingedPullback R S) (k : Comparison f) :
    (pull f).obj (𝟙_ (Complex R)) ≅ 𝟙_ (Complex S) :=
  (HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).app (𝟙_ (Modules R)) ≪≫
    (HomologicalComplex.single (Modules S) (.up ℤ) 0).mapIso (moduleUnit f k)

/-- The actual naturality, reassociation, Koszul-symmetry and action-unit equations.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
def IsCoherent (f : RingedPullback R S) (k : Comparison f) : Prop :=
  (∀ (P Q P' Q' : Complex R) (a : P ⟶ P') (b : Q ⟶ Q'),
    (pull f).map (a ⊗ₘ b) ≫ (comparison f k P' Q').hom =
      (comparison f k P Q).hom ≫ ((pull f).map a ⊗ₘ (pull f).map b)) ∧
  (∀ (P Q H : Complex R),
    (pull f).map (α_ P Q H).hom ≫ (comparison f k P (Q ⊗ H)).hom ≫
      (𝟙 _ ⊗ₘ (comparison f k Q H).hom) =
    (comparison f k (P ⊗ Q) H).hom ≫ ((comparison f k P Q).hom ⊗ₘ 𝟙 _) ≫
      (α_ ((pull f).obj P) ((pull f).obj Q) ((pull f).obj H)).hom) ∧
  (∀ (P Q : Complex R),
    (pull f).map (CochainComplex.Monoidal.braiding P Q).hom ≫
      (comparison f k Q P).hom = (comparison f k P Q).hom ≫
      (CochainComplex.Monoidal.braiding ((pull f).obj P) ((pull f).obj Q)).hom) ∧
  (∀ (P : Complex R), (pull f).map (λ_ P).hom =
    (comparison f k (𝟙_ _) P).hom ≫ ((unit f k).hom ⊗ₘ 𝟙 _) ≫
      (λ_ ((pull f).obj P)).hom) ∧
  (∀ (P : Complex R), (pull f).map (ρ_ P).hom =
    (comparison f k P (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (unit f k).hom) ≫
      (ρ_ ((pull f).obj P)).hom)

/-- The adjunction-conjugate module comparison for a composite.
Source: Stacks 0D6D (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def compositionModule
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (right : h.V ≅ g.V ⋙ f.V) : h.L ≅ f.L ⋙ g.L :=
  (conjugateIsoEquiv (f.moduleAdj.comp g.moduleAdj) h.moduleAdj).symm right.symm

/-- Presentation of the actual composite, normalized on inverse-image generators.
The two right-adjoint comparisons give the inverse-image adjunction comparison
and its module analogue. The equation is the scalar-association formula
`1 ⊗ x ↦ 1 ⊗ (1 ⊗ x)` on every generalized element; linearity then gives
`t ⊗ x ↦ t ⊗ (1 ⊗ x)`. It determines the comparison, rather than merely
requiring an arbitrary endomorphism to commute with tensor.
Source: Stacks 0D6D and 03EL
(blueprint: def-pur-cochain-tensor-coherence-data). -/
structure CompositePresentation
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h) where
  rightSets : h.uPush ≅ g.uPush ⋙ f.uPush
  rightModules : h.V ≅ g.V ⋙ f.V
  scalarAssociation : ∀ (M : Modules R) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying R).obj M),
    h.uInv.map x ≫ h.I.moduleUnderlying.inv.app M ≫ kh.q M ≫
        (underlying T).map ((compositionModule f g h rightModules).hom.app M) =
      ((conjugateIsoEquiv (f.adj.comp g.adj) h.adj).symm
        rightSets.symm).hom.app Z ≫
        g.uInv.map (f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ kf.q M) ≫
          g.I.moduleUnderlying.inv.app (f.L.obj M) ≫ kg.q (f.L.obj M)

/-- Termwise lift of the canonical adjunction/scalar-association comparison.
Source: Stacks 0D6D (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def composition
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    {kf : Comparison f} {kg : Comparison g} {kh : Comparison h}
    (a : CompositePresentation f g h kf kg kh) (P : Complex R) :
    (pull h).obj P ≅ (pull g).obj ((pull f).obj P) :=
  (Functor.mapHomologicalComplexCompIso
    (compositionModule f g h a.rightModules).symm (.up ℤ)).symm.app P

/-- The composition equation with the third site and all three comparisons.
Source: Stacks 0D6D and 07A4
(blueprint: def-pur-cochain-tensor-coherence-data). -/
def IsCompatibleWithComposition
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh) : Prop :=
  ∀ (P Q : Complex R),
    (comparison h kh P Q).hom ≫
      ((composition f g h a P).hom ⊗ₘ (composition f g h a Q).hom) =
    (composition f g h a (P ⊗ Q)).hom ≫
      (pull g).map (comparison f kf P Q).hom ≫
        (comparison g kg ((pull f).obj P) ((pull f).obj Q)).hom


/-- The composite geometric morphism admits the normalized module presentation.
Source: Stacks 03D7 and 0D6D
(blueprint: def-pur-cochain-tensor-coherence-data).
Proof: compose the inverse-image adjunctions and transport ring/module operations
along their composite. Apply the module-pullback adjunction to its scalar extension.
The right adjoints compose canonically; conjugate that comparison to obtain a.
Evaluating the two adjunction units gives the displayed scalar-association equation
on every generalized generator. The canonical tensor comparison exists by 03EL. -/
theorem compositePresentation_exists
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (kf : Comparison f) (kg : Comparison g) :
    ∃ (h : RingedPullback R T) (kh : Comparison h),
      Nonempty (CompositePresentation f g h kf kg kh) := sorry

end CategoryTheory.CochainPullback
