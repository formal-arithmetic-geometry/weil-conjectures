/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Inverse image along an object of the small pro-etale site

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; pro-etale functoriality, Tag 09A5
(blueprint: lem-sfb-proetale-object-inverse-image-restriction).

The comparison data below spell out the canonical presheaf coprojections and
sheafification unit. The theorem applies to an arbitrary site object, with no
monomorphism or finiteness hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The distinguished pair `(U → X, (id, str))` in the inverse-image index.
The chosen pullback puts the variable factor first. Its arrow is the unit of
composition left adjoint to base change, hence is exactly the pair of the identity
and the structure map, rather than an arbitrary arrow to the fibre product.
Source: Stacks, Tags 03CE and 00VC
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
noncomputable def proEtaleObjectInverseImageIndexPoint {X : Scheme.{u}} (W : X.ProEt)
    (U : W.left.ProEt) : proEtaleInverseImageIndex W.hom U :=
  StructuredArrow.mk
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit.app U)

/-- Clause (1)'s canonical comparison data for a specified category of values.
`presheafIso` is restriction to the object followed by the presheaf inverse image;
its components are the distinguished coprojections, expressed using the Kan unit.
The final equation identifies the inverse of `sheafIso` with those coprojections
followed by the actual sheafification unit. Both isomorphisms are natural in the
sheaf, and their components are presheaf/sheaf morphisms, hence natural in site objects.
This structure only packages the assertions; it does not choose any comparison.
Source: Stacks, Tags 03CE, 00VC and 00WH
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
structure ProEtaleObjectRestrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] where
  presheafIso :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan
  coprojection : ∀ (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt),
    (presheafIso.hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op
  sheafification_isIso : ∀ G : Sheaf (ProEt.topology X) D,
    IsIso (toSheafify (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj))
  sheafIso : proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D ≅
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop
  sheafIso_inv : ∀ G : Sheaf (ProEt.topology X) D,
    (sheafIso.inv.app G).hom = presheafIso.hom.app G ≫
      toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)

/-- Restriction of constant-coefficient modules through the constant-ring localization
isomorphism `e : A_W ≅ A_X|_W`. This is the existing sectionwise pushforward of
module sheaves along composition; its scalar action uses `e.hom` and its underlying
abelian presheaf is exactly `U ↦ M(U → W → X)`.
Source: Stacks, Tags 00XZ, 0H7J and 03D2
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
noncomputable abbrev proEtaleObjectModuleRestriction {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A)) :=
  letI : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  SheafOfModules.pushforward.{u + 1} (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing W.left A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Inverse image along an object is slice restriction, including the canonical
presheaf comparison, the sheafification unit, the particular coefficient map, and
module pullback. The commutative-ring comparison retains the ring structure needed
for coefficients; `RingCat` also includes noncommutative ring sheaves.

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; proetale.tex, Tag 09A5
(blueprint: lem-sfb-proetale-object-inverse-image-restriction).

Proof plan:
1. Weakly-etale localization identifies W's site with the slice, with the same
   coverings (lem-weil-proetale-weakly-etale-localization). Restriction is a sheaf
   by def-pur-localized-ringed-site. No monomorphism is needed.
2. At U the distinguished index point has arrow (id, str). An arrow from it to
   (V, phi) is forced to be the projection of phi to V. The pullback universal
   property proves its existence and uniqueness (def-pc-fibre-product and
   def-weil-proetale-inverse-image). Thus the point is initial.
3. The restriction maps G(V) → G(U) form a cocone over the opposite index.
   Its induced map is inverse to the distinguished coprojection: one composite
   uses the identity projection, the other is checked on every coprojection.
   This works in rings as well, without computing their colimits on underlying sets.
4. For b : U' → U the index restriction replaces phi by phi b. The projected
   arrow is therefore composed with b. This proves naturality in U; naturality
   of G → H proves naturality in G. Ring and abelian operations are preserved.
5. The presheaf inverse image is already a sheaf. Extend its identity through
   def-weil-pbc-sheafification to invert the canonical sheafification unit;
   uniqueness proves the other inverse identity. This gives the specified sheaf iso.
6. Write e : A_W → A_X|_W for the constant-section-preserving localization iso.
   The specified c_A is the adjoint of rho_A (def-weil-proetale-inverse-image).
   On the distinguished coprojection it is A_W(phi) rho_A, by the Kan unit in
   lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction. It preserves constant
   sections, as does e. Uniqueness of extension from the constant presheaf gives
   c_A e = id after the comparison, hence c_A is the inverse of e.
7. Apply the distinguished-coprojection comparison to the action map and the
   inverse-image product comparison. The image of (a,m) is the image of am,
   so the identified module action is precisely the restricted action.
8. Using def-pur-sheaf-tensor-product, collapse the sectionwise scalar-extension
   tensor by m tensor a ↦ e(a)m. The inverse is m ↦ m tensor 1; balancing proves
   both identities and linearity. The maps commute with restrictions and module
   homomorphisms. The universal property of def-weil-presheaf-modules-sheafification
   extends this iso to module sheaves. Its underlying abelian sheaf is therefore
   the restricted underlying abelian sheaf, as claimed. -/
theorem proEtaleObjectInverseImageRestriction (X : Scheme.{u}) (W : X.ProEt)
    (A : Type u) [CommRing A] :
    (∀ U : W.left.ProEt,
      Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint W U))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W (Type (u + 1))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W AddCommGrpCat.{u + 1}) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W RingCat.{u + 1}) ∧
    ∃ (comparison : ProEtaleObjectRestrictionComparison W CommRingCat.{u + 1})
      (e : proEtaleConstantRing W.left A ≅
        (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
          W.hom W.prop).obj (proEtaleConstantRing X A)),
      (∀ U : W.left.ProEt,
        (toSheafify (ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app
                (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) ∧
      proEtaleCoefficientInverseImageMap W.hom A ≫ e.hom =
        comparison.sheafIso.hom.app (proEtaleConstantRing X A) ∧
      ∃ rho : ∀ M : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)),
          proEtaleConstantModulePullback W.hom A M ≅
            (proEtaleObjectModuleRestriction W A e).obj M,
        ∀ (M N : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))
          (a : M ⟶ N),
          proEtaleConstantModulePullbackMap W.hom A a ≫ (rho N).hom =
            (rho M).hom ≫ (proEtaleObjectModuleRestriction W A e).map a := by
  sorry

end AlgebraicGeometry.Scheme
