/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.Cohomology.UnitCohomologyPullbackLinear
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.Cohomology.InverseImageCoefficientComposition

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The explicitly constructed forward transport intertwines the two structural
pullback maps in a displayed cartesian square.
Source: Stacks Project, Tag 01F7, cohomology-equation-functorial; Tag 02KH,
the untensored comparison map; Mathlib's adjunction identity for pullback of the unit.
(blueprint: lem-pbc-cartesian-unit-cohomology-pullback-comp)

Proof: Put d = h.isoPullback.hom and a = baseChangeFst f. The projection identity
says d followed by a is iota'. The hom of pullbackObjUnitIso a is adjoint to the
structural map from the unit on C to a_* of the unit on the categorical pullback.
The adjunction unit formula therefore identifies baseChangeUnit followed by the
pushforward of that hom with this structural map. Coefficient naturality moves
the hom through the coefficient comparison. The structural unit maps compose:
on each open this is the composition law for the scheme's structure-sheaf maps.
Applying the inverse-image composition comparison identifies the resulting
coefficient map with coeff iota' of the structural unit map. The constant integer
comparison for the composite is the composite of the two constant comparisons:
both are the unique comparison between the left adjoints to constant sections.
Apply functoriality of mapExactFunctor on Ext and associativity of Ext composition
with these two comparisons. This identifies the composite of the canonical
base-change map with the specified forward transport with ordinary structural
pullback along iota', as claimed. Linearity was already proved in the definition
of the forward map; its bijectivity is not used here. The argument works in degree
zero and for empty schemes and zero rings. -/
theorem cartesian_unit_cohomology_pullback_comp
    {k k' : Type u} [CommRing k] [CommRing k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (n : ℕ)
    (x : HOver f (SheafOfModules.unit C.ringCatSheaf) n) :
    unitCohomologyPullbackLinear (baseChangeSnd (S := k') f) f' h.isoPullback.hom
      h.isoPullback_hom_snd
      (baseChangedModule (S := k') f (SheafOfModules.unit C.ringCatSheaf))
      ((pullbackObjUnitIso (baseChangeFst (S := k') f)).hom ≫
        SheafOfModules.unitToPushforwardObjUnit h.isoPullback.hom.toRingCatSheafHom) n
      (H.baseChangeLinear (S := k') f (SheafOfModules.unit C.ringCatSheaf) n x) =
    Sheaf.H.map (coeff ι' (SheafOfModules.unitToPushforwardObjUnit
        ι'.toRingCatSheafHom)) n
      (Sheaf.H.mapFunctor (invImage ι') (constIso ι').symm
        ((SheafOfModules.toSheaf C.ringCatSheaf).obj
          (SheafOfModules.unit C.ringCatSheaf)) n x) := by sorry

end AlgebraicGeometry.Scheme.Modules
