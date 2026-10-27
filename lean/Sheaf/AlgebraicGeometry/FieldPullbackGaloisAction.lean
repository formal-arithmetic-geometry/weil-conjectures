/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q82
-/
module

public import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Invariants
import Sheaf.FieldTheory.SeparableClosureRestrictionImage
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.FieldTheory.GaloisAutomorphismExtension
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInjective
import WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage

/-! # Field pullback and restriction of the Galois action

Source: Stacks Project, Etale Cohomology, Tags 03Q1 (3), 03QW, 04JQ and 04JM
(blueprint: lem-per-field-pullback-galois-action).

The equivalences and their stalk comparisons are supplied as the witnesses of
`Scheme.abelianSheaves_equiv_discreteGModules`. Their lift-change normalization is
recorded by `fieldStalkActionCompatible`; thus the comparison is independent of a
presentation of the canonical equivalences. Global sections are evaluated at any
terminal etale neighbourhood, including its base change to the larger field.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace Rep

/-- Restriction of discrete continuous integral representations: the group and
coefficient maps are unchanged, and `h` acts as `r h`.
Source: Stacks Project, Tags 03QW and 04JQ
(blueprint: lem-per-field-pullback-galois-action). -/
noncomputable def restrictDiscrete
    {G : Type u} {H : Type v} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (r : H →* G)
    (h : ∀ M : DiscreteContinuousRep.{0, u, w} ℤ G,
      ∀ m : M.obj.V, IsOpen {g : H | (res r M.obj).ρ g m = m}) :
    DiscreteContinuousRep.{0, u, w} ℤ G ⥤ DiscreteContinuousRep.{0, v, w} ℤ H :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ resFunctor r)
    h

end Rep

namespace AlgebraicGeometry.Scheme

/-- The canonical lift-change normalization of an abelian Galois stalk equivalence.
This is the abelian action clause of `abelianSheaves_equiv_discreteGModules`, with
the geometric point written explicitly to permit the literal composite `p_L ≫ u`.
Source: Stacks Project, Tags 03QW and 04JQ
(blueprint: lem-per-field-pullback-galois-action). -/
def fieldStalkActionCompatible
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Spec (.of K))
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅ (pointSmallEtale p).sheafFiber) :
    Prop :=
  ∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
    (algebraMap Ks Ω).comp g.toRingHom = τ.toRingHom.comp (algebraMap Ks Ω) →
    ∀ (U : (Spec (.of K)).Etale) (x x' : (pointSmallEtale p).fiber.obj U),
    x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
    ∀ z : F.obj.obj (op U),
      (i.hom.app F) ((E.functor.obj F).obj.ρ g
        ((i.inv.app F) ((pointSmallEtale p).toPresheafFiber U x F.obj z))) =
      (pointSmallEtale p).toPresheafFiber U x' F.obj z

/-- The actual terminal germ map gives the additive identification with invariants. -/
private theorem terminal_germ_equiv
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ Spec (.of K))
    (hp : p = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅ (pointSmallEtale p).sheafFiber)
    (hi : fieldStalkActionCompatible K Ks Ω p E i)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (T : (Spec (.of K)).Etale) (hT : IsTerminal T)
    (x : (pointSmallEtale p).fiber.obj T) :
    ∃ a : F.obj.obj (op T) ≃+ (@Representation.invariants ℤ (Gal(Ks/K)) (E.functor.obj F).obj.V _ _
      (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ),
      ∀ z, (a z).val = i.inv.app F ((pointSmallEtale p).toPresheafFiber T x F.obj z) := by
  subst p
  let j := (i.inv.app F).hom.comp
    ((pointSmallEtale _).toPresheafFiber T x F.obj).hom
  have hj := etaleGlobalSections_galoisInvariants_injective K Ks Ω T hT E i x F
  have hmem := etaleGlobalSections_galoisInvariants_image K Ks Ω T hT E i hi x F
  let j' : F.obj.obj (op T) →+ (@Representation.invariants ℤ (Gal(Ks/K)) (E.functor.obj F).obj.V _ _
      (E.functor.obj F).obj.hV1 (E.functor.obj F).obj.hV2 (E.functor.obj F).obj.ρ) :=
    { toFun := fun z => ⟨j z, (hmem (j z)).2 ⟨z, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun z w => Subtype.ext (map_add j z w) }
  refine ⟨AddEquiv.ofBijective j' ⟨?_, ?_⟩, fun _ => rfl⟩
  · intro a b hab
    exact hj (congrArg Subtype.val hab)
  · intro v
    obtain ⟨z, hz⟩ := (hmem v.val).1 v.property
    exact ⟨z, Subtype.ext hz⟩

/-- An equivariant isomorphism restricts to an additive isomorphism on invariants. -/
private def invariants_iso
    {G : Type u} [Group G] {X Y : Rep.{w} ℤ G} (q : X ≅ Y) :
    (@Representation.invariants ℤ G X.V _ _ X.hV1 X.hV2 X.ρ) ≃+
      (@Representation.invariants ℤ G Y.V _ _ Y.hV1 Y.hV2 Y.ρ) where
  toFun v := ⟨q.hom.hom v, fun g => by
    rw [← Rep.hom_comm_apply, v.property g]⟩
  invFun v := ⟨q.inv.hom v, fun g => by
    rw [← Rep.hom_comm_apply, v.property g]⟩
  left_inv v := Subtype.ext (Rep.inv_hom_apply X Y q (v : X.V))
  right_inv v := Subtype.ext (Rep.hom_inv_apply X Y q (v : Y.V))
  map_add' v w := Subtype.ext (map_add q.hom.hom (v : X.V) (w : X.V))

/-- Normalize the specified canonical comparison, using the general-site argument of
`inverseImage_stalk_germ` (Stacks Tag 03Q1 (3)). Its existential statement alone
would not identify this particular isomorphism. -/
private theorem canonical_pullback_germ
    {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Etale)
    (x : (pointSmallEtale (y ≫ f)).fiber.obj U) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
        (op U) ≫
      (pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso f y).inv.app U x)
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G).obj ≫
      (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f y).hom.app G =
      (pointSmallEtale (y ≫ f)).toPresheafFiber U x G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv
    ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f y).app G)).1
  simp only [Etale.upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (pointSmallEtale y).sheafFiber.map _ =
    (pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) AddCommGrpCat.{u + 1}
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl

set_option maxHeartbeats 800000 in
-- The comparison traverses several bundled forgetful functors and their stored module instances.
/-- Field-extension pullback is restriction of the absolute Galois action under
the canonical abelian stalk equivalences. The first equation identifies its
underlying additive map with the canonical stalk-pullback isomorphism. The final
clause identifies global sections by their terminal germs with the two invariant
subgroups of the same module, and sends every section's invariant element to itself.

The hypotheses `hK` and `hL` specify the canonical equivalences, exactly as in the
action clause of `abelianSheaves_equiv_discreteGModules`; they are not extra
conditions on the fields or sheaves. Likewise `hres` specifies the restriction map.
All field maps are compatible through the displayed scalar towers. Omega need
not be algebraic over either field, and restriction need not be surjective.

Source: Stacks Project, Etale Cohomology, Tags 03Q1 (3), 03QW, 04JQ and 04JM
(blueprint: lem-per-field-pullback-galois-action).

Proof:
1. Restriction is continuous by `lem-per-galois-restriction-image`. Open stabilizers
pull back to open stabilizers, giving `Rep.restrictDiscrete` with unchanged maps.
2. Compute the unit-on-germs formula for the actual canonical stalk comparison,
using the three general-site factors of `Etale.upperStarCompSheafFiberIso`.
It sends a unit-pulled germ to the original germ. By bijectivity and the
existence of germ representatives, such germs exhaust the pullback stalk.
3. For each tau in G_L use `lem-exc-galois-automorphism-extension` to extend tau
to an L-automorphism of Omega. Its restriction to K^s is r(tau). The action
formula supplied by `hK` and `hL` changes both pointed lifts by this same
automorphism. The germ formula in step 2 proves equivariance on all germs.
4. The additive equivariant isomorphisms and their inverses assemble, by their
naturality, into the stated natural isomorphism of discrete modules.
5. `aux-etale-global-sections-injective` and `aux-etale-global-sections-image`
identify terminal sections over K and L with the respective invariant groups
by the actual germ maps. Transport the L identification through the equivariant
comparison. The unit germ formula in step 2 identifies the two underlying
elements. Consequently the map on invariants is precisely m maps to m. -/
theorem fieldPullback_galoisAction
    (K L Ks Ls Ω : Type u) [Field K] [Field L] [Field Ks] [Field Ls] [Field Ω]
    [Algebra K L] [Algebra K Ks] [IsSepClosure K Ks]
    [Algebra L Ls] [IsSepClosure L Ls] [Algebra Ks Ls] [Algebra K Ls]
    [Algebra Ls Ω] [Algebra K Ω] [Algebra L Ω] [Algebra Ks Ω]
    [IsScalarTower K L Ls] [IsScalarTower K Ks Ls]
    [IsScalarTower K Ls Ω] [IsScalarTower L Ls Ω] [IsScalarTower Ks Ls Ω]
    [IsAlgClosed Ω]
    (r : Gal(Ls/L) →* Gal(Ks/K))
    (hres : ∀ τ : Gal(Ls/L), (algebraMap Ks Ls).comp (r τ).toRingHom =
      τ.toRingHom.comp (algebraMap Ks Ls))
    (EK : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (EL : Sheaf (Spec (.of L)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ls/L)))
    (iK : EK.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber)
    (iL : EL.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ls/L)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ls/L)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))).sheafFiber)
    (hK : fieldStalkActionCompatible K Ks Ω
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L))) EK iK)
    (hL : fieldStalkActionCompatible L Ls Ω
      (Spec.map (CommRingCat.ofHom (algebraMap L Ω))) EL iL) :
    ∃ h : ∀ M : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)),
      ∀ m : M.obj.V, IsOpen {τ : Gal(Ls/L) | (Rep.res r M.obj).ρ τ m = m},
    ∃ e : Etale.upperStar AddCommGrpCat.{u + 1}
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙ EL.functor ≅
      EK.functor ⋙ Rep.restrictDiscrete r h,
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (m : (EL.functor.obj ((Etale.upperStar AddCommGrpCat.{u + 1}
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj F)).obj.V),
        (iK.hom.app F) ((e.hom.app F).hom.hom m) =
          ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))
            (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))).hom.app F)
          ((iL.hom.app _) m)) ∧
      (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
        (T : (Spec (.of K)).Etale) (_hT : IsTerminal T)
        (x : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K L)))).fiber.obj T),
        ∃ (a : F.obj.obj (op T) ≃+
          (@Representation.invariants ℤ (Gal(Ks/K)) (EK.functor.obj F).obj.V _ _
            (EK.functor.obj F).obj.hV1 (EK.functor.obj F).obj.hV2
            (EK.functor.obj F).obj.ρ))
          (b : ((Etale.upperStar AddCommGrpCat.{u + 1}
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj F).obj.obj
            (op ((Spec.map (CommRingCat.ofHom (algebraMap K L))).Etale.obj T)) ≃+
          (@Representation.invariants ℤ (Gal(Ls/L)) (EK.functor.obj F).obj.V _ _
            (EK.functor.obj F).obj.hV1 (EK.functor.obj F).obj.hV2
            ((EK.functor.obj F).obj.ρ.comp r))),
          (∀ z : F.obj.obj (op T), (a z).val = (iK.inv.app F)
            ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap K L)))).toPresheafFiber T x F.obj z)) ∧
          (∀ z, (b z).val = (e.hom.app F).hom.hom ((iL.inv.app _)
            ((pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))).toPresheafFiber
              ((Spec.map (CommRingCat.ofHom (algebraMap K L))).Etale.obj T)
              ((pointSmallEtaleFiberEtaleIso
                (Spec.map (CommRingCat.ofHom (algebraMap K L)))
                (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))).inv.app T x)
              ((Etale.upperStar AddCommGrpCat.{u + 1}
                (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj F).obj z))) ∧
          (∀ z : F.obj.obj (op T),
            (b ((((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))).unit.app F).hom.app
                (op T)) z)).val = (a z).val)) := by
  classical
  have : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K Ls Ω, IsScalarTower.algebraMap_eq K L Ls,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq L Ls Ω])
  have : IsScalarTower K Ks Ω := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K Ls Ω, IsScalarTower.algebraMap_eq K Ks Ls,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Ks Ls Ω])
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let p := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
  let P := Etale.upperStar AddCommGrpCat.{u + 1} f
  let c := Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f p
  have hc (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (U : (Spec (.of K)).Etale) (x : (pointSmallEtale (p ≫ f)).fiber.obj U)
      (z : F.obj.obj (op U)) :
      c.hom.app F ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U)
        ((pointSmallEtaleFiberEtaleIso f p).inv.app U x) (P.obj F).obj
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app
          (op U) z)) = (pointSmallEtale (p ≫ f)).toPresheafFiber U x F.obj z :=
    congrArg (fun q => q z) (canonical_pullback_germ f p F U x)
  have hr : r = IntermediateField.restrictRestrictAlgEquivMapHom K Ks L Ls := by
    ext τ a
    apply (algebraMap Ks Ls).injective
    exact (RingHom.congr_fun (hres τ) a).trans
      (AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgAut (Gal(Ls/L)) K Ls τ) Ks a).symm
  have hcont : Continuous r := by
    rw [hr]
    exact (IntermediateField.separableClosure_restriction_image K L Ks Ls).1
  let h : ∀ M : Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)),
      ∀ m : M.obj.V, IsOpen {τ : Gal(Ls/L) | (Rep.res r M.obj).ρ τ m = m} :=
    fun M m => (M.property m).preimage hcont
  let d := (Functor.isoWhiskerLeft P iL) ≪≫ c ≪≫ iK.symm
  have hd (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (τ : Gal(Ls/L)) (m : (EL.functor.obj (P.obj F)).obj.V) :
      d.hom.app F ((EL.functor.obj (P.obj F)).obj.ρ τ m) =
        (EK.functor.obj F).obj.ρ (r τ) (d.hom.app F m) := by
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    obtain ⟨U, x, z, hz⟩ := (pointSmallEtale (p ≫ f)).toPresheafFiber_jointly_surjective
      (c.hom.app F (iL.hom.app (P.obj F) m))
    let y := (pointSmallEtaleFiberEtaleIso f p).inv.app U x
    let zL : (P.obj F).obj.obj (op (f.Etale.obj U)) :=
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F
        ).hom.app (op U) z
    have hm : m = iL.inv.app (P.obj F)
        ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL) := by
      apply (ConcreteCategory.bijective_of_isIso (iL.hom.app (P.obj F))).1
      apply (ConcreteCategory.bijective_of_isIso (c.hom.app F)).1
      rw [← ConcreteCategory.comp_apply, iL.inv_hom_id_app]
      exact hz.symm.trans (hc F U x z).symm
    obtain ⟨t, ht⟩ := exists_algEquiv_extending_separableClosure L Ls Ω τ
    let tK : Ω ≃ₐ[K] Ω := t.restrictScalars K
    have htK : (algebraMap Ks Ω).comp (r τ).toRingHom =
        tK.toRingHom.comp (algebraMap Ks Ω) := by
      ext a
      change algebraMap Ks Ω (r τ a) = t (algebraMap Ks Ω a)
      calc
        algebraMap Ks Ω (r τ a) =
            algebraMap Ls Ω (algebraMap Ks Ls (r τ a)) :=
          IsScalarTower.algebraMap_apply Ks Ls Ω _
        _ = algebraMap Ls Ω (τ (algebraMap Ks Ls a)) :=
          congrArg (algebraMap Ls Ω) (RingHom.congr_fun (hres τ) a)
        _ = t (algebraMap Ls Ω (algebraMap Ks Ls a)) := RingHom.congr_fun ht _
        _ = t (algebraMap Ks Ω a) := by rw [← IsScalarTower.algebraMap_apply Ks Ls Ω]
    have hbase : Spec.map (CommRingCat.ofHom t.toRingHom) ≫ p = p := by
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact t.commutes a
    let x' : (pointSmallEtale (p ≫ f)).fiber.obj U :=
      Over.homMk (Spec.map (CommRingCat.ofHom t.toRingHom) ≫ x.left) (by
        change (Spec.map (CommRingCat.ofHom t.toRingHom) ≫ x.left) ≫ U.hom = p ≫ f
        rw [Category.assoc, show x.left ≫ U.hom = p ≫ f from Over.w x]
        change Spec.map (CommRingCat.ofHom t.toRingHom) ≫ (p ≫ f) = p ≫ f
        rw [← Category.assoc, hbase])
    let y' := (pointSmallEtaleFiberEtaleIso f p).inv.app U x'
    have hy : y'.left = Spec.map (CommRingCat.ofHom t.toRingHom) ≫ y.left := by
      apply pullback.hom_ext
      · simp only [y', y, Category.assoc, pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
        rfl
      · simp only [y', y, Category.assoc, pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
        exact hbase.symm
    have hactL := hL (P.obj F) τ t ht (f.Etale.obj U) y y' hy zL
    have hactK := hK F (r τ) tK htK U x x' rfl z
    apply (ConcreteCategory.bijective_of_isIso (iK.hom.app F)).1
    change iK.hom.app F (d.hom.app F _) = iK.hom.app F (_)
    have hdval (n : (EL.functor.obj (P.obj F)).obj.V) :
        iK.hom.app F (d.hom.app F n) = c.hom.app F (iL.hom.app (P.obj F) n) := by
      change iK.hom.app F (iK.inv.app F (c.hom.app F (iL.hom.app (P.obj F) n))) = _
      rw [← ConcreteCategory.comp_apply, iK.inv_hom_id_app]
      rfl
    rw [hdval, hm, hactL, hc]
    have hdg : d.hom.app F
        (iL.inv.app (P.obj F)
          ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL)) =
        iK.inv.app F ((pointSmallEtale (p ≫ f)).toPresheafFiber U x F.obj z) := by
      change iK.inv.app F (c.hom.app F (iL.hom.app (P.obj F)
        (iL.inv.app (P.obj F)
          ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL)))) = _
      rw [show iL.hom.app (P.obj F) (iL.inv.app (P.obj F)
        ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL)) =
        (pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL from
          congrArg (fun q => q
            ((pointSmallEtale p).toPresheafFiber (f.Etale.obj U) y (P.obj F).obj zL))
            (iL.inv_hom_id_app (P.obj F))]
      exact congrArg (iK.inv.app F) (hc F U x z)
    rw [hdg]
    exact hactK.symm
  let e : P ⋙ EL.functor ≅ EK.functor ⋙ Rep.restrictDiscrete r h :=
    NatIso.ofComponents (fun F => ObjectProperty.isoMk _
      (@Rep.mkIso ℤ (Gal(Ls/L)) _ _
        (EL.functor.obj (P.obj F)).obj.V (EK.functor.obj F).obj.V
        (EL.functor.obj (P.obj F)).obj.hV1 (EK.functor.obj F).obj.hV1
        (EL.functor.obj (P.obj F)).obj.hV2 (EK.functor.obj F).obj.hV2
        (EL.functor.obj (P.obj F)).obj.ρ ((EK.functor.obj F).obj.ρ.comp r)
        (@Representation.Equiv.mk ℤ (Gal(Ls/L))
          (EL.functor.obj (P.obj F)).obj.V (EK.functor.obj F).obj.V _ _
          _ _ (EL.functor.obj (P.obj F)).obj.hV2 (EK.functor.obj F).obj.hV2
          (EL.functor.obj (P.obj F)).obj.ρ ((EK.functor.obj F).obj.ρ.comp r)
          ((d.app F).addCommGroupIsoToAddEquiv.toIntLinearEquiv
            (modM := (EL.functor.obj (P.obj F)).obj.hV2)
            (modM₂ := (EK.functor.obj F).obj.hV2)) (fun τ => by
              apply DFunLike.ext
              intro m
              exact hd F τ m)))) (by
      intro F G q
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply DFunLike.ext
      intro m
      exact congrArg (fun a => a m) (d.hom.naturality q))
  refine ⟨h, e, ?_, ?_⟩
  · intro F m
    change iK.hom.app F (d.hom.app F m) = c.hom.app F (iL.hom.app (P.obj F) m)
    change iK.hom.app F (iK.inv.app F (c.hom.app F (iL.hom.app (P.obj F) m))) = _
    rw [← ConcreteCategory.comp_apply, iK.inv_hom_id_app]
    rfl
  · intro F T hT x
    have hpK : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Spec.map_comp]
      congr 1
      ext a
      exact (IsScalarTower.algebraMap_apply K L Ω a).symm
    obtain ⟨a, ha⟩ := terminal_germ_equiv K Ks Ω (p ≫ f) hpK EK iK hK F T hT x
    have hTL : IsTerminal (f.Etale.obj T) := hT.isTerminalObj f.Etale T
    let y := (pointSmallEtaleFiberEtaleIso f p).inv.app T x
    obtain ⟨bL, hbL⟩ := terminal_germ_equiv L Ls Ω p rfl EL iL hL
      (P.obj F) (f.Etale.obj T) hTL y
    let b := bL.trans (invariants_iso ((ObjectProperty.ι _).mapIso (e.app F)))
    refine ⟨a, b, ha, ?_, ?_⟩
    · intro z
      change (e.hom.app F).hom.hom (bL z).val = _
      rw [hbL]
    · intro z
      change (e.hom.app F).hom.hom
        (bL (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F
          ).hom.app (op T) z)).val = (a z).val
      rw [hbL, ha]
      change d.hom.app F (iL.inv.app (P.obj F)
        ((pointSmallEtale p).toPresheafFiber (f.Etale.obj T) y (P.obj F).obj
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F
            ).hom.app (op T) z))) = _
      change iK.inv.app F (c.hom.app F (iL.hom.app (P.obj F)
        (iL.inv.app (P.obj F)
          ((pointSmallEtale p).toPresheafFiber (f.Etale.obj T) y (P.obj F).obj
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F
              ).hom.app (op T) z))))) = _
      have hcancel (v : ((pointSmallEtale p).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (P.obj F)) :
          iL.hom.app (P.obj F) (iL.inv.app (P.obj F) v) = v :=
        congrArg (fun q => q v) (iL.inv_hom_id_app (P.obj F))
      rw [hcancel]
      exact congrArg (iK.inv.app F) (hc F T x z)

end AlgebraicGeometry.Scheme
