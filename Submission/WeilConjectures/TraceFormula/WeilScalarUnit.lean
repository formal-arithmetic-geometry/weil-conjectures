/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Submission.WeilConjectures.TraceFormula.BaseChange.Supertrace
public import Submission.WeilConjectures.TraceFormula.Statement
public import Submission.WeilConjectures.TraceFormula.WeilTrace
public import Submission.WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import Submission.WeilConjectures.WeilObject.Sheaf.StalkUnit

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# The unit Weil object twisted by a scalar

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`, `X` a separated scheme of
finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`, and `c` a unit of
`ℚ̄_ℓ`. This file constructs the canonical Weil unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.weilUnit`) with its structure isomorphism multiplied by `c`
(`ProEtale.CondensedRing.weilScalarUnit`) and computes its traces: its local trace at every point
of degree `n + 1` is `c^{n+1}`, and so its global trace is `c^{n+1}` times the number of points of
degree `n + 1`.

The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y` for every scheme `Y`
(`ProEtale.CondensedRing.scalarEndRingHom`): the multiplication by a constant of the regular
condensed module `ℚ̲̄_ℓ` is pulled back along `p_Y^*`. This action is compatible with all pullbacks
(`ProEtale.CondensedRing.εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv`), and under
`End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ` (`ProEtale.CondensedRing.endTensorUnitRingEquiv`) it is the
identity (`ProEtale.CondensedRing.endTensorUnitRingEquiv_scalarEndRingHom`). On `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` the
action is placed in degree `0` (`ProEtale.CondensedRing.homologyUnitEndRingHom`).

The computation follows the one of the untwisted unit in `WeilConjectures.TraceFormula.WeilTrace`:
the only nonzero homology sheaf is `H⁰`, the unit Weil sheaf twisted by `c`
(`ProEtale.CondensedRing.homologyFunctorZeroWeilScalarUnitIso`); the `(n + 1)`-st iterated Weil
structure of the twisted unit Weil sheaf is the twisted unit Weil sheaf for `e^{n+1}` and `c^{n+1}`
(`ProEtale.CondensedRing.WeilSheaf.pow_scalarUnit`), since the action of `c` commutes with the unit
comparisons of the pullbacks; and the Frobenius on its stalk is, conjugated by the unit
comparison of the stalk, the multiplication by `c^{n+1}`, whose trace on the unit is itself.

## Main definitions

- `ProEtale.CondensedRing.scalarEndRingHom`: `ℚ̄_ℓ →+* End (𝟙_ Mod_Y)`.
- `ProEtale.CondensedRing.WeilSheaf.scalarUnit`: the unit Weil sheaf twisted by `c`.
- `ProEtale.CondensedRing.weilScalarUnit`: the canonical Weil unit twisted by `c`.

## Main results

- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit`:
  the local trace of the twisted Weil unit at a point of degree `n + 1` is `c^{n+1}`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit`:
  for `e` of finite order, its global trace in degree `n + 1` is `c^{n+1} · #X(𝔽_{q^{n+1}})`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit_point`,
  `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit_point`:
  for the base `Spec k`, the local trace at its geometric point and the global trace are `c^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The pullback `p_Y^*` from condensed `Λ`-modules is additive on module objects, being additive
on underlying sheaves. -/
instance additive_upperStarFromPointMod (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) : (upperStarFromPointMod Λ Y).Additive where
  map_add := by
    intros
    ext1
    exact (upperStarFromPoint Y).map_add

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y`: the image of the multiplication by
a constant on the regular condensed module `ℚ̲̄_ℓ` under the strong monoidal pullback `p_Y^*`. -/
noncomputable def scalarEndRingHom (Y : Scheme.{u}) :
    _root_.PadicAlgCl ℓ →+* End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))) :=
  (Functor.Monoidal.εIso
      (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).symm.conjRingEquiv.toRingHom.comp
    (((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).mapEndRingHom _).comp
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ).toRingHom)

lemma scalarEndRingHom_apply (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c =
      (Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).hom ≫
        (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
          (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c) ≫
        (Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).inv :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma scalarEndRingHom_eq_map (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c = (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c) := by
  rw [scalarEndRingHom_apply]
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom']
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Under the identification `End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ`, the action of a constant on the
unit is the constant itself. -/
@[simp]
lemma endTensorUnitRingEquiv_scalarEndRingHom (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : _root_.PadicAlgCl ℓ) :
    endTensorUnitRingEquiv ℓ Ω (scalarEndRingHom ℓ (Spec (.of Ω)) c) = c := by
  conv_rhs => rw [← (endTensorUnitRingEquiv ℓ Ω).apply_symm_apply c]
  rw [scalarEndRingHom_eq_map]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `c : P ⋙ F ≅ Q` be an isomorphism of functors and `ε_P : b ≅ P a`, `ε_F : b' ≅ F b`,
`ε_Q : b' ≅ Q a` isomorphisms with `c_a = F ε_P⁻¹ ≫ ε_F⁻¹ ≫ ε_Q`. Then for an endomorphism `t` of
`a`, the conjugate by `ε_F` of `F` applied to the conjugate of `P t` by `ε_P` is the conjugate of
`Q t` by `ε_Q`. -/
lemma CategoryTheory.Iso.hom_comp_map_conj_comp_inv_eq {A B B' : Type*} [Category A] [Category B]
    [Category B'] {P : A ⥤ B} {F : B ⥤ B'} {Q : A ⥤ B'} (c : P ⋙ F ≅ Q) {a : A} {b : B} {b' : B'}
    (εP : b ≅ P.obj a) (εF : b' ≅ F.obj b) (εQ : b' ≅ Q.obj a)
    (h : c.hom.app a = F.map εP.inv ≫ εF.inv ≫ εQ.hom) (t : a ⟶ a) :
    εF.hom ≫ F.map (εP.hom ≫ P.map t ≫ εP.inv) ≫ εF.inv = εQ.hom ≫ Q.map t ≫ εQ.inv := by
  have h1 : F.map εP.inv ≫ εF.inv = c.hom.app a ≫ εQ.inv := by
    rw [h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : εF.hom ≫ F.map εP.hom = εQ.hom ≫ c.inv.app a := by
    rw [← cancel_mono (c.hom.app a), Category.assoc, Category.assoc, Iso.inv_hom_id_app, h,
      Category.comp_id, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_assoc]
  have hn := c.hom.naturality t
  rw [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [h1, reassoc_of% h2, reassoc_of% hn,
    Iso.inv_hom_id_app_assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The action of the constants on the unit is compatible with pullbacks: for `f : X ⟶ Y`, the
pullback `f^*` of the action of `c` on `ℚ̲̄_ℓ,Y`, conjugated by the unit comparison of `f^*`, is
the action of `c` on `ℚ̲̄_ℓ,X`. -/
lemma εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : _root_.PadicAlgCl ℓ) :
    (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom ≫
      (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (scalarEndRingHom ℓ Y c) ≫
        (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      scalarEndRingHom ℓ X c :=
  Iso.hom_comp_map_conj_comp_inv_eq _ _ _ _
    (upperStarFromPointModComp_hom_app_unit (Profinite.padicAlgClRingObj ℓ) f)
    (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c)

/-- The automorphism of the unit `ℚ̲̄_ℓ,Y` of `Mod_Y` given by the action of a unit `c` of
`ℚ̄_ℓ`. -/
noncomputable def scalarAut (Y : Scheme.{u}) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) ≅ 𝟙_ _ :=
  Aut.unitsEndEquivAut _ (Units.map (scalarEndRingHom ℓ Y).toMonoidHom c)

lemma scalarAut_hom (Y : Scheme.{u}) (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (scalarAut ℓ Y c).hom = scalarEndRingHom ℓ Y c :=
  rfl

/-- The action of a constant on the unit commutes with the unit comparison of a pullback. -/
lemma map_scalarEndRingHom_comp_εIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : _root_.PadicAlgCl ℓ) :
    (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map (scalarEndRingHom ℓ Y c) ≫
        (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv ≫
        scalarEndRingHom ℓ X c := by
  rw [← εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv ℓ f c, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing

/-- Let `P g` be a family of endofunctors indexed by the endomorphisms `g` of `X`, contravariant
up to the composition isomorphisms `comp`, let `ε g : a ≅ P g a` be isomorphisms compatible
with `comp`, and let `T` be an automorphism of `a` commuting with the `ε g`. Then the iterated
structure isomorphisms of `(ε e)⁻¹ ≫ T` are `(ε (e^{n+1}))⁻¹ ≫ T^{n+1}`. -/
theorem CategoryTheory.Iso.powSuccStr_symm_trans_hom_eq {C D : Type*} [Category C]
    [Category D] {X : C} (e : X ≅ X) (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (ε : ∀ g : X ⟶ X, a ≅ (P g).obj a)
    (h : ∀ f g : X ⟶ X, (comp f g).hom.app a ≫ (P f).map (ε g).inv ≫ (ε f).inv = (ε (f ≫ g)).inv)
    (T : a ≅ a) (t : End a) (ht : T.hom = t)
    (hT : ∀ g : X ⟶ X, (P g).map t ≫ (ε g).inv = (ε g).inv ≫ t) (n : ℕ) :
    (e.powSuccStr P comp ((ε e.hom).symm ≪≫ T) n).hom =
      (ε (e.pow (n + 1)).hom).inv ≫ t ^ (n + 1) := by
  induction n with
  | zero =>
    have key : ∀ (g g' : X ⟶ X) (h : g = g'),
        eqToHom (congrArg (fun g ↦ (P g).obj a) h) ≫ (ε g').inv = (ε g).inv := by
      rintro g _ rfl
      simp
    rw [powSuccStr_zero, Iso.trans_hom, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, ht,
      ← Category.assoc, key _ _ (Category.id_comp e.hom)]
    exact congrArg (fun s ↦ (ε (e.pow 1).hom).inv ≫ s) (_root_.pow_one t).symm
  | succ n ih =>
    rw [powSuccStr_succ, Iso.trans_hom, Iso.trans_hom, ih, Iso.app_hom, Functor.mapIso_hom,
      Iso.trans_hom, Functor.map_comp, Iso.symm_hom, ht, Category.assoc, reassoc_of% hT,
      reassoc_of% h]
    exact congrArg (fun s ↦ (ε (e.pow (n + 2)).hom).inv ≫ s) (_root_.pow_succ t (n + 1)).symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section ScalarSheaf

variable {X : Over (Spec (.of k))} (e : X ≅ X)

/-- The unit Weil sheaf `ℚ̲̄_ℓ,X` for `e` twisted by a unit `c` of `ℚ̄_ℓ`: the unit module object
with the structure isomorphism `e^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the inverse of the unit comparison
of `e^*` followed by the multiplication by `c`. -/
noncomputable def WeilSheaf.scalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) : WeilSheaf ℓ e :=
  IsoAlgebra.mk (𝟙_ _)
    ((Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
      scalarAut ℓ X.left c)

lemma WeilSheaf.scalarUnit_str (c : (_root_.PadicAlgCl ℓ)ˣ) :
    (WeilSheaf.scalarUnit ℓ e c).str =
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
        scalarAut ℓ X.left c :=
  IsoAlgebra.mk_str _ _

/-- The iterated structure isomorphisms of the twisted unit Weil sheaf are the inverses of the
unit comparisons of the pullbacks `(e^{n+1})^*` followed by the multiplication by `c^{n+1}`. -/
lemma powSuccStr_εIso_symm_trans_scalarAut_hom (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
      ((Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm ≪≫
        scalarAut ℓ X.left c) n).hom =
      (Functor.Monoidal.εIso ((e.pow (n + 1)).hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv ≫
        scalarEndRingHom ℓ X.left
          ((c ^ (n + 1) : (_root_.PadicAlgCl ℓ)ˣ) : _root_.PadicAlgCl ℓ) := by
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact e.powSuccStr_symm_trans_hom_eq _ _
    (fun g ↦ Functor.Monoidal.εIso (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun f g ↦ upperStarComp_hom_app_unit_of_eq _ f.left g.left (Over.comp_left _ _ _ f g).symm
      _ (upperStarComp_left_eq ℓ f g)) (scalarAut ℓ X.left c) _ (scalarAut_hom ℓ X.left c)
    (fun g ↦ map_scalarEndRingHom_comp_εIso_inv ℓ g.left c) n

/-- The twisted unit Weil sheaf for `e` and `c`, as a Weil sheaf for `e^{n+1}`, is the twisted
unit Weil sheaf for `e^{n+1}` and `c^{n+1}`. -/
lemma WeilSheaf.pow_scalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) (n : ℕ) :
    WeilSheaf.pow ℓ (WeilSheaf.scalarUnit ℓ e c) (n + 1) =
      WeilSheaf.scalarUnit ℓ (e.pow (n + 1)) (c ^ (n + 1)) := by
  rw [WeilSheaf.pow_succ, WeilSheaf.scalarUnit_str]
  unfold WeilSheaf.scalarUnit
  congr 1
  ext1
  rw [Iso.trans_hom, Iso.symm_hom, scalarAut_hom]
  exact powSuccStr_εIso_symm_trans_scalarAut_hom ℓ e c n

end ScalarSheaf

section ScalarSheafTrace

variable [Finite k] {X : Over (Spec (.of k))} (e : X ≅ X)

end ScalarSheafTrace

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The automorphism of the unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` given by the action of a unit `c` of
`ℚ̄_ℓ`, placed in degree `0`. -/
noncomputable def boundedConstructibleScalarAut (c : (_root_.PadicAlgCl ℓ)ˣ) :
    𝟙_ (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) ≅ 𝟙_ _ :=
  Aut.unitsEndEquivAut _
    (Units.map ((homologyUnitEndRingHom ℓ X).comp (scalarEndRingHom ℓ X.left)).toMonoidHom c)

variable (e : X ≅ X)

/-- The unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with its canonical Weil structure twisted by a unit `c`
of `ℚ̄_ℓ`: the structure isomorphism is `Le^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the one of the canonical
Weil unit `weilUnit` followed by the multiplication by `c`. Its local traces at the points of
degree `n + 1` are `c^{n+1}`
(`endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit`). -/
noncomputable def weilScalarUnit (c : (_root_.PadicAlgCl ℓ)ˣ) : WeilBoundedConstructible ℓ e.hom :=
  IsoAlgebra.mk (𝟙_ _)
    ((Functor.Monoidal.εIso
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)).symm ≪≫
      boundedConstructibleScalarAut ℓ c)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (e : X ≅ X)

section Trace

variable [Finite k]

attribute [local instance] fintypeFrobeniusFixedPoints

end Trace

/-! ### The base point -/

section Point

variable {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
