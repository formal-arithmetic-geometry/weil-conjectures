/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.Paper.ProperOpenTowerSuccessiveUnitFormula
import Sheaf.Paper.ProperOpenTowerSingleUnitFormula
import WeilConjectures.Algebra.Homology.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Derived-unit resolution calculation in a proper/open tower

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B and 0F7J,
with Sites and Cohomology, Tag 0D6E (blueprint: lem-sfb-proper-open-tower-derived-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
    {X U Xbar Y Ybar Z : Scheme.{u}}
    (j : X ⟶ U) (b : U ⟶ Xbar) (i : Y ⟶ Ybar)
    (q : U ⟶ Y) (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]

/-- The three chosen K-injective resolutions in the proper/open tower.
This packages the existing K-injectivity and quasi-isomorphism notions.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
structure ProperOpenTowerResolution (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u
    + 1} A)) ℤ) where
  I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ
  isKInjective_I : I.IsKInjective
  M : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ
  isKInjective_M : M.IsKInjective
  L : CochainComplex (Sheaf Ybar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ
  isKInjective_L : L.IsKInjective
  u : (((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J) ⟶ I
  quasiIso_u : QuasiIso u
  v : (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (I) ⟶ M
  quasiIso_v : QuasiIso v
  w : (((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((q)_*[ModuleCat.{u +
      1} A]).mapHomologicalComplex (.up ℤ)).obj (I)) ⟶ L
  quasiIso_w : QuasiIso w

attribute [instance] ProperOpenTowerResolution.isKInjective_I
attribute [instance] ProperOpenTowerResolution.isKInjective_M
attribute [instance] ProperOpenTowerResolution.isKInjective_L
attribute [instance] ProperOpenTowerResolution.quasiIso_u
attribute [instance] ProperOpenTowerResolution.quasiIso_v
attribute [instance] ProperOpenTowerResolution.quasiIso_w

variable {A j b i q}

namespace ProperOpenTowerResolution

variable {J J' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (r : ProperOpenTowerResolution A j b i q J)
    (r' : ProperOpenTowerResolution A j b i q J')

/-- The composite augmentation `b_!j_!J → M`.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def augmentation : (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
    ℤ)).obj
    ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J)) ⟶ r.M :=
  (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (r.u) ≫ r.v

/-- The augmentation from `(j ≫ b)_!J`, using the canonical open composition map.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def totalAugmentation : (((j ≫ b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
    (.up ℤ)).obj (J) ⟶ r.M :=
  (NatTrans.mapHomologicalComplex
    (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b).hom (.up ℤ)).app J ≫
      r.augmentation

variable (χ : ((q)_*[ModuleCat.{u + 1} A]) ⋙ ((i)_!open[ModuleCat.{u + 1} A]) ≅
    ((b)_!open[ModuleCat.{u + 1} A]) ⋙ ((p)_*[ModuleCat.{u + 1} A]))

/-- The equation defining the lift `ell` up to homotopy.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
def IsLift (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M)) :
    Prop :=
  Nonempty (Homotopy (r.w ≫ ell) ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app (r.I) ≫
      (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (r.v)))

/-- The first chain map, through the successive resolutions and the lifted comparison.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def firstPath (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
    ℤ)).obj (r.M)) :
  (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((i)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ⟶
      (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((p)_*[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (r.M)) :=
  (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map ((((i)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).map ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map (r.u))) ≫ (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
      (r.w) ≫ (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (ell)

/-- The second chain map, through the section-preserving comparison and single resolution.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def secondPath : (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
    ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((q)_*[ModuleCat.{u +
    1} A]).mapHomologicalComplex (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1}
    A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ⟶ (((s)_*[ModuleCat.{u + 1}
    A]).mapHomologicalComplex (.up ℤ)).obj ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
    (.up ℤ)).obj (r.M)) :=
  (((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app ((((j)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (J))) ≫ (((s)_*[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map (r.augmentation))

/-- A map of the three resolutions over a map of representatives.
Its compatibility equations are homotopies, not degreewise lifting assumptions.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
structure Comparison (f : J ⟶ J') where
  α : r.I ⟶ r'.I
  β : r.M ⟶ r'.M
  γ : r.L ⟶ r'.L
  u_comm : Nonempty (Homotopy (r.u ≫ α) ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map (f) ≫ r'.u))
  v_comm : Nonempty (Homotopy (r.v ≫ β) ((((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map (α) ≫ r'.v))
  w_comm : Nonempty (Homotopy (r.w ≫ γ) ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
      (.up ℤ)).map ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (α)) ≫ r'.w))

end ProperOpenTowerResolution

/-- The ordinary localization unit of direct image at a complex.
This is the existing total-right-derived unit evaluated on its homotopy class;
it imposes no exactness condition on the direct image.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def properOpenTowerUnit {T S : Scheme.{u}} (t : T ⟶ S)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
        DerivedCategory.Q.obj ((((t)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
        (K)) ⟶ R(((t)_*[ModuleCat.{u + 1} A])).obj (DerivedCategory.Q.obj (K)) :=
  ((t)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)

variable {J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (r : ProperOpenTowerResolution A j b i q J)
    (χ : ((q)_*[ModuleCat.{u + 1} A]) ⋙ ((i)_!open[ModuleCat.{u + 1} A]) ≅ ((b)_!open[ModuleCat.{u
        + 1} A]) ⋙ ((p)_*[ModuleCat.{u + 1} A]))
    (Γ : R(((q)_*[ModuleCat.{u + 1} A])) ⋙ D(((i)_!open[ModuleCat.{u + 1} A])) ≅
        D(((b)_!open[ModuleCat.{u + 1} A])) ⋙ R(((p)_*[ModuleCat.{u + 1} A])))

/-- The successive derived-unit route, followed by `Rs_*Γ`, canonical direct-image
composition, and the resolution identification of the common target.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def properOpenTowerSuccessiveUnitPath :
  DerivedCategory.Q.obj ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
      ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((q)_*[ModuleCat.{u
      + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (J))))) ⟶ DerivedCategory.Q.obj ((((s)_*[ModuleCat.{u
      + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((p)_*[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (r.M))) :=
  properOpenTowerUnit (A := A) s ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
      ℤ)).obj ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
      ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ≫
    R(((s)_*[ModuleCat.{u + 1} A])).map (((i)_!open[ModuleCat.{u + 1}
        A]).mapDerivedCategoryFactors.inv.app ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
        (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J))) ≫
      D(((i)_!open[ModuleCat.{u + 1} A])).map (properOpenTowerUnit (A := A) q
          ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J))) ≫
      Γ.hom.app (DerivedCategory.Q.obj ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
          (.up ℤ)).obj (J)))) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom.app
      (D(((b)_!open[ModuleCat.{u + 1} A])).obj (DerivedCategory.Q.obj ((((j)_!open[ModuleCat.{u +
          1} A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ≫
    R(((p ≫ s)_*[ModuleCat.{u + 1} A])).map (((b)_!open[ModuleCat.{u + 1}
        A]).mapDerivedCategoryFactors.hom.app ((((j)_!open[ModuleCat.{u + 1}
        A]).mapHomologicalComplex (.up ℤ)).obj (J)) ≫ DerivedCategory.Q.map (r.augmentation)) ≫
    (((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso (r.M)).hom ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lowerStarComp (ModuleCat.{u + 1} A) p
        s).inv (.up ℤ)).app r.M)

/-- The single derived-unit route for `(p ≫ s)_*`, after the section-preserving
sheaf identification, with the same canonical target resolution identification.
Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sfb-proper-open-tower-derived-unit). -/
noncomputable def properOpenTowerSingleUnitPath :
  DerivedCategory.Q.obj ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
      ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((q)_*[ModuleCat.{u
      + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((j)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (J))))) ⟶ DerivedCategory.Q.obj ((((s)_*[ModuleCat.{u
      + 1} A]).mapHomologicalComplex (.up ℤ)).obj ((((p)_*[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (r.M))) :=
  DerivedCategory.Q.map ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app ((((j)_!open[ModuleCat.{u + 1}
      A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lowerStarComp (ModuleCat.{u + 1} A) p
        s).hom (.up ℤ)).app ((((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj
        ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (J)))) ≫
    DerivedCategory.Q.map ((((p ≫ s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j
        b).inv (.up ℤ)).app J)) ≫
    properOpenTowerUnit (A := A) (p ≫ s) ((((j ≫ b)_!open[ModuleCat.{u + 1}
        A]).mapHomologicalComplex (.up ℤ)).obj (J)) ≫
    R(((p ≫ s)_*[ModuleCat.{u + 1} A])).map (DerivedCategory.Q.map (r.totalAugmentation)) ≫
    (((p ≫ s)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso r.M).hom ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lowerStarComp (ModuleCat.{u + 1} A) p
        s).inv (.up ℤ)).app r.M)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem tower_lift
    {C : Type*} [Category C] [Abelian C]
    {K L T : CochainComplex C ℤ} [L.IsKInjective] [T.IsKInjective]
    (w : K ⟶ L) [QuasiIso w] (c : K ⟶ T) :
    ∃ ell : L ⟶ T, Nonempty (Homotopy (w ≫ ell) c) ∧
      ∀ ell' : L ⟶ T, Nonempty (Homotopy (w ≫ ell') c) →
        Nonempty (Homotopy ell ell') := by
  let R : K.KInjectiveResolution := ⟨L, w, inferInstance, inferInstance⟩
  refine ⟨R.lift c, ⟨R.liftHomotopy c⟩, ?_⟩
  intro ell' h
  exact ⟨R.homotopyOfComp _ _ ((R.liftHomotopy c).trans h.some.symm)⟩

private theorem tower_cancel
    {C : Type*} [Category C] [Abelian C]
    {K L T : CochainComplex C ℤ} [T.IsKInjective]
    (w : K ⟶ L) [QuasiIso w] (f g : L ⟶ T)
    (h : Nonempty (Homotopy (w ≫ f) (w ≫ g))) : Nonempty (Homotopy f g) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.bijective_quotient_map_comp (J := T) w).1
  simpa only [← Functor.map_comp] using HomotopyCategory.eq_of_homotopy _ _ h.some

private theorem tower_map_quasiIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _
    (F.mapHomotopyEquiv e).homotopyEquivalences_hom

private theorem tower_quasiIso_of_homotopy
    {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ}
    (f g : K ⟶ L) (h : Nonempty (Homotopy f g)) [QuasiIso g] : QuasiIso f := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mp
  rw [DerivedCategory.Q_map_eq_of_homotopy C h.some]
  infer_instance

/-- The two resolution paths in a proper/open tower agree up to chain homotopy.
Source: Stacks Project, More on Étale Cohomology, Tags 0F7B and 0F7J, and
Sites and Cohomology, Tag 0D6E (blueprint: lem-sfb-proper-open-tower-derived-unit).

Proof:
1. Exact constant-coefficient inverse image is an additive left adjoint, so the
   right-adjoint K-injective lemma gives K-injectivity of `q_* I` and `p_* M`.
2. The extension-by-zero composition comparison identifies `(b)_!(j)_!J` with
   `(j ≫ b)_!J`; exactness of extension by zero makes `b_!u ≫ v` a quasi-isomorphism
   with K-injective target.
3. Put `c := χ_I ≫ p_*v`.  In the derived category `Qw` is invertible, and the
   Hom-bijection into the K-injective target `p_*M` gives `ell` representing
   `Qc (Qw)⁻¹`, uniquely up to homotopy.
4. Naturality of `χ` gives `i_!q_*u ≫ χ_I = χ_{j_!J} ≫ p_*b_!u`.  Applying `s_*`
   to a homotopy `w ell ≃ c` therefore gives the displayed homotopy of paths.
5. For a total right derived functor, naturality of its unit identifies the unit
   represented by a resolution with the direct image of that resolution map; this
   does not assume direct image preserves quasi-isomorphisms.
6. Applying this unit calculation successively to `q_*` and `s_*`, and using the
   proper/open representative formula for `Γ`, gives the first path.
7. Applying it once to `(s p)_*` and the resolution `b_!u ≫ v`, then using the
   normalized derived direct-image composition isomorphism and `χ`, gives the
   second path.
8. For a map of K-injective representatives, the K-injective Hom-bijection supplies
   comparison maps between the three chosen resolutions; their equations and
   `χ`-naturality make both paths natural.
9. Applying the same comparison to the identity representative shows that all
   comparison maps between two choices of `I`, `M`, and `L` are homotopy equivalences
   and unique over the augmentations.
10. Thus the two paths are independent of all K-injective representatives and
    resolutions, with the source fixed as the localized termwise source.
-/
theorem properOpenTowerDerivedUnit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U Xbar Y Ybar Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian Xbar]
    [IsNoetherian Y] [IsNoetherian Ybar] [IsNoetherian Z]
    (j : X ⟶ U) (b : U ⟶ Xbar) (i : Y ⟶ Ybar)
    (q : U ⟶ Y) (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [IsProper q] [IsProper p] [IsProper s]
    (sq : CommSq b q p i) :
    ∃ (χ : ((q)_*[ModuleCat.{u + 1} A]) ⋙
          ((i)_!open[ModuleCat.{u + 1} A]) ≅
          ((b)_!open[ModuleCat.{u + 1} A]) ⋙
          ((p)_*[ModuleCat.{u + 1} A]))
      (Γ : R((q)_*[ModuleCat.{u + 1} A]) ⋙
          D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((b)_!open[ModuleCat.{u + 1} A]) ⋙
          R((p)_*[ModuleCat.{u + 1} A])),
      (∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        χ.hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar
                (ModuleCat.{u + 1} A) b).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) b p).hom.app F =
          (openImmersionLowerShriekToLowerStar
            (ModuleCat.{u + 1} A) i).app
              ((q)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) q i (b ≫ p)
              sq.w).hom.app F) ∧
      (∀ (I : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) [I.IsKInjective]
          (M : CochainComplex (Sheaf Xbar.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
              [M.IsKInjective]
          (v : (((b)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (I) ⟶ M)
              [QuasiIso v],
        D(((i)_!open[ModuleCat.{u + 1} A])).map ((((q)_*[ModuleCat.{u + 1}
            A]).rightDerivedFunctorObjQIso (I)).hom) ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app ((((q)_*[ModuleCat.{u
              + 1} A]).mapHomologicalComplex (.up ℤ)).obj (I)) ≫ DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app (I)) ≫ DerivedCategory.Q.map
              ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (v)) =
        Γ.hom.app (DerivedCategory.Q.obj (I)) ≫
          R(((p)_*[ModuleCat.{u + 1} A])).map (((b)_!open[ModuleCat.{u + 1}
              A]).mapDerivedCategoryFactors.hom.app (I) ≫ DerivedCategory.Q.map (v)) ≫
              (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso (M)).hom ) ∧
      (∀ (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) [J.IsKInjective]
          (r : ProperOpenTowerResolution A j b i q J),
        CochainComplex.IsKInjective ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
            ℤ)).obj (r.I)) ∧
        CochainComplex.IsKInjective ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
            ℤ)).obj (r.M)) ∧
        CochainComplex.IsKInjectiveResolution Xbar A r.totalAugmentation ∧
        ∃ (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M)),
          r.IsLift p χ ell ∧
          (∀ (ell' : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M)),
            r.IsLift p χ ell' → Nonempty (Homotopy ell ell')) ∧
          Nonempty (Homotopy (r.firstPath p s ell) (r.secondPath p s χ)) ∧
          DerivedCategory.Q.map (r.firstPath p s ell) = properOpenTowerSuccessiveUnitPath p s r Γ ∧
          DerivedCategory.Q.map (r.secondPath p s χ) = properOpenTowerSingleUnitPath p s r χ) ∧
      (∀ (J J' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          [J.IsKInjective] [J'.IsKInjective]
          (r : ProperOpenTowerResolution A j b i q J)
          (r' : ProperOpenTowerResolution A j b i q J') (f : J ⟶ J'),
        Nonempty (r.Comparison r' f) ∧
        (∀ (c d : r.Comparison r' f),
          Nonempty (Homotopy c.α d.α) ∧ Nonempty (Homotopy c.β d.β) ∧
          Nonempty (Homotopy c.γ d.γ)) ∧
        (∀ (c : r.Comparison r' f), QuasiIso f →
          QuasiIso c.α ∧ QuasiIso c.β ∧ QuasiIso c.γ ∧
          QuasiIso ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f))))) ∧
          QuasiIso ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (c.β))))) ∧
      (∀ (J J' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          [J.IsKInjective] [J'.IsKInjective]
          (r : ProperOpenTowerResolution A j b i q J)
          (r' : ProperOpenTowerResolution A j b i q J')
          (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M))
          (ell' : r'.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r'.M))
          (f : J ⟶ J') (c : r.Comparison r' f),
        r.IsLift p χ ell → r'.IsLift p χ ell' →
        Nonempty (Homotopy (ell ≫ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
            (c.β)) (c.γ ≫ ell')) ∧
        Nonempty (Homotopy (r.firstPath p s ell ≫ (((s)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map (c.β)))
          ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f)))) ≫
              r'.firstPath p s ell')) ∧
        Nonempty (Homotopy (r.secondPath p s χ ≫ (((s)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map (c.β)))
          ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f)))) ≫
              r'.secondPath p s χ))) ∧
      (∀ (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) [J.IsKInjective]
          (r r' : ProperOpenTowerResolution A j b i q J)
          (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M))
          (ell' : r'.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r'.M)),
        r.IsLift p χ ell → r'.IsLift p χ ell' →
        ∃ (c : r.Comparison r' (𝟙 J)),
          QuasiIso c.α ∧ QuasiIso c.β ∧ QuasiIso c.γ ∧
          IsIso (DerivedCategory.Q.map ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up
              ℤ)).map ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (c.β)))) ∧
          DerivedCategory.Q.map (r.firstPath p s ell) ≫ DerivedCategory.Q.map
              ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (c.β))) =
            DerivedCategory.Q.map (r'.firstPath p s ell') ∧
          DerivedCategory.Q.map (r.secondPath p s χ) ≫ DerivedCategory.Q.map ((((s)_*[ModuleCat.{u
              + 1} A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1}
              A]).mapHomologicalComplex (.up ℤ)).map (c.β))) =
            DerivedCategory.Q.map (r'.secondPath p s χ)) := by
  obtain ⟨θ, Γ, hsec, hrep, -⟩ := unboundedProperOpenInterchange A
  let χ := θ b q p i sq
  let G := Γ b q p i sq
  specialize hsec b q p i sq
  specialize hrep b q p i sq
  let jf := ((j)_!open[ModuleCat.{u + 1} A])
  let bf := ((b)_!open[ModuleCat.{u + 1} A])
  let iqf := ((q)_*[ModuleCat.{u + 1} A]) ⋙ ((i)_!open[ModuleCat.{u + 1} A])
  let pf := ((p)_*[ModuleCat.{u + 1} A])
  let sf := ((s)_*[ModuleCat.{u + 1} A])
  let jc := jf.mapHomologicalComplex (.up ℤ)
  let bc := bf.mapHomologicalComplex (.up ℤ)
  let iqc := ((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ) ⋙
    ((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)
  let pc := pf.mapHomologicalComplex (.up ℤ)
  let sc := sf.mapHomologicalComplex (.up ℤ)
  have hcomp : ∀ (J J' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          [J.IsKInjective] [J'.IsKInjective]
          (r : ProperOpenTowerResolution A j b i q J)
          (r' : ProperOpenTowerResolution A j b i q J') (f : J ⟶ J'),
        Nonempty (r.Comparison r' f) ∧
        (∀ (c d : r.Comparison r' f),
          Nonempty (Homotopy c.α d.α) ∧ Nonempty (Homotopy c.β d.β) ∧
          Nonempty (Homotopy c.γ d.γ)) ∧
        (∀ (c : r.Comparison r' f), QuasiIso f →
          QuasiIso c.α ∧ QuasiIso c.β ∧ QuasiIso c.γ ∧
          QuasiIso ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f))))) ∧
          QuasiIso ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (c.β)))) := by
    intro J J' hJ hJ' r r' f
    obtain ⟨α, hα, _⟩ := tower_lift r.u (jc.map f ≫ r'.u)
    obtain ⟨β, hβ, _⟩ := tower_lift r.v (bc.map α ≫ r'.v)
    obtain ⟨γ, hγ, _⟩ := tower_lift r.w (iqc.map α ≫ r'.w)
    refine ⟨⟨⟨α, β, γ, hα, hβ, hγ⟩⟩, ?_, ?_⟩
    · intro c d
      have ha : Nonempty (Homotopy c.α d.α) :=
        tower_cancel r.u _ _ ⟨c.u_comm.some.trans d.u_comm.some.symm⟩
      have hb : Nonempty (Homotopy c.β d.β) := tower_cancel r.v _ _
        ⟨c.v_comm.some.trans (((bf.mapHomotopy ha.some).compRight r'.v).trans
          d.v_comm.some.symm)⟩
      have hg : Nonempty (Homotopy c.γ d.γ) := tower_cancel r.w _ _
        ⟨c.w_comm.some.trans (((iqf.mapHomotopy ha.some).compRight r'.w).trans
          d.w_comm.some.symm)⟩
      exact ⟨ha, hb, hg⟩
    · intro c hf
      have :=  hf
      have hα : QuasiIso c.α := by
        have :=  tower_map_quasiIso jf f
        have :=  tower_quasiIso_of_homotopy _ _ c.u_comm
        exact quasiIso_of_comp_left r.u c.α
      have :=  hα
      have hβ : QuasiIso c.β := by
        have :=  tower_map_quasiIso bf c.α
        have :=  tower_quasiIso_of_homotopy _ _ c.v_comm
        exact quasiIso_of_comp_left r.v c.β
      have hγ : QuasiIso c.γ := by
        have : QuasiIso ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex
            (.up ℤ)).map ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex
            (.up ℤ)).map c.α)) := tower_map_quasiIso iqf c.α
        have :=  tower_quasiIso_of_homotopy _ _ c.w_comm
        exact quasiIso_of_comp_left r.w c.γ
      have :=  hβ
      exact ⟨hα, hβ, hγ, tower_map_quasiIso (jf ⋙ iqf ⋙ sf) f,
        tower_map_quasiIso (pf ⋙ sf) c.β⟩
  have hnatural : ∀ (J J' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
          [J.IsKInjective] [J'.IsKInjective]
          (r : ProperOpenTowerResolution A j b i q J)
          (r' : ProperOpenTowerResolution A j b i q J')
          (ell : r.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r.M))
          (ell' : r'.L ⟶ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).obj (r'.M))
          (f : J ⟶ J') (c : r.Comparison r' f),
        r.IsLift p χ ell → r'.IsLift p χ ell' →
        Nonempty (Homotopy (ell ≫ (((p)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
            (c.β)) (c.γ ≫ ell')) ∧
        Nonempty (Homotopy (r.firstPath p s ell ≫ (((s)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map (c.β)))
          ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f)))) ≫
              r'.firstPath p s ell')) ∧
        Nonempty (Homotopy (r.secondPath p s χ ≫ (((s)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map ((((p)_*[ModuleCat.{u + 1}
            A]).mapHomologicalComplex (.up ℤ)).map (c.β)))
          ((((s)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((i)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((q)_*[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map
              ((((j)_!open[ModuleCat.{u + 1} A]).mapHomologicalComplex (.up ℤ)).map (f)))) ≫
              r'.secondPath p s χ)) := by
    intro J J' hJ hJ' r r' ell ell' f c hell hell'
    let H := HomotopyCategory.quotient
      (Sheaf Ybar.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)
    let τ := NatTrans.mapHomologicalComplex χ.hom (.up ℤ)
    have hn : iqc.map c.α ≫ τ.app r'.I = τ.app r.I ≫ pc.map (bc.map c.α) := by
      ext n : 1
      exact χ.hom.naturality (c.α.f n)
    have hl := HomotopyCategory.eq_of_homotopy _ _ hell.some
    have hl' := HomotopyCategory.eq_of_homotopy _ _ hell'.some
    have hv := HomotopyCategory.eq_of_homotopy _ _ (pf.mapHomotopy c.v_comm.some)
    have hw := HomotopyCategory.eq_of_homotopy _ _ c.w_comm.some
    have hn' := congrArg H.map hn
    change H.map (r.w ≫ ell) = H.map (τ.app r.I ≫ pc.map r.v) at hl
    change H.map (r'.w ≫ ell') = H.map (τ.app r'.I ≫ pc.map r'.v) at hl'
    change H.map (pc.map (r.v ≫ c.β)) =
      H.map (pc.map (bc.map c.α ≫ r'.v)) at hv
    change H.map (r.w ≫ c.γ) = H.map (iqc.map c.α ≫ r'.w) at hw
    simp only [Functor.map_comp] at hl hl' hv hw hn'
    have he : Nonempty (Homotopy (ell ≫ pc.map c.β) (c.γ ≫ ell')) := by
      apply Nonempty.intro
      apply HomotopyCategory.homotopyOfEq
      apply (CochainComplex.IsKInjective.bijective_quotient_map_comp
        (J := pc.obj r'.M) r.w).1
      change H.map r.w ≫ H.map (ell ≫ pc.map c.β) =
        H.map r.w ≫ H.map (c.γ ≫ ell')
      simp only [Functor.map_comp, ← Category.assoc]
      rw [hl, Category.assoc, hv, ← Category.assoc, ← hn', Category.assoc,
        ← hl', ← Category.assoc, ← hw]
    have hu := HomotopyCategory.eq_of_homotopy _ _
      ((iqf ⋙ sf).mapHomotopy c.u_comm.some)
    have hwS := HomotopyCategory.eq_of_homotopy _ _ (sf.mapHomotopy c.w_comm.some)
    have heS := HomotopyCategory.eq_of_homotopy _ _ (sf.mapHomotopy he.some)
    let HS := HomotopyCategory.quotient
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)
    have hp : Nonempty (Homotopy (r.firstPath p s ell ≫ sc.map (pc.map c.β))
        (sc.map (iqc.map (jc.map f)) ≫ r'.firstPath p s ell')) := by
      apply Nonempty.intro
      apply HomotopyCategory.homotopyOfEq
      change HS.map (sc.map (iqc.map r.u) ≫ sc.map r.w ≫ sc.map ell ≫
        sc.map (pc.map c.β)) = HS.map (sc.map (iqc.map (jc.map f)) ≫
        sc.map (iqc.map r'.u) ≫ sc.map r'.w ≫ sc.map ell')
      change HS.map (sc.map (iqc.map (r.u ≫ c.α))) =
        HS.map (sc.map (iqc.map (jc.map f ≫ r'.u))) at hu
      change HS.map (sc.map (r.w ≫ c.γ)) =
        HS.map (sc.map (iqc.map c.α ≫ r'.w)) at hwS
      change HS.map (sc.map (ell ≫ pc.map c.β)) =
        HS.map (sc.map (c.γ ≫ ell')) at heS
      simp only [Functor.map_comp] at hu hwS heS ⊢
      rw [heS, ← Category.assoc (HS.map (sc.map r.w)), hwS,
        Category.assoc, ← Category.assoc (HS.map (sc.map (iqc.map r.u))), hu]
      rw [Category.assoc]
    refine ⟨he, hp, ?_⟩
    have path (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (t : ProperOpenTowerResolution A j b i q K)
        (e : t.L ⟶ pc.obj t.M) (h : t.IsLift p χ e) :
        Nonempty (Homotopy (t.firstPath p s e) (t.secondPath p s χ)) := by
      refine ⟨((sf.mapHomotopy h.some).compLeft (sc.map (iqc.map t.u))).trans ?_⟩
      apply Homotopy.ofEq
      change sc.map (iqc.map t.u) ≫ sc.map _ = sc.map _ ≫ sc.map _
      rw [← sc.map_comp, ← sc.map_comp]
      congr 1
      have hn : iqc.map t.u ≫ τ.app t.I = τ.app (jc.obj K) ≫ pc.map (bc.map t.u) := by
        ext n : 1
        exact χ.hom.naturality (t.u.f n)
      dsimp only [ProperOpenTowerResolution.augmentation]
      simp only [Functor.map_comp, ← Category.assoc]
      rw [hn]
    exact ⟨(((path J r ell hell).some.symm.compRight _).trans hp.some).trans
      ((path J' r' ell' hell').some.compLeft _)⟩
  refine ⟨χ, G, hsec, hrep, ?_, ?_, ?_, ?_⟩
  · intro J hJ r
    refine ⟨inferInstance, inferInstance, ⟨?_, inferInstance⟩, ?_⟩
    · have : IsIso ((NatTrans.mapHomologicalComplex
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b).hom (.up ℤ)).app J) :=
        ((NatIso.mapHomologicalComplex
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b) (.up ℤ)).app J).isIso_hom
      have : QuasiIso (bc.map r.u) := inferInstance
      dsimp only [ProperOpenTowerResolution.totalAugmentation,
        ProperOpenTowerResolution.augmentation]
      infer_instance
    · obtain ⟨ell, hell, huniq⟩ := tower_lift r.w
        ((NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app r.I ≫ pc.map r.v)
      refine ⟨ell, hell, huniq, ?_, ?_, ?_⟩
      · apply Nonempty.intro
        refine ((sf.mapHomotopy hell.some).compLeft (sc.map (iqc.map r.u))).trans ?_
        apply Homotopy.ofEq
        dsimp [ProperOpenTowerResolution.secondPath, ProperOpenTowerResolution.augmentation]
        change sc.map (iqc.map r.u) ≫ sc.map _ = sc.map _ ≫ sc.map _
        rw [← sc.map_comp, ← sc.map_comp]
        congr 1
        have hn : iqc.map r.u ≫
            (NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app r.I =
            (NatTrans.mapHomologicalComplex χ.hom (.up ℤ)).app (jc.obj J) ≫
              pc.map (bc.map r.u) := by
          ext n : 1
          exact χ.hom.naturality (r.u.f n)
        simp only [Functor.map_comp, ← Category.assoc]
        rw [hn]
      · exact properOpenTowerSuccessiveUnitFormula j b i q p s J r.I r.M r.u r.v χ
          r.L r.w ell G hell (hrep r.I r.M r.v)
      · exact properOpenTowerSingleUnitFormula j b i q p s J r.I r.M r.u r.v χ
  · exact hcomp
  · exact hnatural
  · intro J hJ r r' ell ell' hell hell'
    obtain ⟨⟨c⟩, _, hc⟩ := hcomp J J r r' (𝟙 J)
    obtain ⟨ha, hb, hg, _, ht⟩ := hc c inferInstance
    have := ht
    obtain ⟨_, hp, hq⟩ := hnatural J J r r' ell ell' (𝟙 J) c hell hell'
    have hid : sc.map (iqc.map (jc.map (𝟙 J))) = 𝟙 _ := by
      simp only [CategoryTheory.Functor.map_id]
    change Nonempty (Homotopy (_ ≫ _) (sc.map (iqc.map (jc.map (𝟙 J))) ≫ _)) at hp hq
    rw [hid, Category.id_comp] at hp hq
    refine ⟨c, ha, hb, hg, inferInstance, ?_, ?_⟩
    · simpa only [← Functor.map_comp] using
        DerivedCategory.Q_map_eq_of_homotopy _ hp.some
    · simpa only [← Functor.map_comp] using
        DerivedCategory.Q_map_eq_of_homotopy _ hq.some

end AlgebraicGeometry.Etale
