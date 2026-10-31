/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Sectionwise laws transferred through injective evaluations

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-zero-laws)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Identity, composition and cocone equations for specified abelian-group maps.
Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, the canonical diagram and cocone.
(blueprint: def-weil-pbc-spectral-limit-cohomology-laws)

Keeping the maps as structure parameters avoids expanding their constructions
separately in the three compatibility assertions. -/
structure CohomologyMapLaws {I : Type u} [Preorder I]
    {M : I → AddCommGrpCat.{u}} {N : AddCommGrpCat.{u}}
    (a : ∀ i j, i ≤ j → (M i ⟶ M j)) (b : ∀ i, M i ⟶ N) : Prop where
  identity : ∀ i, a i i le_rfl = 𝟙 _
  composition : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
    a i j hij ≫ a j k hjk = a i k (hij.trans hjk)
  cocone : ∀ (i j : I) (h : i ≤ j), a i j h ≫ b j = b i

private theorem hom_eq_of_eval {M N : AddCommGrpCat.{u}} {T : Type u}
    (ev : N → T) (hinj : Function.Injective ev) (a b : M ⟶ N)
    (h : ∀ x, HEq (ev (a.hom x)) (ev (b.hom x))) : a = b := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact hinj (eq_of_heq (h x))

private theorem presheaf_app_heq {Y : TopCat.{u}}
    {F G : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F ⟶ G)
    {U V : Opens Y} (e : U = V)
    {s : F.obj (op U)} {t : F.obj (op V)} (hst : HEq s t) :
    HEq ((α.app (op U)).hom s) ((α.app (op V)).hom t) := by
  subst V
  cases hst
  rfl

private theorem coprojection_comp {C : Type*} [Category C] {J : Type*} [Category J]
    (P : J ⥤ C) [HasColimit P] {Q : J → C} (e : ∀ i, P.obj i ≅ Q i)
    {i j : J} (h : i ⟶ j) :
    ((e i).inv ≫ P.map h ≫ (e j).hom) ≫ ((e j).inv ≫ colimit.ι P j) =
      (e i).inv ≫ colimit.ι P i := by
  simp [Category.assoc]

/-- Sectionwise diagram and cocone laws transfer through injective evaluations.
The groups M_i and N are arbitrary. Their specified maps a and b are required to
have the displayed section values under the injective evaluations ev and evN.
No cohomology comparison or colimit assertion is assumed.

Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-zero-laws)

Proof: equality of additive maps follows from injectivity of their evaluations.
For identity use the identity section law of α. For composition, transport the
intermediate evaluation along f_ij inverse-image(top)=top and apply the α cocycle.
For the legs, write δ_i for the inverse of eP_i followed by the coprojection, and
η_i for the inverse-image unit. Apply hP to ev_i(x), then compose with δ_j.
Compatibility of p transports the inverse-image opens. The colimit cocone equation
and cancellation of eP_j identify the resulting coefficient arrow with δ_i.
The two resulting evaluations agree, hence the specified maps agree. -/
theorem spectralLimit_section_laws
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u})
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (X : TopCat.{u}) (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
    (F : ∀ i : I,
      CategoryTheory.Sheaf (Opens.grothendieckTopology (S i)) AddCommGrpCat.{u})
    (α : ∀ (i j : I) (h : i ≤ j),
      F i ⟶ (pushforward AddCommGrpCat.{u} (f i j h)).obj (F j))
    (hαid : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i i le_rfl).hom.app (op U) s) s)
    (hαcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
        ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
          ((α i j hij).hom.app (op U) s)))
    (P : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [HasColimit P]
    (eP : ∀ i : I, P.obj i ≅
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i))
    (hP : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
          (op ((Opens.map (p i)).obj U))
        (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
            (F i)).hom.app (op U) s))
        (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
            (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
              ((α i j h).hom.app (op U) s)))
    (M : I → AddCommGrpCat.{u}) (N : AddCommGrpCat.{u})
    (ev : ∀ i, M i → (F i).obj.obj (op ⊤))
    (evN : N → (colimit P).obj.obj (op ⊤))
    (hinj : ∀ i, Function.Injective (ev i)) (hinjN : Function.Injective evN)
    (a : ∀ i j, i ≤ j → (M i ⟶ M j)) (b : ∀ i, M i ⟶ N)
    (ha0 : ∀ (i j : I) (h : i ≤ j) (x : M i),
      HEq (ev j ((a i j h).hom x)) ((α i j h).hom.app (op ⊤) (ev i x)))
    (hb0 : ∀ (i : I) (x : M i),
      HEq (evN ((b i).hom x))
        ((((eP i).inv ≫ colimit.ι P i).hom.app (op ((Opens.map (p i)).obj ⊤))).hom
          ((((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
              (F i)).hom.app (op ⊤)).hom (ev i x)))) :
    CohomologyMapLaws a b := by
  classical
  constructor
  · intro i
    apply hom_eq_of_eval _ (hinj i)
    intro x
    exact (ha0 i i le_rfl x).trans (hαid i ⊤ (ev i x))
  · intro i j k hij hjk
    apply hom_eq_of_eval _ (hinj k)
    intro x
    simp only [AddCommGrpCat.comp_apply]
    have hi := ha0 i j hij x
    have hj := ha0 j k hjk ((a i j hij).hom x)
    have hk := ha0 i k (hij.trans hjk) x
    exact hj.trans ((presheaf_app_heq (α j k hjk).hom
      (Opens.map_top (f i j hij)).symm hi).trans
        ((hαcomp i j k hij hjk ⊤ _).symm.trans hk.symm))
  · intro i j h
    apply hom_eq_of_eval _ hinjN
    intro x
    simp only [AddCommGrpCat.comp_apply]
    let δ := fun k : I ↦ (eP k).inv ≫ colimit.ι P k
    let η := fun k : I ↦ (sheafAdjunctionContinuous (Opens.map (p k))
      AddCommGrpCat.{u} (Opens.grothendieckTopology (S k))
        (Opens.grothendieckTopology X)).unit.app (F k)
    have hi := ha0 i j h x
    have hj := hb0 j ((a i j h).hom x)
    have hk := hb0 i x
    have hu := presheaf_app_heq (η j).hom (Opens.map_top (f i j h)).symm hi
    have h1 := presheaf_app_heq (δ j).hom
      (congrArg (fun U ↦ (Opens.map (p j)).obj U) (Opens.map_top (f i j h))).symm hu
    have e : (Opens.map (p j)).obj ((Opens.map (f i j h)).obj ⊤) =
        (Opens.map (p i)).obj ⊤ := by
      change (Opens.map (p j ≫ f i j h)).obj ⊤ = _
      rw [hpcomp]
    have h2 := presheaf_app_heq (δ j).hom e (hP i j h ⊤ (ev i x)).symm
    have hd : ((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom) ≫ δ j = δ i := by
      exact coprojection_comp P eP (homOfLE h)
    have h3 := congrArg (fun τ ↦ (τ.hom.app (op ((Opens.map (p i)).obj ⊤))).hom
      ((η i).hom.app (op ⊤) (ev i x))) hd
    exact hj.trans (h1.trans (h2.trans ((heq_of_eq h3).trans hk.symm)))


end TopCat.Sheaf
