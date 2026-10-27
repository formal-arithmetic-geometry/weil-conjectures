/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Finite limits and coherence for internal group restriction

Source: current blueprint, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-written internal-action infrastructure; Stacks 0037, 01D3, 03D7, 03EK, 03CY.
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
-/

@[expose] public section

set_option autoImplicit false
-- Preserve the existing theorem binders, including the specified site witnesses.
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]
  (J : Precoverage C) (hJ : J.IsSiteForCoverings)
  {K L H : Cᵒᵖ ⥤ GrpCat.{u}}
  (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
  (hL : Presheaf.IsSheaf J.toGrothendieck (L ⋙ forget GrpCat.{u}))
  (hH : Presheaf.IsSheaf J.toGrothendieck (H ⋙ forget GrpCat.{u}))

/-- A group-sheaf map is an internal monoid map.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof: its components preserve the group unit and multiplication. -/
theorem restrictionGroupMap_isMonHom (θ : L ⟶ K) :
    IsMonHom (M := groupSheaf J L hL) (N := groupSheaf J K hK)
      (⟨Functor.whiskerRight θ (forget GrpCat.{u})⟩ : groupSheaf J L hL ⟶ groupSheaf J K hK) := by
  constructor
  · ext U x
    exact (θ.app U).hom.map_one
  · ext U x
    exact (θ.app U).hom.map_mul x.1 x.2

/-- Restrict the genuine internal action using Mathlib's existing comap.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence). -/
def restrictSetActions (θ : L ⟶ K) : SetActions J K hK ⥤ SetActions J L hL :=
  @Mod.comap _ _ _ _ _ _ _ _ _ _
    (⟨Functor.whiskerRight θ (forget GrpCat.{u})⟩ : groupSheaf J L hL ⟶ groupSheaf J K hK)
    (restrictionGroupMap_isMonHom J hK hL θ)

/-- Maps between trivial actions are equivariant.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof: both action maps are the second projection, which commutes with every map. -/
theorem trivialSetActions_map {X Y : Sheaf J.toGrothendieck (Type u)} (f : X ⟶ Y) :
    @IsModHom _ _ _ _ _ _ (groupSheaf J K hK) _ X Y
      (ModObj.trivialAction (groupSheaf J K hK) X)
      (ModObj.trivialAction (groupSheaf J K hK) Y) f := by
  let : ModObj (groupSheaf J K hK) X := ModObj.trivialAction _ X
  let : ModObj (groupSheaf J K hK) Y := ModObj.trivialAction _ Y
  exact ⟨(CartesianMonoidalCategory.whiskerLeft_snd _ f).symm⟩

/-- Trivial inflation keeps the sheaf and every map, with the trivial action.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence). -/
def trivialSetActions : Sheaf J.toGrothendieck (Type u) ⥤ SetActions J K hK where
  obj X := Mod.trivialAction (Mon.mk (groupSheaf J K hK)) X
  map f := { hom := f, isModHom := trivialSetActions_map J hK f }

include hJ in
/-- Forgetting an internal action creates every finite limit; restriction and trivial
inflation preserve finite limits. Creation includes the terminal object, componentwise
products and the restricted action on equalizers.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (steps 1--3): a limit consists of tuples satisfying all diagram-arrow equations.
Gluing is coordinatewise, including the empty tuple. Act coordinatewise; equivariance
preserves the equations. Projections force this action uniquely. Restriction substitutes
theta in each coordinate, and trivial inflation makes every coordinate action trivial. -/
theorem internalRestriction_finiteLimits (θ : L ⟶ K) :
    (∀ (D : Type) [SmallCategory D] [FinCategory D],
      Nonempty (CreatesLimitsOfShape D (Mod.forget (groupSheaf J K hK) :
        SetActions J K hK ⥤ Sheaf J.toGrothendieck (Type u)))) ∧
    PreservesFiniteLimits (restrictSetActions J hK hL θ) ∧
    PreservesFiniteLimits (trivialSetActions J hK) := by
  refine ⟨fun D _ _ ↦ ⟨inferInstance⟩, ⟨fun D _ _ ↦ ?_⟩, ⟨fun D _ _ ↦ ?_⟩⟩
  · have : PreservesLimitsOfShape D
        (restrictSetActions J hK hL θ ⋙ Mod.forget (groupSheaf J L hL)) :=
      inferInstanceAs (PreservesLimitsOfShape D (Mod.forget (groupSheaf J K hK)))
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (restrictSetActions J hK hL θ) (Mod.forget (groupSheaf J L hL))
  · have : PreservesLimitsOfShape D
        (trivialSetActions J hK ⋙ Mod.forget (groupSheaf J K hK)) :=
      inferInstanceAs (PreservesLimitsOfShape D (𝟭 (Sheaf J.toGrothendieck (Type u))))
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (trivialSetActions J hK) (Mod.forget (groupSheaf J K hK))

private theorem mod_eqToHom_hom {A : Sheaf J.toGrothendieck (Type u)} [MonObj A]
    {M N : Mod (Sheaf J.toGrothendieck (Type u)) A} (h : M = N) :
    (eqToHom h).hom = eqToHom (congrArg Mod.X h) := by
  subst h
  rfl

include hJ in
/-- Restriction leaves underlying sheaves and maps unchanged, substitutes theta in the
section action, and has literal identity, composition and trivial-inflation identities.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 4): evaluate on a section: successive substitution is theta(psi(h));
identity substitution changes nothing, and every substituted trivial action is trivial.
All maps keep their original components. Proof irrelevance identifies the action laws. -/
theorem internalRestriction_identities (θ : L ⟶ K) (ψ : H ⟶ L) :
    (restrictSetActions J hK hL θ ⋙ Mod.forget (groupSheaf J L hL) =
      Mod.forget (groupSheaf J K hK)) ∧
    (∀ (X : SetActions J K hK) (U : Cᵒᵖ) (a : L.obj U) (x : X.X.obj.obj U),
      setAction J L hL ((restrictSetActions J hK hL θ).obj X) U a x =
        setAction J K hK X U (θ.app U a) x) ∧
    restrictSetActions J hK hK (𝟙 K) = 𝟭 _ ∧
    restrictSetActions J hK hL θ ⋙ restrictSetActions J hL hH ψ =
      restrictSetActions J hK hH (ψ ≫ θ) ∧
    trivialSetActions J hK ⋙ restrictSetActions J hK hL θ = trivialSetActions J hL := by
  refine ⟨rfl, fun X U a x ↦ rfl, ?_, ?_, ?_⟩
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · dsimp [restrictSetActions, Mod.comap]
      congr 1
    · apply Mod.hom_ext
      simp only [Mod.comp_hom', mod_eqToHom_hom]
      simp [restrictSetActions, Mod.comap]
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · dsimp [restrictSetActions, Mod.comap]
    · apply Mod.hom_ext
      simp only [Mod.comp_hom', mod_eqToHom_hom]
      simp [restrictSetActions, Mod.comap]
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · dsimp [restrictSetActions, trivialSetActions, Mod.comap]
      congr 1
    · apply Mod.hom_ext
      simp only [Mod.comp_hom', mod_eqToHom_hom]
      simp [restrictSetActions, trivialSetActions, Mod.comap]

private theorem setAction_naturality (X : SetActions J K hK) {U V : Cᵒᵖ}
    (f : U ⟶ V) (k : K.obj U) (x : X.X.obj.obj U) :
    X.X.obj.map f (setAction J K hK X U k x) =
      setAction J K hK X V (K.map f k) (X.X.obj.map f x) := by
  have h := congrArg
    (fun t : (K.obj U × X.X.obj.obj U) ⟶ X.X.obj.obj V ↦ t (k, x))
    ((ModObj.smul (M := groupSheaf J K hK) (X := X.X)).hom.naturality f)
  change setAction J K hK X V (K.map f k) (X.X.obj.map f x) =
    X.X.obj.map f (setAction J K hK X U k x) at h
  exact h.symm

private theorem setAction_map {X Y : SetActions J K hK} (f : X ⟶ Y)
    (U : Cᵒᵖ) (k : K.obj U) (x : X.X.obj.obj U) :
    setAction J K hK Y U k (f.hom.hom.app U x) =
      f.hom.hom.app U (setAction J K hK X U k x) := by
  have h := congrArg
    (fun t : groupSheaf J K hK ⊗ X.X ⟶ Y.X ↦ t.hom.app U (k, x)) (Mod.act_hom f)
  change f.hom.hom.app U (setAction J K hK X U k x) =
    setAction J K hK Y U k (f.hom.hom.app U x) at h
  exact h.symm

private def fixedSubfunctor (X : SetActions J K hK) : Subfunctor X.X.obj where
  obj U := {x | ∀ (V : Cᵒᵖ) (f : U ⟶ V) (k : K.obj V),
    setAction J K hK X V k (X.X.obj.map f x) = X.X.obj.map f x}
  map := by
    intro U V f x hx W g k
    simpa only [Functor.map_comp_apply] using hx W (f ≫ g) k

private theorem fixedSubfunctor_isSheaf (X : SetActions J K hK) :
    Presheaf.IsSheaf J.toGrothendieck (fixedSubfunctor J hK X).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hX := (isSheaf_iff_isSheaf_of_type _ _).1 X.X.property
  apply (Subfunctor.isSheaf_iff _ hX).2
  intro U x hx V f k
  apply (hX _ (J.toGrothendieck.pullback_stable f.unop hx)).isSeparatedFor.ext
  intro W g hg
  rw [setAction_naturality]
  have h := hg (op W) (𝟙 (op W)) (K.map g.op k)
  simpa only [Functor.map_comp_apply, Functor.map_id_apply, op_comp, Quiver.Hom.op_unop]
    using h

private abbrev fixedSheaf (X : SetActions J K hK) : Sheaf J.toGrothendieck (Type u) :=
  ⟨(fixedSubfunctor J hK X).toFunctor, fixedSubfunctor_isSheaf J hK X⟩

private def fixedMap {X Y : SetActions J K hK} (f : X ⟶ Y) :
    fixedSheaf J hK X ⟶ fixedSheaf J hK Y where
  hom := {
    app U := ↾fun x ↦ ⟨f.hom.hom.app U x.val, by
      intro V g k
      have n := ConcreteCategory.congr_hom (f.hom.hom.naturality g) x.val
      change f.hom.hom.app V (X.X.obj.map g x.val) =
        Y.X.obj.map g (f.hom.hom.app U x.val) at n
      change setAction J K hK Y V k (Y.X.obj.map g (f.hom.hom.app U x.val)) =
        Y.X.obj.map g (f.hom.hom.app U x.val)
      rw [← n, setAction_map, x.property V g k]⟩
    naturality := by
      intro U V g
      ext x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x.val }

private def fixedFunctor : SetActions J K hK ⥤ Sheaf J.toGrothendieck (Type u) where
  obj := fixedSheaf J hK
  map := fixedMap J hK
  map_id X := by ext U x; rfl
  map_comp f g := by ext U x; rfl

private def toFixed {A : Sheaf J.toGrothendieck (Type u)} {X : SetActions J K hK}
    (f : (trivialSetActions J hK).obj A ⟶ X) : A ⟶ fixedSheaf J hK X where
  hom := {
    app U := ↾fun x ↦ ⟨f.hom.hom.app U x, by
      intro V g k
      have n := ConcreteCategory.congr_hom (f.hom.hom.naturality g) x
      change f.hom.hom.app V (A.obj.map g x) =
        X.X.obj.map g (f.hom.hom.app U x) at n
      change setAction J K hK X V k (X.X.obj.map g (f.hom.hom.app U x)) =
        X.X.obj.map g (f.hom.hom.app U x)
      rw [← n, setAction_map]
      rfl⟩
    naturality := by
      intro U V g
      ext x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x }

private def fromFixed {A : Sheaf J.toGrothendieck (Type u)} {X : SetActions J K hK}
    (f : A ⟶ fixedSheaf J hK X) : (trivialSetActions J hK).obj A ⟶ X :=
  Mod.homMk
    ⟨{ app U := ↾fun x ↦ (f.hom.app U x).val
       naturality := by
         intro U V g
         ext x
         exact congrArg Subtype.val (ConcreteCategory.congr_hom (f.hom.naturality g) x) }⟩
    (by
      ext U p
      change (f.hom.app U p.2).val =
        setAction J K hK X U p.1 (f.hom.app U p.2).val
      simpa only [Functor.map_id_apply] using
        ((f.hom.app U p.2).property U (𝟙 U) p.1).symm)

private def fixedHomEquiv (A : Sheaf J.toGrothendieck (Type u))
    (X : SetActions J K hK) :
    ((trivialSetActions J hK).obj A ⟶ X) ≃ (A ⟶ (fixedFunctor J hK).obj X) where
  toFun := toFixed J hK
  invFun := fromFixed J hK
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

include hJ in
/-- The right adjoint is the actual fixed subsheaf, characterized by its inclusion.
The condition tests every further arrow, not merely the group sections over U.
Source: paragraph (3); Stacks 0037
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (steps 5--6): restriction preserves universally fixed sections. Glue them in X;
on every further V, pull back the cover and test every k in K(V). Separatedness proves
fixedness of the glued section. An equivariant map out of a trivial action factors
uniquely through these subsets; conversely the inclusion makes every such map
 equivariant. These inverse natural Hom bijections give the adjunction by 0037.
Its counit is the inclusion, so the right adjoint is determined as a subobject. -/
theorem internalRestriction_fixedAdjoint :
    ∃ (F : SetActions J K hK ⥤ Sheaf J.toGrothendieck (Type u))
      (i : F ⟶ Mod.forget (groupSheaf J K hK))
      (a : trivialSetActions J hK ⊣ F),
      (∀ (X : SetActions J K hK) (U : Cᵒᵖ),
        Function.Injective ((i.app X).hom.app U)) ∧
      (∀ (X : SetActions J K hK) (U : Cᵒᵖ) (x : X.X.obj.obj U),
        (∃ y, (i.app X).hom.app U y = x) ↔
          ∀ (V : Cᵒᵖ) (f : U ⟶ V) (k : K.obj V),
            setAction J K hK X V k (X.X.obj.map f x) = X.X.obj.map f x) ∧
      (∀ X : SetActions J K hK, (a.counit.app X).hom = i.app X) := by
  let i : fixedFunctor J hK ⟶ Mod.forget (groupSheaf J K hK) := {
    app X := ⟨(fixedSubfunctor J hK X).ι⟩ }
  let a : trivialSetActions J hK ⊣ fixedFunctor J hK := Adjunction.mkOfHomEquiv {
    homEquiv := fixedHomEquiv J hK
    homEquiv_naturality_left_symm := by intros; ext U x; rfl
    homEquiv_naturality_right := by intros; ext U x; rfl }
  refine ⟨fixedFunctor J hK, i, a, fun X U ↦ Subtype.val_injective, ?_, ?_⟩
  · intro X U x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  · intro X
    ext U x
    rfl

include hJ in
/-- Actions of the terminal group are ordinary sheaves, and restriction along K to 1
is trivial inflation under that equivalence.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 4): the unit action law forces the unique group element to act identically.
Forgetting and restoring this action are inverse, on objects and maps. -/
theorem internalRestriction_terminal :
    ∃ e : Mod (Sheaf J.toGrothendieck (Type u))
        (𝟙_ (Sheaf J.toGrothendieck (Type u))) ≌ Sheaf J.toGrothendieck (Type u),
      e.functor = Mod.forget (𝟙_ (Sheaf J.toGrothendieck (Type u))) ∧
      e.inverse ⋙ Mod.comap (CartesianMonoidalCategory.toUnit (groupSheaf J K hK)) =
        trivialSetActions J hK := by
  let T : Sheaf J.toGrothendieck (Type u) ⥤
      Mod (Sheaf J.toGrothendieck (Type u)) (𝟙_ (Sheaf J.toGrothendieck (Type u))) := {
    obj X := Mod.trivialAction (Mon.mk (𝟙_ (Sheaf J.toGrothendieck (Type u)))) X
    map f := Mod.homMk f (CartesianMonoidalCategory.whiskerLeft_snd _ f).symm }
  have action (X : Mod (Sheaf J.toGrothendieck (Type u)) (𝟙_ (Sheaf J.toGrothendieck (Type u)))) :
      @Mod.act _ _ _ (𝟙_ (Sheaf J.toGrothendieck (Type u))) _ X.X X.mod =
        CartesianMonoidalCategory.snd
          (𝟙_ (Sheaf J.toGrothendieck (Type u))) X.X := by
    let := X.mod
    have h := ModObj.one_smul (M := 𝟙_ (Sheaf J.toGrothendieck (Type u))) X.X
    change (𝟙 _ ▷ X.X) ≫
      @Mod.act _ _ _ (𝟙_ (Sheaf J.toGrothendieck (Type u))) _ X.X X.mod =
      (λ_ X.X).hom at h
    calc
      _ = (λ_ X.X).hom := by
        simpa only [id_whiskerRight, Category.id_comp] using h
      _ = _ := CartesianMonoidalCategory.leftUnitor_hom _
  let e : Mod (Sheaf J.toGrothendieck (Type u)) (𝟙_ (Sheaf J.toGrothendieck (Type u))) ≌
      Sheaf J.toGrothendieck (Type u) := {
    functor := Mod.forget _
    inverse := T
    unitIso := NatIso.ofComponents
      (fun X ↦ Mod.isoMk (Iso.refl _) (by
        change @Mod.act _ _ _ (𝟙_ (Sheaf J.toGrothendieck (Type u))) _ X.X X.mod ≫
          𝟙 X.X =
          (𝟙_ (Sheaf J.toGrothendieck (Type u)) ◁ 𝟙 X.X) ≫
            CartesianMonoidalCategory.snd (𝟙_ (Sheaf J.toGrothendieck (Type u))) X.X
        simpa only [whiskerLeft_id, Category.id_comp, Category.comp_id] using action X))
      (fun f ↦ Mod.hom_ext _ _ rfl)
    counitIso := Iso.refl _ }
  refine ⟨e, rfl, ?_⟩
  refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
  · dsimp [e, T, trivialSetActions, Mod.comap]
    congr 1
  · apply Mod.hom_ext
    simp only [Mod.comp_hom', mod_eqToHom_hom]
    simp [e, T, trivialSetActions, Mod.comap]

include hK hL hH in
/-- Literal identities on inverse images in the action-site presentation. Equality
comparisons obey the identity and associativity equations, before taking mates.
Source: paragraph (3) (blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (steps 4, 8): precomposition keeps sections and component maps. Associativity
is associativity of theta(psi(h)); trivial inflation ignores every group label. -/
theorem internalRestriction_presentedIdentities (θ : L ⟶ K) (ψ : H ⟶ L)
    (A : Type (u + 1)) [Category.{u} A] :
    restriction J hJ (𝟙 K) A = 𝟭 _ ∧
    restriction J hJ θ A ⋙ restriction J hJ ψ A = restriction J hJ (ψ ≫ θ) A ∧
    inflation J hJ K A ⋙ restriction J hJ θ A = inflation J hJ L A := by
  constructor
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · apply ObjectProperty.FullSubcategory.ext
      refine Functor.ext (fun U ↦ ?_) (fun U V f ↦ ?_)
      ·   rfl
      · simp [restriction, precomposition, restrictionSite]
        rfl
    · ext U
      simp [restriction, precomposition, restrictionSite]
  constructor
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · apply ObjectProperty.FullSubcategory.ext
      refine Functor.ext (fun U ↦ ?_) (fun U V f ↦ ?_)
      ·   rfl
      · simp [restriction, precomposition, restrictionSite]
    · ext U
      simp [restriction, precomposition, restrictionSite]
  · refine Functor.ext (fun X ↦ ?_) (fun X Y f ↦ ?_)
    · rfl
    · ext U
      simp [restriction, inflation, precomposition, restrictionSite, projection]

/-- The ringed realization of a stipulated right adjoint, with identity structural map.
This packages the conclusion, rather than assuming a right adjoint exists.
Source: paragraph (3); Stacks 01D3
(blueprint: lem-sfb-internal-restriction-geometric-coherence). -/
structure RestrictionRingedRealization {D : Type u} [SmallCategory D]
    (B : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (hF : ∀ X : Sheaf B (Type u), Presheaf.IsSheaf T (F.op ⋙ X.obj))
    (R : Sheaf B CommRingCat.{u}) (hR : Presheaf.IsSheaf T (F.op ⋙ R.obj))
    (G : Sheaf T (Type u) ⥤ Sheaf B (Type u))
    (a : precomposition B T F (Type u) hF ⊣ G) where
  /-- The existing ringed-topos structure with its induced module pushforward. -/
  ringed : RingedToposMorphism (baseRing T (pulledCoefficient T F R hR)) (baseRing B R)
  /-- The inverse image is the stipulated literal precomposition. -/
  inverse_eq : ringed.inverse = precomposition B T F (Type u) hF
  /-- The direct image is the supplied right adjoint. -/
  direct_eq : ringed.direct = G
  /-- Its adjunction is the supplied one, including unit and counit. -/
  adjunction_eq : HEq ringed.adj a
  /-- The structural map is the identity after the inverse-image identification. -/
  structural :
    (eqToIso inverse_eq).inv.app ((sheafCompose B (forget RingCat)).obj (baseRing B R)) ≫
      ringed.ringMap = 𝟙 _

omit [HasFiniteLimits C] in
private theorem precomposition_finiteLimits {D : Type u} [SmallCategory D]
    (B : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (hF : ∀ X : Sheaf B (Type u), Presheaf.IsSheaf T (F.op ⋙ X.obj)) :
    PreservesFiniteLimits (precomposition B T F (Type u) hF) where
  preservesFiniteLimits I _ _ := by
    have : PreservesLimitsOfShape I
        (precomposition B T F (Type u) hF ⋙ sheafToPresheaf T (Type u)) :=
      inferInstanceAs (PreservesLimitsOfShape I
        (sheafToPresheaf B (Type u) ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj F.op))
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (precomposition B T F (Type u) hF) (sheafToPresheaf T (Type u))

omit [HasFiniteLimits C] in
private theorem precomposition_ringed {D : Type u} [SmallCategory D]
    (B : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (hF : ∀ X : Sheaf B (Type u), Presheaf.IsSheaf T (F.op ⋙ X.obj))
    (R : Sheaf B CommRingCat.{u}) (hR : Presheaf.IsSheaf T (F.op ⋙ R.obj))
    (G : Sheaf T (Type u) ⥤ Sheaf B (Type u))
    (a : precomposition B T F (Type u) hF ⊣ G) :
    Nonempty (RestrictionRingedRealization B T F hF R hR G a) := by
  let d : RingedToposMorphism.RingData
      (baseRing T (pulledCoefficient T F R hR)) (baseRing B R) := {
    inverse := precomposition B T F (Type u) hF
    direct := G
    adj := a
    leftExact := precomposition_finiteLimits B T F hF
    ringMap := 𝟙 _
    ring_zero := fun X z hz U t ↦ hz (F.op.obj U) t
    ring_one := fun X z hz U t ↦ hz (F.op.obj U) t
    ring_add := fun X x y z hz U t ↦ hz (F.op.obj U) t
    ring_mul := fun X x y z hz U t ↦ hz (F.op.obj U) t }
  obtain ⟨m⟩ := SheafOfModules.ringData_inducedModules (pulledCoefficient T F R hR) R d
  exact ⟨{
    ringed := d.withModules m
    inverse_eq := rfl
    direct_eq := rfl
    adjunction_eq := HEq.rfl
    structural := by simp [RingedToposMorphism.RingData.withModules, d] }⟩

include hK hL in
/-- Given right adjoints, restriction and trivial inflation define ringed geometric
morphisms with the identity structural ring maps. No right-adjoint existence for an
arbitrary restriction is required in this assertion.
Source: paragraph (3); Stacks 01D3
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (steps 3, 7, 9): the action-site equivalence identifies these inverse images
with action restriction and trivial inflation. They preserve finite limits by the tuple
construction. Transport the ring operations, which are unchanged on sections. The
identity structural map preserves them. Equip the resulting geometric morphism with
the induced module pushforward from def-weil-pbc-ringed-topos-morphism. -/
theorem internalRestriction_ringed (θ : L ⟶ K)
    (R : Sheaf J.toGrothendieck CommRingCat.{u}) :
    (∀ (G : Sheaf (topology L J) (Type u) ⥤ Sheaf (topology K J) (Type u))
      (a : restriction J hJ θ (Type u) ⊣ G),
      Nonempty (RestrictionRingedRealization (topology K J) (topology L J)
        (restrictionSite θ) ((actionPrecomposition_isSheaf J hJ θ (Type u)).1)
        (coefficientSheaf K J hJ R)
        ((actionPrecomposition_isSheaf J hJ θ CommRingCat.{u}).1
          (coefficientSheaf K J hJ R)) G a)) ∧
    (∀ (G : Sheaf (topology K J) (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
      (a : inflation J hJ K (Type u) ⊣ G),
      Nonempty (RestrictionRingedRealization J.toGrothendieck (topology K J)
        (projection K) ((actionPrecomposition_isSheaf J hJ (𝟙 K) (Type u)).2) R
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) CommRingCat.{u}).2 R) G a)) := by
  constructor
  · intro G a
    exact precomposition_ringed _ _ _ _ _ _ G a
  · intro G a
    exact precomposition_ringed _ _ _ _ _ _ G a

include hK hL hH in
/-- The geometric comparisons are the mates of the literal inverse-image identities.
This equation expresses their compatibility over the base for two successive
restrictions. Together with the identity equation it specifies the coherence, rather
than just the existence of some right-adjoint isomorphism.
Source: paragraph (3); Stacks 0DV0; Mathlib Adjunction.Mates
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 8): compose the adjunctions by composing their Hom bijections. Under
conjugation, the two displayed paths are both the identity on the same inverse image.
Use conjugateEquiv_comp and its whiskering form; the composite adjunction has the
same three Hom bijections under either association. conjugateEquiv_id gives the unit
coherence. The same argument applies to restriction identity and composition after
the literal equalities of internalRestriction_presentedIdentities. -/
theorem internalRestriction_baseCoherence (θ : L ⟶ K) (ψ : H ⟶ L)
    (FK : Sheaf (topology K J) (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (FL : Sheaf (topology L J) (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (FH : Sheaf (topology H J) (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (Gθ : Sheaf (topology L J) (Type u) ⥤ Sheaf (topology K J) (Type u))
    (Gψ : Sheaf (topology H J) (Type u) ⥤ Sheaf (topology L J) (Type u))
    (aK : inflation J hJ K (Type u) ⊣ FK)
    (aL : inflation J hJ L (Type u) ⊣ FL)
    (aH : inflation J hJ H (Type u) ⊣ FH)
    (aθ : restriction J hJ θ (Type u) ⊣ Gθ)
    (aψ : restriction J hJ ψ (Type u) ⊣ Gψ)
    (eθ : inflation J hJ K (Type u) ⋙ restriction J hJ θ (Type u) =
      inflation J hJ L (Type u))
    (eψ : inflation J hJ L (Type u) ⋙ restriction J hJ ψ (Type u) =
      inflation J hJ H (Type u)) :
    conjugateEquiv ((aK.comp aθ).comp aψ) aH
        (eqToHom ((congrArg (fun F ↦ F ⋙ restriction J hJ ψ (Type u)) eθ).trans eψ).symm) =
      Functor.whiskerLeft Gψ (conjugateEquiv (aK.comp aθ) aL (eqToHom eθ.symm)) ≫
        conjugateEquiv (aL.comp aψ) aH (eqToHom eψ.symm) ∧
    conjugateEquiv aK aK (𝟙 _) = 𝟙 _ := by
  refine ⟨?_, conjugateEquiv_id aK⟩
  rw [← conjugateEquiv_whiskerRight (aK.comp aθ) aL aψ,
    conjugateEquiv_comp]
  congr 1

include hK hL in
/-- Coherence of identity and composition comparisons between restriction inverse
images, for any right adjoints supplied to the identified inverse images. The
identifications e2 and e3 are precisely the literal equalities stated above; they
may describe any parenthesization of a chain of restriction functors.
Source: paragraph (3); Stacks 0DV0; Mathlib Adjunction.Mates
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 8): conjugateEquiv_comp turns the composite on the right adjoints into
the reversed composite of the two inverse-image identities. eqToHom_trans identifies
that with their transitive equality. For an identity use conjugateEquiv_id. Applying
this to every pair of paths proves the identity, associativity, and over-base
coherences. ConjugateIsoEquiv makes each comparison invertible. -/
theorem internalRestriction_comparisonCoherence (θ : L ⟶ K)
    (F2 F3 : Sheaf (topology K J) (Type u) ⥤ Sheaf (topology L J) (Type u))
    (e2 : F2 = restriction J hJ θ (Type u)) (e3 : F3 = F2)
    (G1 G2 G3 : Sheaf (topology L J) (Type u) ⥤ Sheaf (topology K J) (Type u))
    (a1 : restriction J hJ θ (Type u) ⊣ G1) (a2 : F2 ⊣ G2) (a3 : F3 ⊣ G3) :
    conjugateEquiv a1 a2 (eqToHom e2) ≫ conjugateEquiv a2 a3 (eqToHom e3) =
      conjugateEquiv a1 a3 (eqToHom (e3.trans e2)) ∧
    conjugateEquiv a1 a1 (𝟙 _) = 𝟙 _ ∧
    IsIso (conjugateEquiv a1 a2 (eqToHom e2)) := by
  refine ⟨?_, conjugateEquiv_id a1, inferInstance⟩
  rw [conjugateEquiv_comp]
  congr 1
  exact eqToHom_trans e3 e2

private noncomputable def coefficientChange {D : Type u} [SmallCategory D]
    (B : GrothendieckTopology D) {R R' : Sheaf B CommRingCat.{u}} (φ : R ⟶ R') :
    CoefficientChange B φ where
  ringed := {
    inverse := 𝟭 _
    direct := 𝟭 _
    adj := Adjunction.id
    leftExact := inferInstance
    ringMap := (sheafCompose B (forget RingCat)).map
      ((sheafCompose B (forget₂ CommRingCat RingCat)).map φ)
    ring_zero := by
      intro T z hz U t
      change (φ.hom.app U).hom (z.hom.app U t) = 0
      rw [hz U t]
      exact (φ.hom.app U).hom.map_zero
    ring_one := by
      intro T z hz U t
      change (φ.hom.app U).hom (z.hom.app U t) = 1
      rw [hz U t]
      exact (φ.hom.app U).hom.map_one
    ring_add := by
      intro T x y z hz U t
      change (φ.hom.app U).hom (z.hom.app U t) =
        (φ.hom.app U).hom (x.hom.app U t) + (φ.hom.app U).hom (y.hom.app U t)
      rw [hz U t]
      exact (φ.hom.app U).hom.map_add _ _
    ring_mul := by
      intro T x y z hz U t
      change (φ.hom.app U).hom (z.hom.app U t) =
        (φ.hom.app U).hom (x.hom.app U t) * (φ.hom.app U).hom (y.hom.app U t)
      rw [hz U t]
      exact (φ.hom.app U).hom.map_mul _ _
    modules := SheafOfModules.restrictScalars
      ((sheafCompose B (forget₂ CommRingCat RingCat)).map φ)
    additive := inferInstance
    underlying := Iso.refl _
    module_linear := by
      intro M T a x y z hz U t
      exact hz U t }
  inverse_eq := rfl
  structural := by simp

include hK hL in
/-- Coefficient maps have their original components. The two composites in the
restriction square have the same structural map, under the literal base comparison.
The vertical ringed maps have inverse image the identity and structural map phi.
Source: paragraph (3); Stacks 01D3
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 9): all actions on coefficients are trivial, so phi is equivariant.
Both composites have components id composed with phi_U or phi_U composed with id.
The identity-topos morphism has direction (E,R') to (E,R), as encoded by
CoefficientChange. These component equalities also give the identity coherences. -/
theorem internalRestriction_coefficients (θ : L ⟶ K)
    {R R' : Sheaf J.toGrothendieck CommRingCat.{u}} (φ : R ⟶ R') :
    Nonempty (CoefficientChange J.toGrothendieck φ) ∧
    Nonempty (CoefficientChange (topology K J)
      ((inflation J hJ K CommRingCat.{u}).map φ)) ∧
    (∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      (((inflation J hJ K CommRingCat.{u}).map φ).hom.app
        (op (Object.mk (K := K) U.unop))) r = φ.hom.app U r) ∧
    (restriction J hJ θ CommRingCat.{u}).map
        ((inflation J hJ K CommRingCat.{u}).map φ) ≫
          (eqToIso ((internalRestriction_presentedIdentities J hJ hK hL hL θ (𝟙 L)
            CommRingCat.{u}).2.2)).hom.app R' =
      (eqToIso ((internalRestriction_presentedIdentities J hJ hK hL hL θ (𝟙 L)
        CommRingCat.{u}).2.2)).hom.app R ≫
          (inflation J hJ L CommRingCat.{u}).map φ := by
  refine ⟨⟨coefficientChange J.toGrothendieck φ⟩,
    ⟨coefficientChange (topology K J) ((inflation J hJ K CommRingCat.{u}).map φ)⟩,
    fun U r ↦ rfl, ?_⟩
  exact (eqToIso ((internalRestriction_presentedIdentities J hJ hK hL hL θ (𝟙 L)
    CommRingCat.{u}).2.2)).hom.naturality φ

/-- The normalized extension-of-scalars square for a literal precomposition.
This is a record of comparisons, not an assumption used to define a pullback.
Source: paragraph (3); Stacks 03D7, 03EK, 03CY
(blueprint: lem-sfb-internal-restriction-geometric-coherence). -/
structure RestrictionScalarSquare {D : Type u} [SmallCategory D]
    (B : GrothendieckTopology C) (T : GrothendieckTopology D) (F : D ⥤ C)
    (hF : ∀ X : Sheaf B (Type u), Presheaf.IsSheaf T (F.op ⋙ X.obj))
    (hFc : ∀ X : Sheaf B CommRingCat.{u}, Presheaf.IsSheaf T (F.op ⋙ X.obj))
    {R R' : Sheaf B CommRingCat.{u}} (φ : R ⟶ R')
    (P : PrecompositionPullback B T F hF R (hFc R))
    (P' : PrecompositionPullback B T F hF R' (hFc R')) where
  /-- The comparison of the two extension-of-scalars pullbacks. -/
  comparison (M : ringedSiteModules.{u} (baseRing B R)) :
    P'.pullback.functor.obj (SheafOfModules.changeOfRings.{u, u, u} φ M) ≅
      SheafOfModules.changeOfRings.{u, u, u} ((precomposition B T F CommRingCat.{u} hFc).map φ)
        (P.pullback.functor.obj M)
  /-- Naturality is for the actual extension-of-scalars maps. -/
  naturality {M N : ringedSiteModules.{u} (baseRing B R)} (f : M ⟶ N) :
    P'.pullback.functor.map
        (SheafOfModules.changeOfRingsHom.{u, u, u} φ M f) ≫
        (comparison N).hom =
      (comparison M).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u}
        ((precomposition B T F CommRingCat.{u} hFc).map φ)
        (P.pullback.functor.obj M) (P.pullback.functor.map f)
  /-- The comparison takes r' tensor m to the identical local pure tensor. -/
  pure (M : ringedSiteModules.{u} (baseRing B R)) (U : Dᵒᵖ)
      (r : R'.obj.obj (F.op.obj U)) (m : M.val.obj (F.op.obj U)) :
    (comparison M).hom.val.app U
        ((P'.sections (SheafOfModules.changeOfRings.{u, u, u} φ M) U).symm
          (SheafOfModules.scalarExtensionConstraintTmul φ M (F.op.obj U) m r)) =
      SheafOfModules.scalarExtensionConstraintTmul
        ((precomposition B T F CommRingCat.{u} hFc).map φ)
        (P.pullback.functor.obj M) U ((P.sections M U).symm m) r

include hK hL in
/-- The coefficient squares for p_K and q_theta commute on module pullbacks, with
the identity on presheaf pure tensors, also for nonflat maps of coefficient rings.
Source: paragraph (3); Stacks 03D7, 03EK, 03CY
(blueprint: lem-sfb-internal-restriction-geometric-coherence).
Proof (step 10): module pullback for a coefficient map is the sheafified sectionwise
scalar tensor, by lem-weil-pbc-ringed-topoi-module-adjunction. For restriction and
trivial inflation the structural ring map is the identity, and the normalized
module-tensor comparison of lem-sfb-internal-restriction-module-tensor keeps each
pure tensor. Thus r' tensor m maps to r' tensor m, equivariantly for the restricted
or trivial action. Pure tensors generate the presheaf tensors. The unique
sheafification factorization (def-weil-presheaf-modules-sheafification) gives the
comparison and naturality; the same uniqueness gives its identity and composition
coherences. No flatness, nonzero-ring or nonempty-cover assumption is used. -/
theorem internalRestriction_scalarSquares (θ : L ⟶ K)
    {R R' : Sheaf J.toGrothendieck CommRingCat.{u}} (φ : R ⟶ R') :
    (∀ (P : PrecompositionPullback J.toGrothendieck (topology K J) (projection K)
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) (Type u)).2) R
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) CommRingCat.{u}).2 R))
      (P' : PrecompositionPullback J.toGrothendieck (topology K J) (projection K)
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) (Type u)).2) R'
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) CommRingCat.{u}).2 R')),
      Nonempty (RestrictionScalarSquare J.toGrothendieck (topology K J) (projection K)
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) (Type u)).2)
        ((actionPrecomposition_isSheaf J hJ (𝟙 K) CommRingCat.{u}).2) φ P P')) ∧
    (∀ (P : PrecompositionPullback (topology K J) (topology L J) (restrictionSite θ)
        ((actionPrecomposition_isSheaf J hJ θ (Type u)).1) (coefficientSheaf K J hJ R)
        ((actionPrecomposition_isSheaf J hJ θ CommRingCat.{u}).1
          (coefficientSheaf K J hJ R)))
      (P' : PrecompositionPullback (topology K J) (topology L J) (restrictionSite θ)
        ((actionPrecomposition_isSheaf J hJ θ (Type u)).1) (coefficientSheaf K J hJ R')
        ((actionPrecomposition_isSheaf J hJ θ CommRingCat.{u}).1
          (coefficientSheaf K J hJ R'))),
      Nonempty (RestrictionScalarSquare (topology K J) (topology L J) (restrictionSite θ)
        ((actionPrecomposition_isSheaf J hJ θ (Type u)).1)
        ((actionPrecomposition_isSheaf J hJ θ CommRingCat.{u}).1)
        ((inflation J hJ K CommRingCat.{u}).map φ) P P')) := by
  sorry

end CategoryTheory.InternalActionSite
