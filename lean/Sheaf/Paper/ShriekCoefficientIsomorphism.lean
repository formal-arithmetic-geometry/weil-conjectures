/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Sheaf.Compactification.BoundaryRefinement
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Sheaf.Paper.CondensedCoefficientIsoConstructible
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

/-!
# Coefficient-isomorphism transport of compactification functors

Source: blueprint main-20261015, sk-thm-existence/det-existence-restriction and
sk-def-sfb-coefficient-comparisons, Push and extension by zero
(blueprint: lem-sfb-shriek-coefficient-isomorphism).

The comparison is constructed from the two canonical scalar-restriction comparisons.
All categories are the ordinary unbounded derived module-object categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar

/-- Termwise restriction along the inverse coefficient isomorphism.
Source: blueprint coefficient comparisons, ring-isomorphism specialization
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
noncomputable abbrev shriekCoefficientTransport (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :=
  (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficientMap e.inv.hom T)).mapDerivedCategory

/-- The existing finite-constant-model, finite-Tor property, as an object property.
Source: blueprint det-existence-restriction, coefficient specializations
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
abbrev shriekCoefficientCtf (T : Scheme.{u}) :=
  constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _

/-- The existing intersection-defined localizing closure, with coproducts indexed in
`Type (u + 1)`, the fixed ambient Hom universe.
Source: blueprint det-existence-localizing and coefficient comparisons
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
abbrev shriekCoefficientLocalizing (T : Scheme.{u}) :=
  (shriekCoefficientCtf (Λ := Λ) T).localizingClosure

-- Keep the geometric pullback constructions opaque in categorical comparisons.
set_option backward.isDefEq.respectTransparency true

/-- The ambient canonical comparison, obtained by the direct-image comparison and
then the termwise open-extension comparison, with associators inserted.
Source: blueprint coefficient comparisons, Push and extension by zero
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
noncomputable def shriekCoefficientCompactificationIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        shriekCoefficientTransport e Y ≅
      shriekCoefficientTransport e X ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  letI (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  letI (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap e.inv.hom T)).symm
  let J := CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i
  let J' := CondensedRing.openImmersionLowerShriek Λ' c.obj.obj.i
  let P := CondensedRing.lowerStar Λ c.obj.obj.g
  let P' := CondensedRing.lowerStar Λ' c.obj.obj.g
  let UZ := shriekCoefficientTransport e c.obj.obj.Z
  let d : P.rightDerivedFunctor ⋙ shriekCoefficientTransport e Y ≅
      UZ ⋙ P'.rightDerivedFunctor :=
    CondensedRing.derivedComapLowerStarIso e.inv.hom c.obj.obj.g
  let j : J.mapDerivedCategory ⋙ UZ ≅
      shriekCoefficientTransport e X ⋙ J'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso J (Mod.comap
      (coefficientMap e.inv.hom c.obj.obj.Z))).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.comapOpenImmersionLowerShriekIso e.inv.hom c.obj.obj.i) ≪≫
      Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom X)) J'
  exact Functor.associator J.mapDerivedCategory P.rightDerivedFunctor
      (shriekCoefficientTransport e Y) ≪≫
    Functor.isoWhiskerLeft J.mapDerivedCategory d ≪≫
    (Functor.associator J.mapDerivedCategory UZ P'.rightDerivedFunctor).symm ≪≫
    Functor.isoWhiskerRight j P'.rightDerivedFunctor ≪≫
    Functor.associator (shriekCoefficientTransport e X) J'.mapDerivedCategory
      P'.rightDerivedFunctor

private theorem localModel_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : HasFiniteConstantLocalModel Λ T M) :
    HasFiniteConstantLocalModel Λ T N := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨j⟩⟩ := hU a
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f a)).mapIso i.symm ≪≫ j⟩⟩

private theorem stratified_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : IsFiniteConstantStratified Λ T M) :
    IsFiniteConstantStratified Λ T N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ localModel_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso i) (hS a)⟩

private theorem constructible_iso {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (i : M ≅ N) (h : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ T N := by
  classical
  unfold IsConstantModelConstructible at h ⊢
  split at h
  · rw [if_pos ‹_›]
    exact stratified_iso i h
  · rw [if_neg ‹_›]
    exact fun U hU ↦ stratified_iso
      ((CondensedRing.upperStar Λ U.ι).mapIso i) (h U hU)

-- Match the ambient tensor instance already fixed in `shriekCoefficientCtf`.
set_option backward.isDefEq.respectTransparency false in
private instance ctf_replete (T : Scheme.{u}) :
    (shriekCoefficientCtf (Λ := Λ) T).IsClosedUnderIsomorphisms where
  of_iso i h :=
    ⟨⟨ObjectProperty.prop_of_iso _ i h.1.1,
      fun n ↦ constructible_iso ((DerivedCategory.homologyFunctor _ n).mapIso i) (h.1.2 n)⟩,
      ObjectProperty.prop_of_iso _ i h.2⟩

private noncomputable def transportCompIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    shriekCoefficientTransport e T ⋙ shriekCoefficientTransport e.symm T ≅ 𝟭 _ := by
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((Mod.comapComp _ _).symm ≪≫ Mod.comapCongr (by
        change (upperStarFromPoint T).map e.hom.hom ≫
          (upperStarFromPoint T).map e.inv.hom = 𝟙 _
        rw [← Functor.map_comp]
        change (upperStarFromPoint T).map ((Mon.forget _).map (e.hom ≫ e.inv)) = _
        simp only [Iso.hom_inv_id]
        exact (upperStarFromPoint T).map_id Λ) ≪≫ Mod.comapId _) ≪≫
    Functor.mapDerivedCategoryIdIso _

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private theorem transport_equivalence (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientTransport e T).IsEquivalence := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  have : (Mod.comap (coefficientMap e.inv.hom T)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.inv.hom T)).functor.IsEquivalence)
  exact Functor.isEquivalence_mapDerivedCategory _

private theorem transport_ctf (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    ∀ K, shriekCoefficientCtf (Λ := Λ') T ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientCtf (Λ := Λ) T K := by
  intro K
  constructor
  · intro h
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (constantModelCtf_coefficientIso e.symm T
        ⟨(shriekCoefficientTransport e T).obj K, h⟩)
  · intro h
    exact constantModelCtf_coefficientIso e T ⟨K, h⟩

private theorem map_closure
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (h : ∀ K, P K → Q (F.obj K)) :
    ∀ K, P.localizingClosure K → Q.localizingClosure (F.obj K) := by
  have : (Q.localizingClosure.inverseImage F).IsLocalizing :=
    { isClosedUnderColimitsOfShape_discrete := fun _ ↦ inferInstance }
  exact ObjectProperty.localizingClosure_le
    (Q := Q.localizingClosure.inverseImage F)
    (fun K hK ↦ Q.le_localizingClosure _ (h K hK))

/-- Exact scalar transport identifies both the constructible classes and their closures.
Source: blueprint det-existence-restriction and coefficient comparisons
(blueprint: lem-sfb-shriek-coefficient-isomorphism).

Proof: The sheaf tensor, module-object Grothendieck, and derived coproduct theorems
supply all ambient small coproducts, including the empty one. Restriction along the
inverse and forward ring isomorphisms gives inverse exact module equivalences.
Apply exact-functor derived factorization to obtain inverse triangulated functors.
Equivalences preserve coproducts. Apply constantModelCtf_coefficientIso to e and its
inverse and use repleteness to identify the constructible classes. The inverse image
of the primed localizing closure is replete, triangulated and closed under coproducts,
and contains the unprimed constructible class. Minimality of the defining intersection
gives preservation of the closure. Repeat for the inverse to obtain reflection. -/
theorem shriekCoefficientIso_transport (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientTransport e T).IsEquivalence ∧
    (shriekCoefficientTransport e T).IsTriangulated ∧
    (∀ I : Type (u + 1),
      PreservesColimitsOfShape (Discrete I) (shriekCoefficientTransport e T)) ∧
    (∀ K, shriekCoefficientCtf (Λ := Λ') T ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientCtf (Λ := Λ) T K) ∧
    (∀ K, shriekCoefficientLocalizing (Λ := Λ') T
        ((shriekCoefficientTransport e T).obj K) ↔
      shriekCoefficientLocalizing (Λ := Λ) T K) := by
  have := transport_equivalence e T
  have := transport_equivalence e.symm T
  refine ⟨inferInstance, inferInstance, fun _ ↦ inferInstance, transport_ctf e T, ?_⟩
  intro K
  constructor
  · intro h
    exact ObjectProperty.prop_of_iso _ ((transportCompIso e T).app K)
      (map_closure (shriekCoefficientTransport e.symm T)
        (shriekCoefficientCtf (Λ := Λ') T) (shriekCoefficientCtf (Λ := Λ) T)
        (fun L hL ↦ (transport_ctf e.symm T L).2 hL) _ h)
  · exact map_closure (shriekCoefficientTransport e T)
      (shriekCoefficientCtf (Λ := Λ) T) (shriekCoefficientCtf (Λ := Λ') T)
      (fun L hL ↦ (transport_ctf e T L).2 hL) K

/-- The restriction of `U_T` to the two intersection-defined localizing closures.
Source: blueprint coefficient comparisons and det-existence-restriction
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
noncomputable abbrev shriekCoefficientLocalizingTransport
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientLocalizing (Λ := Λ) T).FullSubcategory ⥤
      (shriekCoefficientLocalizing (Λ := Λ') T).FullSubcategory :=
  (shriekCoefficientLocalizing (Λ := Λ') T).lift
    ((shriekCoefficientLocalizing (Λ := Λ) T).ι ⋙ shriekCoefficientTransport e T)
    (fun K ↦ ((shriekCoefficientIso_transport e T).2.2.2.2 K.obj).2 K.property)

/-- The restricted scalar transport is an exact equivalence.
Source: blueprint coefficient comparisons and det-existence-restriction
(blueprint: lem-sfb-shriek-coefficient-isomorphism).

Proof: The inverse scalar restriction preserves the localizing closure by the same
intersection argument as in shriekCoefficientIso_transport. The unit and counit of the
ambient equivalence restrict to these full replete subcategories. The shift and
triangles are induced from the ambient derived category, so exactness restricts too. -/
theorem shriekCoefficientIso_localizing
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u}) :
    (shriekCoefficientLocalizingTransport e T).IsEquivalence ∧
      (shriekCoefficientLocalizingTransport e T).IsTriangulated := by
  have := (shriekCoefficientIso_transport e T).1
  have h : (shriekCoefficientLocalizing (Λ := Λ') T).inverseImage
      (shriekCoefficientTransport e T) = shriekCoefficientLocalizing (Λ := Λ) T := by
    ext K
    exact (shriekCoefficientIso_transport e T).2.2.2.2 K
  let E := (shriekCoefficientTransport e T).asEquivalence
  exact ⟨inferInstanceAs ((E.congrFullSubcategory h).functor.IsEquivalence), inferInstance⟩

/-- Preservation of the localizing closure transfers to the primed compactification functor.
Source: blueprint coefficient comparisons and det-existence-restriction
(blueprint: lem-sfb-shriek-coefficient-isomorphism).

Proof: For M' in the primed closure, inverse scalar restriction puts V_X M' in the
unprimed closure. The assumed preservation puts H V_X M' in the unprimed target
closure, hence U_Y H V_X M' is in the primed target closure. The canonical comparison
and U_X V_X M' ≅ M' identify this with H' M'. Repleteness proves the assertion. -/
theorem shriekCoefficientIso_preservesLocalizing
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, shriekCoefficientLocalizing (Λ := Λ) X K →
      shriekCoefficientLocalizing (Λ := Λ) Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) :
    ∀ K, shriekCoefficientLocalizing (Λ := Λ') X K →
      shriekCoefficientLocalizing (Λ := Λ') Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).obj K) := by
  intro K hK
  have := (shriekCoefficientIso_transport e X).1
  let U := (shriekCoefficientTransport e X).asEquivalence
  let L := U.inverse.obj K
  have hL : shriekCoefficientLocalizing (Λ := Λ) X L :=
    ((shriekCoefficientIso_transport e X).2.2.2.2 L).1
      (ObjectProperty.prop_of_iso _ (U.counitIso.app K).symm hK)
  exact ObjectProperty.prop_of_iso _
    ((shriekCoefficientCompactificationIso e c).app L ≪≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj).mapIso
        (U.counitIso.app K))
    (((shriekCoefficientIso_transport e Y).2.2.2.2 _).2 (h L hL))

/-- The restriction F of the fixed compactification functor H to the localizing closures.
Source: blueprint det-existence-restriction, notation F in coefficient transport
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
noncomputable abbrev shriekCoefficientLowerShriekLocalizing
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, shriekCoefficientLocalizing (Λ := Λ) X K →
      shriekCoefficientLocalizing (Λ := Λ) Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) :
    (shriekCoefficientLocalizing (Λ := Λ) X).FullSubcategory ⥤
      (shriekCoefficientLocalizing (Λ := Λ) Y).FullSubcategory :=
  (shriekCoefficientLocalizing (Λ := Λ) Y).lift
    ((shriekCoefficientLocalizing (Λ := Λ) X).ι ⋙
      CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj)
    (fun K ↦ h K.obj K.property)

/-- The left comparison a on localizing closures, with components the ambient canonical
comparison. Source: blueprint coefficient comparisons and det-existence-restriction
(blueprint: lem-sfb-shriek-coefficient-isomorphism). -/
noncomputable def shriekCoefficientLocalizingIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, shriekCoefficientLocalizing (Λ := Λ) X K →
      shriekCoefficientLocalizing (Λ := Λ) Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K)) :
    shriekCoefficientLowerShriekLocalizing c h ⋙ shriekCoefficientLocalizingTransport e Y ≅
      shriekCoefficientLocalizingTransport e X ⋙
        shriekCoefficientLowerShriekLocalizing c
          (shriekCoefficientIso_preservesLocalizing e c h) :=
  NatIso.ofComponents
    (fun K ↦ (shriekCoefficientLocalizing (Λ := Λ') Y).isoMk
      ((shriekCoefficientCompactificationIso e c).app K.obj))
    (fun {_ _} g ↦ ObjectProperty.hom_ext _
      ((shriekCoefficientCompactificationIso e c).hom.naturality g.hom))

/-- The canonical left comparison transports the given right adjoints uniquely with their
counits, and either right adjoint preserves the constructible finite-Tor class exactly
when the other does.
Source: blueprint det-existence-restriction, identification of the same Brown adjoint,
and coefficient comparisons, Push, extension by zero, Shriek
(blueprint: lem-sfb-shriek-coefficient-isomorphism).

Proof: Let a be the restricted canonical comparison. For N in the unprimed target
closure, set t_N = a.inv.app (G.obj N) ≫ U_Y.map (adj.counit.app N), and let b_N
be its adjunct under the given primed adjunction. Equivalently b is the right mate
of a.inv. Naturality of a, the unit and the counit gives a natural transformation.
The exact equivalences U_X and U_Y and the mate-isomorphism theorem imply that b
is invertible. The adjunction hom-bijection formula gives
  a.hom.app (G.obj N) ≫ F'.map b_N ≫ adj'.counit.app (U_Y.obj N)
    = U_Y.map (adj.counit.app N).
Conversely that equation determines the adjunct t_N and hence b_N uniquely.
For the final equivalence, transport a primed constructible object by V_Y, apply
the unprimed preservation assumption, transport by U_X, and use b and U_Y V_Y ≅ id.
Conversely apply the primed preservation assumption to U_Y N, use b to identify
U_X G N with G' U_Y N, and reflect constructibility along U_X. All constructible
classes are the finite-constant-model, finite-Tor classes of this node. -/
theorem shriekCoefficientIso_adjoints
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, shriekCoefficientLocalizing (Λ := Λ) X K →
      shriekCoefficientLocalizing (Λ := Λ) Y
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (shriekCoefficientLocalizing (Λ := Λ) Y).FullSubcategory ⥤
      (shriekCoefficientLocalizing (Λ := Λ) X).FullSubcategory)
    (G' : (shriekCoefficientLocalizing (Λ := Λ') Y).FullSubcategory ⥤
      (shriekCoefficientLocalizing (Λ := Λ') X).FullSubcategory)
    (adj : shriekCoefficientLowerShriekLocalizing c h ⊣ G)
    (adj' : shriekCoefficientLowerShriekLocalizing c
      (shriekCoefficientIso_preservesLocalizing e c h) ⊣ G') :
    (∃! b : G ⋙ shriekCoefficientLocalizingTransport e X ≅
        shriekCoefficientLocalizingTransport e Y ⋙ G',
      ∀ N, (shriekCoefficientLocalizingIso e c h).hom.app (G.obj N) ≫
        (shriekCoefficientLowerShriekLocalizing c
          (shriekCoefficientIso_preservesLocalizing e c h)).map (b.hom.app N) ≫
        adj'.counit.app ((shriekCoefficientLocalizingTransport e Y).obj N) =
          (shriekCoefficientLocalizingTransport e Y).map (adj.counit.app N)) ∧
    ((∀ N : (shriekCoefficientLocalizing (Λ := Λ) Y).FullSubcategory,
        shriekCoefficientCtf (Λ := Λ) Y N.obj →
        shriekCoefficientCtf (Λ := Λ) X (G.obj N).obj) ↔
      (∀ N : (shriekCoefficientLocalizing (Λ := Λ') Y).FullSubcategory,
        shriekCoefficientCtf (Λ := Λ') Y N.obj →
        shriekCoefficientCtf (Λ := Λ') X (G'.obj N).obj)) := by
  have := (shriekCoefficientIso_localizing e X).1
  have := (shriekCoefficientIso_localizing e Y).1
  let U := shriekCoefficientLocalizingTransport e X
  let V := shriekCoefficientLocalizingTransport e Y
  let F' := shriekCoefficientLowerShriekLocalizing c
    (shriekCoefficientIso_preservesLocalizing e c h)
  let a := shriekCoefficientLocalizingIso e c h
  have : IsIso (mateEquiv adj adj' a.inv).natTrans :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj' U V a.symm
  let b : G ⋙ U ≅ V ⋙ G' := asIso (mateEquiv adj adj' a.inv).natTrans
  have hb (N) : a.hom.app (G.obj N) ≫ F'.map (b.hom.app N) ≫
      adj'.counit.app (V.obj N) = V.map (adj.counit.app N) := by
    change a.hom.app (G.obj N) ≫
      F'.map ((mateEquiv adj adj' a.inv).natTrans.app N) ≫ _ = _
    rw [mateEquiv_counit adj adj' a.inv N]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rfl
  refine ⟨⟨b, hb, ?_⟩, ?_⟩
  · intro b' hb'
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adj'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_symm_apply]
    apply (cancel_epi (a.hom.app (G.obj N))).1
    exact (hb' N).trans (hb N).symm
  · constructor
    · intro hG N hN
      let M := V.asEquivalence.inverse.obj N
      let i := V.asEquivalence.counitIso.app N
      have hM : shriekCoefficientCtf (Λ := Λ) Y M.obj :=
        (transport_ctf e Y M.obj).1
          (ObjectProperty.prop_of_iso _
            ((shriekCoefficientLocalizing (Λ := Λ') Y).ι.mapIso i).symm hN)
      exact ObjectProperty.prop_of_iso _
        ((shriekCoefficientLocalizing (Λ := Λ') X).ι.mapIso
          (b.app M ≪≫ G'.mapIso i))
        ((transport_ctf e X (G.obj M).obj).2 (hG M hM))
    · intro hG N hN
      apply (transport_ctf e X (G.obj N).obj).1
      exact ObjectProperty.prop_of_iso _
        ((shriekCoefficientLocalizing (Λ := Λ') X).ι.mapIso (b.app N)).symm
        (hG (V.obj N) ((transport_ctf e Y N.obj).2 hN))

end AlgebraicGeometry.ProEtale
