/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

/-!
# Computing derived morphisms with arbitrary K-injective resolutions

Source: Stacks Project, Derived Categories, Tags 070I and 070Y, and the explicit
arbitrary-resolution consequence in the DAG (blueprint: lem-sf-kinjective-derived-map-computation).
The comparison is the recorded comparison of `def-sfb-right-derived-functor`.
All complexes are unbounded, and resolution maps need only be quasi-isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- Transport a derived morphism along two resolution maps, with the canonical comparison
between the two localization presentations. Source: Stacks Tags 070I and 070Y
(blueprint: lem-sf-kinjective-derived-map-computation). -/
noncomputable def kInjectiveResolutionHomTarget
    {N N' I J : CochainComplex C ℤ} (a : N ⟶ I) (b : N' ⟶ J)
    [QuasiIso a] (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj I) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J) :=
  (DerivedCategory.quotientCompQhIso C).hom.app I ≫ CategoryTheory.inv (DerivedCategory.Q.map a) ≫
    h ≫ DerivedCategory.Q.map b ≫ (DerivedCategory.quotientCompQhIso C).inv.app J

/-- Apply F to a homotopy class and then localize, using the canonical presentation
isomorphisms. Source: Stacks Tag 014X, degreewise additivity and preservation of homotopy
(blueprint: lem-sf-kinjective-derived-map-computation). -/
noncomputable def kInjectiveHomotopyImage (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ}
    (g : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map g) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app _

variable (F : C ⥤ D) [F.Additive]
  (enough : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The map c_a inverse, followed by RF(h), followed by c_b. The c maps are exactly
RF(Qa) followed by the inverse derived unit at the resolution, as recorded in the dependency.
Source: Stacks Tag 070Y (blueprint: lem-sf-kinjective-derived-map-computation). -/
noncomputable def kInjectiveDerivedResolutionMap
    {N N' I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N' ⟶ J) [QuasiIso a] [QuasiIso b]
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) :=
  (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a).inv ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions enough).map h ≫
    (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough b).hom

/-- The canonical transition c_a inverse followed by c_b for two resolutions of N.
Source: Stacks Tag 070Y (blueprint: lem-sf-kinjective-derived-map-computation). -/
noncomputable def kInjectiveDerivedResolutionTransition
    {N I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N ⟶ J) [QuasiIso a] [QuasiIso b] :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) :=
  (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a).symm ≪≫
    F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough b

/-- Unique homotopy-class computation of every derived morphism. Source: Stacks Tags
070I and 070Y (blueprint: lem-sf-kinjective-derived-map-computation).

Proof: (1) Additivity induces F on homotopy classes (Tag 014X).
(2) Localization inverts a and b, and the derived unit is invertible on I and J, so the
recorded c maps are isomorphisms, with inverses RF(Qa inverse) followed by eta_I.
(3) Apply `CochainComplex.IsKInjective.Qh_map_bijective` to I and J to get existence and
uniqueness of g. (4) Naturality gives RF(Qg) eta_I = eta_J Q(Fg). Substitute
Qg = Qb h (Qa inverse), cancel eta_J and use functoriality to obtain the stated formula.
These are steps 1--4 of the node, using def-sfb-right-derived-functor,
def-weil-abstract-derived-category and lem-weil-pbc-kinjective-hom-derived. -/
theorem kInjectiveDerivedMapComputation
    {N N' I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N' ⟶ J) [QuasiIso a] [QuasiIso b]
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    (∃! g : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J,
      DerivedCategory.Qh.map g = kInjectiveResolutionHomTarget a b h) ∧
    (∀ g : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J,
      DerivedCategory.Qh.map g = kInjectiveResolutionHomTarget a b h →
      F.kInjectiveDerivedResolutionMap enough a b h = F.kInjectiveHomotopyImage g) := by
  constructor
  · obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (.up ℤ)).obj I) J).surjective
        (kInjectiveResolutionHomTarget a b h)
    exact ⟨g, hg, fun g' hg' ↦
      (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective (hg'.trans hg.symm)⟩
  · intro g hg
    let R := F.rightDerivedFunctorOfQuasiIsoResolutions enough
    let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit enough
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough I
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso enough J
    calc
      F.kInjectiveDerivedResolutionMap enough a b h =
          (DerivedCategory.quotientCompQhIso D).inv.app
              ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
            η.app ((HomotopyCategory.quotient C (.up ℤ)).obj I) ≫
            R.map (DerivedCategory.Qh.map g) ≫
            CategoryTheory.inv (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
            (DerivedCategory.quotientCompQhIso D).hom.app
              ((F.mapHomologicalComplex (.up ℤ)).obj J) := by
              rw [hg]
              simp [kInjectiveDerivedResolutionMap,
                rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
                kInjectiveResolutionHomTarget, R, η, Category.assoc,
                ← Functor.map_comp, ← Functor.map_comp_assoc, -Functor.map_inv,
                -NatTrans.naturality]
      _ = F.kInjectiveHomotopyImage g := by
        have hn := η.naturality g
        dsimp at hn
        dsimp [kInjectiveHomotopyImage]
        change _ ≫ η.app _ ≫ R.map (DerivedCategory.Qh.map g) ≫ _ ≫ _ = _
        rw [← reassoc_of% hn]
        simp
        rfl

/-- Identity and composition compatibility, both for the unique lifts and their computed
images. Source: Stacks Tags 070I and 070Y
(blueprint: lem-sf-kinjective-derived-map-computation).

Proof: step 5 of the node. Q sends the identity lift to the transported identity.
For composable lifts g and g', Q(g g') is Qd h' (Qb inverse) Qb h (Qa inverse),
which cancels to the transported composite. Injectivity of the Hom comparison proves
these are the unique lifts. F on homotopy classes and Q preserve identities and
composition. Equivalently the c_b inverse and c_b cancel in the two displayed maps. -/
theorem kInjectiveDerivedMapComputation_functorial
    {N N' N'' I J L : CochainComplex C ℤ}
    [I.IsKInjective] [J.IsKInjective] [L.IsKInjective]
    (a : N ⟶ I) (b : N' ⟶ J) (d : N'' ⟶ L)
    [QuasiIso a] [QuasiIso b] [QuasiIso d]
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (h' : DerivedCategory.Q.obj N' ⟶ DerivedCategory.Q.obj N'') :
    DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient C (.up ℤ)).obj I)) =
      kInjectiveResolutionHomTarget a a (𝟙 _) ∧
    F.kInjectiveDerivedResolutionMap enough a a (𝟙 _) = 𝟙 _ ∧
    (∀ (g : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj J)
        (g' : (HomotopyCategory.quotient C (.up ℤ)).obj J ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj L),
      DerivedCategory.Qh.map g = kInjectiveResolutionHomTarget a b h →
      DerivedCategory.Qh.map g' = kInjectiveResolutionHomTarget b d h' →
      DerivedCategory.Qh.map (g ≫ g') = kInjectiveResolutionHomTarget a d (h ≫ h')) ∧
    F.kInjectiveDerivedResolutionMap enough a d (h ≫ h') =
      F.kInjectiveDerivedResolutionMap enough a b h ≫
        F.kInjectiveDerivedResolutionMap enough b d h' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [kInjectiveResolutionHomTarget, -NatTrans.naturality]
  · simp [kInjectiveDerivedResolutionMap]
  · intro g g' hg hg'
    rw [Functor.map_comp, hg, hg']
    simp [kInjectiveResolutionHomTarget, Category.assoc]
  · simp [kInjectiveDerivedResolutionMap, Functor.map_comp, Category.assoc]

/-- The transition is the image of the unique lift of Qa inverse followed by Qb.
Source: Stacks Tags 070I and 070Y
(blueprint: lem-sf-kinjective-derived-map-computation).

Proof: step 6 of the node applies the Hom bijection and the map formula to h = identity.
The computed map is c_a inverse followed by c_b. The unique k is therefore exactly
its K-injective homotopy-class representative. -/
theorem kInjectiveDerivedResolutionTransition_computation
    {N I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N ⟶ J) [QuasiIso a] [QuasiIso b] :
    (∃! k : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J,
      DerivedCategory.Qh.map k = kInjectiveResolutionHomTarget a b (𝟙 _)) ∧
    (∀ k : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J,
      DerivedCategory.Qh.map k = kInjectiveResolutionHomTarget a b (𝟙 _) →
      (F.kInjectiveDerivedResolutionTransition enough a b).hom =
        F.kInjectiveHomotopyImage k) := by
  obtain ⟨hex, hmap⟩ := F.kInjectiveDerivedMapComputation enough a b (𝟙 _)
  refine ⟨hex, fun k hk ↦ ?_⟩
  simpa [kInjectiveDerivedResolutionMap, kInjectiveDerivedResolutionTransition] using hmap k hk

/-- Identity, inverse and cocycle laws for the transition isomorphisms.
Source: Stacks Tag 070Y (blueprint: lem-sf-kinjective-derived-map-computation).

Proof: step 6 of the node. Each transition is the composite of two c isomorphisms.
Cancel c_a with its inverse to get the identity, reverse the two factors to get the
inverse, and cancel the middle c_b inverse with c_b for the three-resolution cocycle. -/
theorem kInjectiveDerivedResolutionTransition_laws
    {N I J L : CochainComplex C ℤ}
    [I.IsKInjective] [J.IsKInjective] [L.IsKInjective]
    (a : N ⟶ I) (b : N ⟶ J) (d : N ⟶ L)
    [QuasiIso a] [QuasiIso b] [QuasiIso d] :
    F.kInjectiveDerivedResolutionTransition enough a a = Iso.refl _ ∧
    (F.kInjectiveDerivedResolutionTransition enough a b).symm =
      F.kInjectiveDerivedResolutionTransition enough b a ∧
    F.kInjectiveDerivedResolutionTransition enough a b ≪≫
        F.kInjectiveDerivedResolutionTransition enough b d =
      F.kInjectiveDerivedResolutionTransition enough a d := by
  refine ⟨?_, ?_, ?_⟩
  · ext
    simp [kInjectiveDerivedResolutionTransition]
  · ext
    simp [kInjectiveDerivedResolutionTransition]
  · ext
    simp [kInjectiveDerivedResolutionTransition]

/-- The change-of-resolution square commutes for every derived morphism.
Source: Stacks Tag 070Y (blueprint: lem-sf-kinjective-derived-map-computation).

Proof: step 7 of the node. Substitute T_(b',b) = c_b inverse c_b' and
M_(b,a)(h) = c_a inverse RF(h) c_b. Both paths in the square cancel to
c_a inverse RF(h) c_b'. The map computation identifies M with Q(Fg) for each
resolution choice, so this is precisely the requested intertwining square. -/
theorem kInjectiveDerivedResolutionTransition_naturality
    {N N' I I' J J' : CochainComplex C ℤ}
    [I.IsKInjective] [I'.IsKInjective] [J.IsKInjective] [J'.IsKInjective]
    (a : N ⟶ I) (a' : N ⟶ I') (b : N' ⟶ J) (b' : N' ⟶ J')
    [QuasiIso a] [QuasiIso a'] [QuasiIso b] [QuasiIso b']
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    F.kInjectiveDerivedResolutionMap enough a b h ≫
        (F.kInjectiveDerivedResolutionTransition enough b b').hom =
      (F.kInjectiveDerivedResolutionTransition enough a a').hom ≫
        F.kInjectiveDerivedResolutionMap enough a' b' h := by
  simp [kInjectiveDerivedResolutionMap, kInjectiveDerivedResolutionTransition,
    Category.assoc]

end CategoryTheory.Functor
