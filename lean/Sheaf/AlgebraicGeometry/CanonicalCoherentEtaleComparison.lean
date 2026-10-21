/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphism
public import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence
import Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists

/-!
# The normalized coherent to etale comparison

Source: Stacks Project, Tags 03P2 and 03FD; the comparison of cohomological delta functors
normalized by the identity on sections
(blueprint: def-pbc-canonical-coherent-etale-comparison).
-/

@[expose] public section

universe u v w u₀ v₀ w₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

attribute [local irreducible] tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The recorded tensor-section sheaf in the coefficient universe of etale inverse image.
This is only the existing coefficient-lift functor applied to the recorded sheaf.
Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
abbrev liftedCoherentEtaleSheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CoherentEtale.Coeff F

/-- The map on associated etale sheaves induced by a module morphism.
Its components, prescribed by the comparison theorem, determine it uniquely.
Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentEtaleMap {X : Scheme.{u}} (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    liftedCoherentEtaleSheaf F ⟶ liftedCoherentEtaleSheaf G :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (Classical.choose (etale_zariski_qcoh_comparison X) F G φ)

attribute [local irreducible] coherentEtaleMap CoherentEtale.IsNormalized
  CoherentEtale.sourceGroup CoherentEtale.targetGroup CoherentEtale.Coeff

/-- A normalized morphism of the two cohomological delta functors on quasi-coherent modules.
The source is the underlying Zariski abelian sheaf. Naturality alone is insufficient:
the displayed connecting-map condition and normalization in degree zero are essential.
Source: Stacks Project, Tags 03P2, 03FD and 010S
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def IsNormalizedCoherentEtaleComparison (X : Scheme.{u})
    (c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q) : Prop :=
  CoherentEtale.IsNormalized X (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
    (fun F _ q ↦ (c F q).toAddMonoidHom)

attribute [local semireducible] coherentEtaleMap

/-- Existence and uniqueness of the normalized comparison.
Source: Stacks Project, Tags 03P2, 03FD and 010S
(blueprint: def-pbc-canonical-coherent-etale-comparison).

Proof: Properness gives compactness and separatedness. A finite affine cover embeds each
quasi-coherent module into an acyclic quasi-coherent module, and the fixed resolution and
coefficient-universe comparisons transfer acyclicity to both cohomology theories. The
normalized additive-morphism existence theorem supplies naturality, the degree-zero unit
and all boundary squares. The terminal tensor-pullback unit is an isomorphism, proving
bijectivity in degree zero. Dimension shifting along the acyclic embeddings proves
bijectivity in every degree: use exactness on the quotient for injectivity and the two
surjective boundaries for surjectivity. The same source-boundary surjectivity proves
uniqueness by induction on the degree, simultaneously for all quasi-coherent modules. -/
theorem exists_unique_normalizedCoherentEtaleComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    ∃! c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+
        CoherentEtale.Target X F q,
      IsNormalizedCoherentEtaleComparison X c := by
  classical
  let m : CoherentEtale.Maps X := fun F G _ _ φ ↦ coherentEtaleMap F G φ
  have hm (F G : X.Modules)
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (U : X.Etale) :=
    congrArg AddCommGrpCat.uliftFunctor.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 F G φ U)
  have heff : CoherentEtale.Effaces X m := by
    apply CoherentEtale.exists_effacing_sequence f m
    unfold CoherentEtale.Coeff
    exact hm
  obtain ⟨c, hc⟩ : ∃ c : CoherentEtale.Family X, CoherentEtale.IsNormalized X m c := by
    apply CoherentEtale.exists_normalized_map f m
    unfold CoherentEtale.Coeff
    exact hm
  have hb := CoherentEtale.normalized_bijective X m heff c hc
    (fun F _ ↦ CoherentEtale.normalized_zero_bijective X m c hc F)
  let e (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :=
    AddEquiv.ofBijective (c F q) (hb F q)
  refine ⟨e, hc, ?_⟩
  intro d hd
  have hd' : CoherentEtale.IsNormalized X m
      (fun F _ q ↦ (d F q).toAddMonoidHom) := hd
  have h := CoherentEtale.normalized_unique X m heff
    (fun F _ q ↦ (d F q).toAddMonoidHom) c hd' hc
  funext F hF q
  apply AddEquiv.ext
  intro x
  exact congrArg (fun t : CoherentEtale.Family X ↦ t F q x) h

attribute [local semireducible] CoherentEtale.sourceGroup CoherentEtale.targetGroup
  CoherentEtale.Coeff

/-- Cache the additive group underlying the recorded module cohomology object.
This uses the existing derived functor without changing its construction.
Source: Stacks Project, Tag 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentModuleGroup (X : Scheme.{u})
    (F : X.Modules) (q : ℕ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}).obj ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)

/-- The uniquely normalized etale comparison, rather than an arbitrary natural isomorphism.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def normalizedCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q :=
  Classical.choose (exists_unique_normalizedCoherentEtaleComparison f) F q

/-- The canonical change of universe for an Ext presentation.
Its underlying equivalence is Mathlib’s `Ext.chgUniv`, which preserves the
represented morphism in every derived-category presentation.
Source: Mathlib's Ext.homAddEquiv; both sides use the same derived category.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentExtUniverseEquiv {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [hs : HasExt.{v} A] [hl : HasExt.{w} A] (M N : A) (q : ℕ) :
    Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q where
  toEquiv := Abelian.Ext.chgUniv
  map_add' x y := by
    let := HasDerivedCategory.standard A
    have h (z : Abelian.Ext.{v} M N q) :
        Abelian.Ext.homAddEquiv.{max u₀ v₀, w} (Abelian.Ext.chgUniv z) =
          Abelian.Ext.homAddEquiv.{max u₀ v₀, v} z :=
      Abelian.Ext.homEquiv_chgUniv z
    apply Abelian.Ext.homAddEquiv.{max u₀ v₀, w}.injective
    exact (h (x + y)).trans
      (((Abelian.Ext.homAddEquiv.{max u₀ v₀, v}).map_add x y).trans
        ((congrArg₂ (· + ·) (h x).symm (h y).symm).trans
          ((Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).map_add
            (Abelian.Ext.chgUniv x) (Abelian.Ext.chgUniv y)).symm))

/-- Universe transport represents the same morphism in any derived category.
Source: Mathlib's `Ext.homEquiv_chgUniv`.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentExtUniverseEquiv_hom
    {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [hs : HasExt.{v} A] [hl : HasExt.{w} A] [HasDerivedCategory.{w₂} A]
    {M N : A} (q : ℕ) (x : Abelian.Ext.{v} M N q) :
    Abelian.Ext.homAddEquiv.{w₂, w}
      (@coherentExtUniverseEquiv A _ _ hs hl M N q x) =
      Abelian.Ext.homAddEquiv.{w₂, v} x :=
  Abelian.Ext.homEquiv_chgUniv x

/-- Universe change commutes with postcomposition of Ext classes.
Source: Mathlib's `Ext.comp_hom` and `Ext.homEquiv_chgUniv`.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentExtUniverseEquiv_comp
    {A : Type*} [Category A] [Abelian A] [HasExt.{u} A] [HasExt.{u + 1} A]
    {M N N' : A} (q : ℕ) (x : Abelian.Ext.{u} M N q) (f : N ⟶ N') :
    @coherentExtUniverseEquiv A _ _ ‹HasExt.{u} A› ‹HasExt.{u + 1} A› M N' q
      (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      (@coherentExtUniverseEquiv A _ _ ‹HasExt.{u} A› ‹HasExt.{u + 1} A› M N q x).comp
        (Abelian.Ext.mk₀ f) (add_zero q) := by
  let := HasDerivedCategory.standard A
  apply Abelian.Ext.homAddEquiv.injective
  rw [coherentExtUniverseEquiv_hom]
  simp only [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom]
  have hh : (@coherentExtUniverseEquiv A _ _ ‹HasExt.{u} A› ‹HasExt.{u + 1} A›
      M N q x).hom = x.hom := coherentExtUniverseEquiv_hom q x
  exact congrArg (fun t ↦ t.comp
    (ShiftedHom.mk₀ (0 : ℤ) (by simp) ((DerivedCategory.singleFunctor A 0).map f))
      (zero_add (q : ℤ))) hh.symm

/-- Changing the presentation universe commutes with maps of sheaf cohomology.
Source: Mathlib's Ext composition and `Sheaf.H.map_apply`.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentSheafUniverseEquiv_naturality
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [hs : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hl : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    {F G : Sheaf J AddCommGrpCat.{u}} (q : ℕ) (f : F ⟶ G) (x : Sheaf.H.{u} F q) :
    @coherentExtUniverseEquiv _ _ _ hs hl _ G q
      (Sheaf.H.map.{u, u, u, u} f q x) =
    Sheaf.H.map.{u + 1, u, u, u} f q
      (@coherentExtUniverseEquiv _ _ _ hs hl _ F q x) := by
  simp only [Sheaf.H.map_apply]
  exact coherentExtUniverseEquiv_comp q x f

/-- Universe comparison with the native bundled cohomology group instances fixed.
Source: Mathlib's canonical Ext universe equivalence.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentSheafUniverseEquiv
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [hs : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hl : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    (q : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    (@Sheaf.functorH.{u, u, u, u} C _ J _ hs q).obj F ≃+
      (@Sheaf.functorH.{u + 1, u, u, u} C _ J _ hl q).obj F :=
  @coherentExtUniverseEquiv _ _ _ hs hl _ F q

/-- Evaluate the bundled universe comparison as the original Ext map.
Source: the defining comparison.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentSheafUniverseEquiv_apply
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [hs : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hl : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    (q : ℕ) (F : Sheaf J AddCommGrpCat.{u}) (x : @Sheaf.H.{u} C _ J F _ hs q) :
    coherentSheafUniverseEquiv J q F x =
      @coherentExtUniverseEquiv _ _ _ hs hl _ F q x := rfl

private theorem coherentSheafUniverseEquiv_native_naturality
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [hs : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hl : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    (q : ℕ) {F G : Sheaf J AddCommGrpCat.{u}} (φ : F ⟶ G)
    (x : (@Sheaf.functorH.{u, u, u, u} C _ J _ hs q).obj F) :
    coherentSheafUniverseEquiv J q G
        ((@Sheaf.functorH.{u, u, u, u} C _ J _ hs q).map φ x) =
      (@Sheaf.functorH.{u + 1, u, u, u} C _ J _ hl q).map φ
        (coherentSheafUniverseEquiv J q F x) := by
  exact coherentSheafUniverseEquiv_naturality J q φ x

/-- Compose the resolution and universe comparisons before specializing their objects.
Source: Stacks Project, Tag 03FD; composition of the recorded comparisons.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentModuleUniverseComparison
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C)
    {B : Type v} [AddCommGroup B] (U : L.obj M ≃+ B) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (K.obj M) ≃+ B :=
  (η.app M).addCommGroupIsoToAddEquiv.trans U

/-- Evaluate the composite using the recorded resolution component.
Source: the defining composite.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentModuleUniverseComparison_apply
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C)
    {B : Type v} [AddCommGroup B] (U : L.obj M ≃+ B) (x : K.obj M) :
    coherentModuleUniverseComparison η M U x = U ((η.app M).hom x) := rfl

private theorem coherentModuleUniverseComparison_naturality
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    {P : C ⥤ AddCommGrpCat.{v}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L)
    (U : ∀ M, L.obj M ≃+ P.obj M)
    (hu : ∀ {F G : C} (φ : F ⟶ G) (x : L.obj F),
      U G (L.map φ x) = P.map φ (U F x))
    {F G : C} (φ : F ⟶ G) (x : K.obj F) :
    coherentModuleUniverseComparison η G (U G) ((K.map φ).hom x) =
      P.map φ (coherentModuleUniverseComparison η F (U F) x) := by
  exact (coherentModuleUniverseComparison_apply η G (U G) _).trans
    ((congrArg (U G) (ConcreteCategory.congr_hom (η.hom.naturality φ) x)).trans
      ((hu φ _).trans (congrArg (fun z ↦ P.map φ z)
        (coherentModuleUniverseComparison_apply η F (U F) x).symm)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed resolution comparison, with only the universe of its Ext presentation changed.
The component API evaluates this composite without unfolding the construction
of the common resolution.
Source: Stacks Project, Tag 03FD; the explicit common-resolution comparison.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : X.Modules) (q : ℕ) : coherentModuleGroup X F q ≃+
      CoherentEtale.Source X F q :=
  coherentModuleUniverseComparison (moduleCohomologyExtResolutionNatIso X q) F
    (@coherentSheafUniverseEquiv X.Opens inferInstance (Opens.grothendieckTopology X)
      (comparisonHasSheafify X) (comparisonHasExt X) (HasExt.standard _) q
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F))

/-- Evaluate the fixed comparison using its recorded resolution-isomorphism component.
Source: Stacks Project, Tag 03FD; this is the defining composite.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem moduleAbelianCohomologyLarge_component (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge X F q x =
      @coherentExtUniverseEquiv
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q
        (((moduleCohomologyExtResolutionNatIso X q).app F).hom x) := by
  unfold moduleAbelianCohomologyLarge
  exact (@coherentModuleUniverseComparison_apply _ _ _ _ _ _
    (moduleCohomologyExtResolutionNatIso X q) F
    (CoherentEtale.Source X F q) inferInstance _ x).trans
      (@coherentSheafUniverseEquiv_apply X.Opens inferInstance
        (Opens.grothendieckTopology X) (comparisonHasSheafify X)
        (comparisonHasExt X) (HasExt.standard _) q _ _)

attribute [local irreducible] moduleAbelianCohomologyLarge

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed module comparison commutes with maps of coefficients.
Source: the naturality square of the common-resolution isomorphism, followed by
canonical Ext universe transport.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem moduleAbelianCohomologyLarge_naturality (X : Scheme.{u}) (q : ℕ)
    (F G : X.Modules) (φ : F ⟶ G)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge X G q
      (((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom x) =
      CoherentEtale.sourceMap X φ q (moduleAbelianCohomologyLarge X F q x) := by
  unfold moduleAbelianCohomologyLarge
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  exact coherentModuleUniverseComparison_naturality
    (P := T ⋙ @Sheaf.functorH.{u + 1, u, u, u} X.Opens inferInstance
      (Opens.grothendieckTopology X) (comparisonHasSheafify X) (HasExt.standard _) q)
    (moduleCohomologyExtResolutionNatIso X q)
    (fun M ↦ @coherentSheafUniverseEquiv X.Opens inferInstance
      (Opens.grothendieckTopology X) (comparisonHasSheafify X)
      (comparisonHasExt X) (HasExt.standard _) q (T.obj M))
    (fun φ x ↦ @coherentSheafUniverseEquiv_native_naturality X.Opens inferInstance
      (Opens.grothendieckTopology X) (comparisonHasSheafify X)
      (comparisonHasExt X) (HasExt.standard _) q _ _ (T.map φ) x) φ x

/-- The canonical etale-to-module comparison. Its inverse is the fixed resolution comparison
followed by the uniquely normalized change-of-site comparison.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def canonicalCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Target X F q ≃+ coherentModuleGroup X F q :=
  ((moduleAbelianCohomologyLarge X F q).trans
    (normalizedCoherentEtaleComparison f F q)).symm

/-- Transport an additive endomorphism along an additive equivalence.
The full additive-group structures are fixed before taking inherited projections.
Source: transport of structure; Stacks Project, Tag 0A3P.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentConjugateEndomorphism {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (f : B →+ B) : A →+ A :=
  e.symm.toAddMonoidHom.comp (f.comp e.toAddMonoidHom)

/-- Conjugate on module objects before specializing the functors.
Source: the fixed natural-isomorphism component; Stacks Project, Tag 03FD.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentModuleConjugateEndomorphism
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C)
    (a : L.obj M →+ L.obj M) : K.obj M →+ K.obj M :=
  coherentConjugateEndomorphism (ExtEdgeResolution.moduleComparisonEquiv η M) a

/-- Evaluate module conjugation by its forward and inverse components.
Source: the defining composite.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentModuleConjugateEndomorphism_apply
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L) (M : C)
    (a : L.obj M →+ L.obj M) (x : K.obj M) :
    coherentModuleConjugateEndomorphism η M a x = (η.app M).inv (a ((η.app M).hom x)) := rfl

/-- The additive coefficient action transported through the fixed resolution comparison.
Source: Stacks Project, Tags 03FD and 0A3P.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (φ : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F) :
    (RingedSpace.moduleCohomology X.toRingedSpace q).obj F →+
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj F :=
  coherentModuleConjugateEndomorphism (moduleCohomologyExtResolutionNatIso X q) F
    ((@Sheaf.functorH.{u, u, u, u} X.Opens inferInstance
      (Opens.grothendieckTopology X) (comparisonHasSheafify X) (comparisonHasExt X) q).map
      φ).hom

/-- Evaluate the action using the recorded resolution-isomorphism component.
Source: Stacks Project, Tags 03FD and 0A3P.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentAdditiveEndomorphism_apply (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (φ : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    (v : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    coherentAdditiveEndomorphism X F q φ v =
      ((moduleCohomologyExtResolutionNatIso X q).app F).inv
        (@Sheaf.H.map _ _ _ inferInstance (comparisonHasExt X) _ _ φ q
          (((moduleCohomologyExtResolutionNatIso X q).app F).hom v)) :=
  coherentModuleConjugateEndomorphism_apply (moduleCohomologyExtResolutionNatIso X q) F
    ((@Sheaf.functorH.{u, u, u, u} X.Opens inferInstance
      (Opens.grothendieckTopology X) (comparisonHasSheafify X) (comparisonHasExt X) q).map
      φ).hom v


/-- The associated structure-module sheaf, expressed through the recorded tensor-sections
construction and coefficient lift. Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
abbrev structureTensorEtaleSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  @liftedCoherentEtaleSheaf X (unit X)
    (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf))

/-- Restrict scalars on the target without changing an additive equivalence.
Source: restriction of scalars retains the underlying additive group.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentScalarEquiv {R k : Type u} [Ring R] [Field k] (M : ModuleCat.{u} R)
    (σ : k →+* R) {A : Type*} [AddCommGroup A]
    (e : A ≃+ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M) :
    letI : Module k M := Module.compHom M σ
    A ≃+ ModuleCat.of k M := e

/-- Specialize the canonical comparison to the structure module.
Source: Stacks Project, Tags 03P2, 03FD and 0A3P
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def structureCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (q : ℕ) :
    Sheaf.H (structureTensorEtaleSheaf X) q ≃+ scalarCohomology f (unit X) q :=
  coherentScalarEquiv ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (unit X))
    (scalarMap f ⊤) (@canonicalCoherentEtaleComparison k _ X f _ (unit X)
      (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) q)

/-- The same canonical comparison on a base-changed proper scheme. Properness of the
base change is supplied by stability under base change, not a new hypothesis.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def structureCoherentEtaleComparisonOfPullback
    {k K : Type u} [Field k] [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (g : Y ⟶ Spec (.of K))
    (j : Y ⟶ X) (t : Spec (.of K) ⟶ Spec (.of k)) (h : IsPullback j g f t)
    (q : ℕ) : Sheaf.H (structureTensorEtaleSheaf Y) q ≃+ scalarCohomology g (unit Y) q :=
  letI : IsProper g := MorphismProperty.of_isPullback h inferInstance
  structureCoherentEtaleComparison g q

/-- Coherent Frobenius as an additive endomorphism of the actual k-cohomology module,
when the supplied abelian coefficient map is sectionwise pth power.
Source: Stacks Project, Tags 03FD and 0A3P
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def structureCoherentFrobenius {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X)) :
    scalarCohomology f (unit X) q →+ scalarCohomology f (unit X) q :=
  coherentAdditiveEndomorphism X (unit X) q φ

end
end AlgebraicGeometry.Scheme.Modules
