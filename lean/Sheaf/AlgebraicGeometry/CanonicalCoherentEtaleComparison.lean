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
  ((moduleCohomologyExtResolutionNatIso X q).app F).addCommGroupIsoToAddEquiv.trans
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q)

private theorem iso_composite_apply
    {A B : AddCommGrpCat.{u}} {C : Type*} [AddCommGroup C]
    (e : A ≅ B) (t : B ≃+ C) (x : A) :
    e.addCommGroupIsoToAddEquiv.trans t x = t (e.hom x) := rfl

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
  exact iso_composite_apply (moduleCohomologyExtResolutionNatIso X q |>.app F)
    (@coherentExtUniverseEquiv
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      _ _ (comparisonHasExt X) (HasExt.standard _) _ _ q) x

attribute [local irreducible] moduleAbelianCohomologyLarge

private theorem iso_component_natural
    {C : Type*} [Category C] {R : Type u} [Ring R]
    {K : C ⥤ ModuleCat.{u} R} {L : C ⥤ AddCommGrpCat.{u}}
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ L)
    {F G : C} (f : F ⟶ G) (x : K.obj F) :
    (η.app G).hom ((K.map f).hom x) = (L.map f) ((η.app F).hom x) :=
  ConcreteCategory.congr_hom (η.hom.naturality f) x

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
  let U := @coherentExtUniverseEquiv
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    inferInstance inferInstance (comparisonHasExt X) (HasExt.standard _)
  have h := iso_component_natural (moduleCohomologyExtResolutionNatIso X q) φ x
  dsimp only [Functor.comp_map, Sheaf.functorH] at h
  have hu := @coherentSheafUniverseEquiv_naturality
    X.Opens inferInstance (Opens.grothendieckTopology X) inferInstance
    (comparisonHasExt X) (HasExt.standard _)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) q
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
    (((moduleCohomologyExtResolutionNatIso X q).app F).hom x)
  exact (moduleAbelianCohomologyLarge_component X G q _).trans
    ((congrArg (U _ _ q) h).trans
      (hu.trans (congrArg (CoherentEtale.sourceMap X φ q)
        (moduleAbelianCohomologyLarge_component X F q x).symm)))

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

/-- An additive coefficient endomorphism acts on module cohomology through the fixed
module/abelian resolution comparison. In particular this defines coherent Frobenius when
`φ` is sectionwise pth power; no module-linearity of `φ` is required.
Source: Stacks Project, Tags 03FD and 0A3P
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : X.Modules) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    coherentModuleGroup X F q →+ coherentModuleGroup X F q :=
  (moduleAbelianCohomologyLarge X F q).symm.toAddMonoidHom.comp
    ((@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ φ q).comp
      (moduleAbelianCohomologyLarge X F q).toAddMonoidHom)

/-- The associated structure-module sheaf, expressed through the recorded tensor-sections
construction and coefficient lift. Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
abbrev structureTensorEtaleSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  @liftedCoherentEtaleSheaf X (unit X)
    (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf))

/-- Specialize the canonical comparison to the structure module.
Source: Stacks Project, Tags 03P2, 03FD and 0A3P
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def structureCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (q : ℕ) :
    Sheaf.H (structureTensorEtaleSheaf X) q ≃+ scalarCohomology f (unit X) q :=
  @canonicalCoherentEtaleComparison k _ X f _ (unit X)
    (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)) q

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
