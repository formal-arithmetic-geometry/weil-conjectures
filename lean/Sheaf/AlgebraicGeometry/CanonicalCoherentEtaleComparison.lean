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

universe u v w u₀ v₀
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
abbrev liftedCoherentEtaleSheaf {X : Scheme.{u}} (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CoherentEtale.Coeff F

/-- The map on associated etale sheaves induced by a module morphism.
Its components, prescribed by the comparison theorem, determine it uniquely.
Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentEtaleMap {X : Scheme.{u}} (F G : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    liftedCoherentEtaleSheaf F ⟶ liftedCoherentEtaleSheaf G :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
    (Classical.choose (etale_zariski_qcoh_comparison X) F G φ)

/-- A normalized morphism of the two cohomological delta functors on quasi-coherent modules.
The source is the underlying Zariski abelian sheaf. Naturality alone is insufficient:
the displayed connecting-map condition and normalization in degree zero are essential.
Source: Stacks Project, Tags 03P2, 03FD and 010S
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def IsNormalizedCoherentEtaleComparison (X : Scheme.{u})
    (c : ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q) : Prop :=
  CoherentEtale.IsNormalized X (fun F G _ _ φ ↦ coherentEtaleMap F G φ)
    (fun F _ q ↦ (c F q).toAddMonoidHom)

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
    ∃! c : ∀ (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ),
      CoherentEtale.Source X F q ≃+
        CoherentEtale.Target X F q,
      IsNormalizedCoherentEtaleComparison X c := by
  classical
  let m : CoherentEtale.Maps X := fun F G _ _ φ ↦ coherentEtaleMap F G φ
  have hm (F G : SheafOfModules.{u} X.ringCatSheaf)
      [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (U : X.Etale) :
      (m F G φ).hom.app (op U) =
        AddCommGrpCat.uliftFunctor.map (((tensorPullback U.hom).map φ).app ⊤) := by
    change AddCommGrpCat.uliftFunctor.map
      ((Classical.choose (etale_zariski_qcoh_comparison X) F G φ).hom.app (op U)) = _
    exact congrArg AddCommGrpCat.uliftFunctor.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 F G φ U)
  have heff := CoherentEtale.exists_effacing_sequence f m hm
  obtain ⟨c, hc⟩ := CoherentEtale.exists_normalized_map f m hm
  have hb := CoherentEtale.normalized_bijective X m heff c hc
    (fun F _ ↦ CoherentEtale.normalized_zero_bijective X m c hc F)
  let e (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent] (q : ℕ) :=
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

/-- Cache the additive group underlying the recorded module cohomology object.
This uses the existing derived functor without changing its construction.
Source: Stacks Project, Tag 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentModuleGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  (RingedSpace.moduleCohomology X.toRingedSpace q ⋙
    forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).obj F

/-- The uniquely normalized etale comparison, rather than an arbitrary natural isomorphism.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def normalizedCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Source X F q ≃+ CoherentEtale.Target X F q :=
  Classical.choose (exists_unique_normalizedCoherentEtaleComparison f) F q

/-- The canonical change of universe for an Ext presentation.
Source: Mathlib's Ext.homAddEquiv; both sides use the same derived category.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentExtUniverseEquiv {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasExt.{v} A] [HasExt.{w} A] (M N : A) (q : ℕ) :
    Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q :=
  letI := HasDerivedCategory.standard A
  (Abelian.Ext.homAddEquiv.{max u₀ v₀, v}).trans
    (Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).symm

/-- Changing Ext universes commutes with coefficient postcomposition.
Source: Mathlib's Ext.homAddEquiv and Ext.comp_hom.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentExtUniverse_postcomp
    {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [HasExt.{v} A] [HasExt.{w} A] {M N N' : A} (f : N ⟶ N') (q : ℕ)
    (x : Abelian.Ext.{v} M N q) :
    (coherentExtUniverseEquiv.{v, w, u₀, v₀} M N' q :
      Abelian.Ext.{v} M N' q ≃+ Abelian.Ext.{w} M N' q)
        (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      ((coherentExtUniverseEquiv.{v, w, u₀, v₀} M N q :
        Abelian.Ext.{v} M N q ≃+ Abelian.Ext.{w} M N q) x).comp
          (Abelian.Ext.mk₀ f) (add_zero q) := by
  let := HasDerivedCategory.standard A
  have hu (N : A) (y : Abelian.Ext.{v} M N q) :
      ((coherentExtUniverseEquiv.{v, w, u₀, v₀} M N q) y).hom =
        y.hom := by
    change Abelian.Ext.homAddEquiv
      (Abelian.Ext.homAddEquiv.symm (Abelian.Ext.homAddEquiv y)) = _
    exact AddEquiv.apply_symm_apply _ _
  apply (Abelian.Ext.homAddEquiv.{max u₀ v₀, w}).injective
  change (_ : Abelian.Ext.{w} M N' q).hom = (_ : Abelian.Ext.{w} M N' q).hom
  rw [hu, Abelian.Ext.comp_hom, Abelian.Ext.comp_hom, hu,
    Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom]

-- The independent Ext sizes occur in the two group fields of this record.
set_option linter.checkUnivs false in
/-- Two Ext presentations with their coefficient maps and their canonical compatibility.
Source: Mathlib's Ext functors and Ext.homAddEquiv.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
structure CoherentExtPresentation {A : Type u₀} [Category.{v₀} A] (N : A) where
  small : AddCommGrpCat.{v}
  large : AddCommGrpCat.{w}
  smallMap : (N ⟶ N) → (small →+ small)
  largeMap : (N ⟶ N) → (large →+ large)
  change : small ≃+ large
  naturality : ∀ (φ : N ⟶ N) (x : small),
    change (smallMap φ x) = largeMap φ (change x)

/-- Construct both presentations together, before specializing the coefficient category.
Every field is the existing Ext construction; naturality is coefficient postcomposition.
Source: Mathlib's Ext functors and Ext.homAddEquiv.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentExtPresentationData {A : Type u₀} [Category.{v₀} A] [Abelian A]
    [h₁ : HasExt.{v} A] [h₂ : HasExt.{w} A] (M N : A) (q : ℕ) :
    CoherentExtPresentation N where
  small := AddCommGrpCat.of (Abelian.Ext.{v} M N q)
  large := AddCommGrpCat.of (Abelian.Ext.{w} M N q)
  smallMap φ := (@Abelian.Ext.mk₀ _ _ _ h₁ _ _ φ).postcomp M (add_zero q)
  largeMap φ := (@Abelian.Ext.mk₀ _ _ _ h₂ _ _ φ).postcomp M (add_zero q)
  change := @coherentExtUniverseEquiv A _ _ h₁ h₂ M N q
  naturality φ x := @coherentExtUniverse_postcomp A _ _ h₁ h₂ _ _ _ φ q x

/-- Cache the small Ext-size proof for the coherent comparison.
Source: Mathlib's Grothendieck abelian category theorem.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
theorem coherentCohomologyHasExt (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  infer_instance

/-- The two concrete presentations for the underlying Zariski abelian sheaf.
Source: Stacks Project, Tag 03FD; Mathlib's constant-integer-sheaf Ext construction.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentExtPresentationFor (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    CoherentExtPresentation ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
  @coherentExtPresentationData
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    inferInstance inferInstance (coherentCohomologyHasExt X) (HasExt.standard _)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q

/-- The small Ext presentation of the underlying Zariski abelian cohomology.
Source: Stacks Project, Tag 03FD.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentSmallAbelianGroup (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) : AddCommGrpCat.{u} :=
  (coherentExtPresentationFor X F q).small

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Cache the existing fixed resolution comparison with its small Ext groups explicit.
No comparison map is selected or changed.
Source: Stacks Project, Tag 03FD.
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentSmallResolutionEquiv (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ coherentSmallAbelianGroup X F q :=
  moduleCohomologyExtResolutionEquiv X F q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed resolution comparison, with only the universe of its Ext presentation changed.
Source: Stacks Project, Tag 03FD; `moduleCohomologyExtResolutionEquiv` is the explicit
common-resolution comparison (blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def moduleAbelianCohomologyLarge (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    coherentModuleGroup X F q ≃+ CoherentEtale.Source X F q :=
  (coherentSmallResolutionEquiv X F q).trans (coherentExtPresentationFor X F q).change

/-- The canonical etale-to-module comparison. Its inverse is the fixed resolution comparison
followed by the uniquely normalized change-of-site comparison.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def canonicalCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : SheafOfModules.{u} X.ringCatSheaf)
    [F.IsQuasicoherent] (q : ℕ) :
    CoherentEtale.Target X F q ≃+ coherentModuleGroup X F q :=
  ((moduleAbelianCohomologyLarge X F q).trans
    (normalizedCoherentEtaleComparison f F q)).symm

/-- An additive coefficient endomorphism acts on module cohomology through the fixed
module/abelian resolution comparison. In particular this defines coherent Frobenius when
`φ` is sectionwise pth power; no module-linearity of `φ` is required.
Source: Stacks Project, Tags 03FD and 0A3P
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentAdditiveEndomorphism (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf) (q : ℕ)
    (φ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) :
    coherentModuleGroup X F q →+ coherentModuleGroup X F q :=
  let D := coherentExtPresentationFor X F q
  let e := (coherentSmallResolutionEquiv X F q).trans D.change
  e.symm.toAddMonoidHom.comp ((D.largeMap φ).comp e.toAddMonoidHom)

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
