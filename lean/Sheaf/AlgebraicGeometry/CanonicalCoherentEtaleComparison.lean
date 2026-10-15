/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The normalized coherent to etale comparison

Source: Stacks Project, Tags 03P2 and 03FD; the comparison of cohomological delta functors
normalized by the identity on sections
(blueprint: def-pbc-canonical-coherent-etale-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The recorded tensor-section sheaf in the coefficient universe of etale inverse image.
This is only the existing coefficient-lift functor applied to the recorded sheaf.
Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
abbrev liftedCoherentEtaleSheaf {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf F)

/-- The map on associated etale sheaves induced by a module morphism.
Its components, prescribed by the comparison theorem, determine it uniquely.
Source: Stacks Project, Tag 03P2
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def coherentEtaleMap {X : Scheme.{u}} (F G : X.Modules)
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
    (c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      @Sheaf.H _ _ (Opens.grothendieckTopology X)
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
          inferInstance (HasExt.standard _) q ≃+
        @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
          (liftedCoherentEtaleSheaf F) inferInstance inferInstance q) : Prop :=
  (∀ (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
      (φ : F ⟶ G) (q : ℕ) (x : @Sheaf.H _ _
        (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q),
    c G q (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) q x) =
      @Sheaf.H.map.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance _ _
        (coherentEtaleMap F G φ) q (c F q x)) ∧
  (∀ (F : X.Modules) [F.IsQuasicoherent]
      (x : @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) 0),
    @Sheaf.H.equiv₀.{u + 1, u + 1, u, u + 1} _ _ _ inferInstance inferInstance
        (liftedCoherentEtaleSheaf F) _ terminalIsTerminal (c F 0 x) =
      ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F
        (@Sheaf.H.equiv₀ _ _ _ inferInstance (HasExt.standard _)
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F) _ isTerminalTop x))) ∧
  ∀ (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
      (_hS : S.ShortExact)
      (hz : coherentEtaleMap S.X₁ S.X₂ S.f ≫ coherentEtaleMap S.X₂ S.X₃ S.g = 0)
      (ha : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact)
      (he : (ShortComplex.mk (coherentEtaleMap S.X₁ S.X₂ S.f)
        (coherentEtaleMap S.X₂ S.X₃ S.g) hz).ShortExact)
      (q : ℕ) (x : @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj S.X₃)
        inferInstance (HasExt.standard _) q),
    c S.X₁ (q + 1)
        (@Abelian.Ext.comp _ _ _ (HasExt.standard _) _ _ _ q 1 x
          (@ShortComplex.ShortExact.extClass _ _ _ (HasExt.standard _) _ ha)
          (q + 1) rfl) =
      @Abelian.Ext.comp _ _ _ inferInstance _ _ _ q 1 (c S.X₃ q x)
        (@ShortComplex.ShortExact.extClass _ _ _ inferInstance _ he) (q + 1) rfl

/-- Existence and uniqueness of the normalized comparison.
Source: Stacks Project, Tags 03P2, 03FD and 010S
(blueprint: def-pbc-canonical-coherent-etale-comparison).

Proof: A proper scheme over a field is quasi-compact and separated. Quasi-coherent
modules form an abelian category, and their cohomology is an effaceable delta functor:
embed into quasi-coherent injectives, using a finite affine cover to identify its
cohomology with sheaf cohomology. Etale quasi-coherent descent is exact and identifies
sections in degree zero. The comparison theorem identifies higher cohomology on the two
sites. Extend the identity on sections to a morphism of delta functors by universality.
It is invertible by the comparison theorem, and uniqueness of a delta-functor extension
proves uniqueness of the entire family, including all degrees simultaneously. -/
theorem exists_unique_normalizedCoherentEtaleComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    ∃! c : ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      @Sheaf.H _ _ (Opens.grothendieckTopology X)
          ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
          inferInstance (HasExt.standard _) q ≃+
        @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
          (liftedCoherentEtaleSheaf F) inferInstance inferInstance q,
      IsNormalizedCoherentEtaleComparison X c := by
  sorry

/-- The uniquely normalized etale comparison, rather than an arbitrary natural isomorphism.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def normalizedCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q ≃+
      @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
        (liftedCoherentEtaleSheaf F) inferInstance inferInstance q :=
  Classical.choose (exists_unique_normalizedCoherentEtaleComparison f) F q

/-- The fixed resolution comparison, with only the universe of its Ext presentation changed.
Source: Stacks Project, Tag 03FD; `moduleCohomologyExtResolutionEquiv` is the explicit
common-resolution comparison (blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def moduleAbelianCohomologyLarge (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+
      @Sheaf.H _ _ (Opens.grothendieckTopology X)
        ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F)
        inferInstance (HasExt.standard _) q :=
  letI := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  letI : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  (moduleCohomologyExtResolutionEquiv X F q).trans
    (Abelian.Ext.homAddEquiv.{u + 1, u}.trans
      Abelian.Ext.homAddEquiv.{u + 1, u + 1}.symm)

/-- The canonical etale-to-module comparison. Its inverse is the fixed resolution comparison
followed by the uniquely normalized change-of-site comparison.
Source: Stacks Project, Tags 03P2 and 03FD
(blueprint: def-pbc-canonical-coherent-etale-comparison). -/
def canonicalCoherentEtaleComparison {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    [F.IsQuasicoherent] (q : ℕ) :
    @Sheaf.H.{u + 1, u + 1, u, u + 1} _ _ X.smallEtaleTopology
        (liftedCoherentEtaleSheaf F) inferInstance inferInstance q ≃+
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :=
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
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :=
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
