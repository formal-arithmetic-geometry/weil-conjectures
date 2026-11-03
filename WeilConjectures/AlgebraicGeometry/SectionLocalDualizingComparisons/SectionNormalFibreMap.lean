/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionComparisonArrows.SectionComparisonArrows
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCanonicalInterfaces
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionAffineCoordinates
import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.RegularIdealConormalCoordinates
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule

/-! # The specified symmetric normal bundle and its counit fibre map

Source: main-20261015, sec-smooth-purity/sk-thm-dnc, opening and Local construction
(blueprint: def-trf-section-normal-fibre-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows Opposite

private def comparisonModuleMap {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (f : A ⟶ B) : A.toModule ⟶ B.toModule where
  val :=
    { app U := ModuleCat.ofHom (X := A.toModule.val.obj U)
        (Y := B.toModule.val.obj U)
        { toFun := f.right.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change A.right.obj.obj U at x
            change f.right.hom.app U (A.hom.hom.app U r * x) =
              B.hom.hom.app U r * f.right.hom.app U x
            rw [map_mul]
            congr 1
            exact congrArg (fun k ↦ k.hom.app U r) f.w }
      naturality {U V} k := by
        ext x
        exact congrArg (fun q ↦ q x) (f.right.hom.naturality k) }

private theorem algebra_isIso_of_module {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (f : A ⟶ B) [IsIso (comparisonModuleMap f)] : IsIso f := by
  have : IsIso (comparisonModuleMap f).val := by
    change IsIso ((SheafOfModules.forget S.ringCatSheaf).map (comparisonModuleMap f))
    infer_instance
  have (U : S.Opensᵒᵖ) : IsIso (f.right.hom.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have : IsIso ((comparisonModuleMap f).val.app U) := by
      change IsIso ((PresheafOfModules.evaluation _ U).map (comparisonModuleMap f).val)
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ((comparisonModuleMap f).val.app U)
  have : IsIso f.right.hom := NatIso.isIso_of_isIso_app _
  have : IsIso f.right := by
    refine ⟨⟨ObjectProperty.homMk (inv f.right.hom), ?_, ?_⟩⟩
    · apply Sheaf.hom_ext
      exact IsIso.hom_inv_id f.right.hom
    · apply Sheaf.hom_ext
      exact IsIso.inv_hom_id f.right.hom
  have : IsIso ((Under.forget _).map f) := ‹IsIso f.right›
  exact isIso_of_reflects_iso f (Under.forget _)

/-- The conormal module of a smooth closed section has rank d.
Source: sk-thm-dnc, centred coordinates
(blueprint: def-trf-section-normal-fibre-map).
Proof: the Cartesian centre square identifies the ideal with (x_1,...,x_d) in an
etale algebra over R[x]. Flat base change identifies I/I^2 with the free module
on the classes of x_j. These charts cover the section, including d=0. -/
theorem conormalRank {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d := by
  classical
  choose c hc using fun t : S ↦ SmoothSectionCentredCoordinates.exists_affineChart d g s hs t
  have hI (t : S) : Ideal.span (Set.range (c t).x) = s.ker.ideal (c t).U := by
    have h := (c t).sectionIdeal
    rw [Ideal.map_span, ← Set.range_comp] at h
    simpa only [Function.comp_def, MvPolynomial.eval₂Hom_X'] using h
  have hprecover : ⨆ t : S, s ⁻¹ᵁ (c t).U.1 = ⊤ := by
    simp_rw [(c _).sectionPreimage]
    apply eq_top_iff.mpr
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hc t⟩
  choose l b hl hb hm hf hbij using fun t : S ↦
    ConormalGradedAlgebra.regular_ideal_conormal_coordinates s (c t).U d (c t).x
      (hI t) (c t).regular
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free _
    (fun t : S ↦ (s ⁻¹ᵁ (c t).U.1).ι)
  · simpa only [Scheme.Opens.opensRange_ι] using hprecover
  · intro t
    exact ⟨Scheme.Modules.overIsoFreeEquiv _ _ _ (hf t).some⟩

/-- The actual canonical symmetric-to-conormal-graded comparison is invertible.
Source: sk-thm-dnc, centred coordinates
(blueprint: def-trf-section-normal-fibre-map).
Proof: on the centred etale charts, the coordinate regular sequence identifies the
graded algebra with the polynomial algebra on I/I^2, by the same monomials in every
degree. Flat base change and localization preserve these identifications. -/
theorem conormalSymmetricIsIso {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : IsIso (ConormalGradedAlgebra.symmetricComparison s) := by
  classical
  choose c hc using fun t : S ↦ SmoothSectionCentredCoordinates.exists_affineChart d g s hs t
  have hI (t : S) : Ideal.span (Set.range (c t).x) = s.ker.ideal (c t).U := by
    have h := (c t).sectionIdeal
    rw [Ideal.map_span, ← Set.range_comp] at h
    simpa only [Function.comp_def, MvPolynomial.eval₂Hom_X'] using h
  have hprecover : ⨆ t : S, s ⁻¹ᵁ (c t).U.1 = ⊤ := by
    simp_rw [(c _).sectionPreimage]
    apply eq_top_iff.mpr
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hc t⟩
  choose l b hl hb hm hf hbij using fun t : S ↦
    ConormalGradedAlgebra.regular_ideal_conormal_coordinates s (c t).U d (c t).x
      (hI t) (c t).regular
  have hqc : (ConormalGradedAlgebra.piece s 1).IsQuasicoherent :=
    (ConormalGradedAlgebra.presentation s).pieceQuasicoherent 1
  have hsrc := (quasiCoherentSymmetricAlgebra_affine_comparison S
    (ConormalGradedAlgebra.piece s 1)).1
  have hdst := (ConormalGradedAlgebra.presentation s).quasicoherent
  have hiso : IsIso (comparisonModuleMap (ConormalGradedAlgebra.symmetricComparison s)) := by
    apply Scheme.Modules.Hom.isIso_of_bijective_on_affine_open_cover _
      (fun t : S ↦ s ⁻¹ᵁ (c t).U.1) hprecover
      (fun t ↦ (c t).U.2.preimage s)
    intro t
    exact hbij t
  exact algebra_isIso_of_module (ConormalGradedAlgebra.symmetricComparison s)

/-- The normal bundle has the specified relative-Spec symmetric algebra as its total space.
Source: sk-thm-dnc, definition of N_s
(blueprint: def-trf-section-normal-fibre-map). -/
def normalBundle {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : Scheme.{u} :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1)

/-- The specified normal bundle is relative Spec Sym(I/I^2), with its actual projection.
Source: sk-thm-dnc, definition of N_s
(blueprint: def-trf-section-normal-fibre-map). -/
def normalProjection {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : normalBundle d g s hs ⟶ S :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)

/-- The zero section is the augmentation killing all degree-one conormal generators.
Source: sk-thm-dnc, definition of z
(blueprint: def-trf-section-normal-fibre-map). -/
def normalZero {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : S ⟶ normalBundle d g s hs :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1)

/-- The Rees cone-to-Sym comparison is fixed on every homogeneous representative.
The first factor sends a/t modulo t to the degree-one conormal class; the second is
relative Spec of the canonical symmetric-algebra comparison. No bundle isomorphism
is chosen from bare existence.
Source: sk-thm-dnc, definition of the canonical zero fibre
(blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalBundleIso {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : s.ker.normalCone ≅ normalBundle d g s hs :=
  letI := conormalRank d g s hs
  letI := conormalSymmetricIsIso d g s hs
  FiniteSmoothPurity.reesConeComparison s ≪≫
    (Over.forget S).mapIso
      ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
        (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
          (ObjectProperty.isoMk _ (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop))

/-- The canonical inclusion of Spec Sym(I/I^2) in the actual deformation at zero.
Source: sk-thm-dnc, zero fibre (blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalFibreInclusion {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : normalBundle d g s hs ⟶ s.ker.deformationSpace :=
  (normalBundleIso d g s hs).inv ≫ s.ker.normalConeToDeformationSpace

private theorem augmentation_inclusion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (ConormalGradedAlgebra.presentation i).inclusion 1 ≫
      (commAlgebraSheafModuleFunctor Z.sheaf).map
        (ConormalGradedAlgebra.augmentation i) = 0 := by
  let adj := (Scheme.Modules.exists_tensorPullbackAdjunction i).choose
  apply (adj.homEquiv (ConormalGradedAlgebra.power i 1) _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (i ⁻¹ᵁ U.unop))
    (ConormalGradedAlgebra.homogeneousClass i _ _ 1 U.unop a) = 0
  have h := (ConormalGradedAlgebra.presentation i).augmentation.exists.choose_spec
  simpa only [ConormalGradedAlgebra.augmentation, Nat.one_ne_zero, ↓reduceIte] using
    h 1 U.unop a

private theorem augmentation_comparison {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ConormalGradedAlgebra.symmetricComparison i ≫ PurityNormalBundle.augmentationToBase i =
      VectorBundleZeroSection.augmentationToBase Z (ConormalGradedAlgebra.piece i 1) := by
  apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core Z
    (ConormalGradedAlgebra.piece i 1)
    (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj) 0)
  · intro U a
    change (PurityNormalBundle.augmentationToBase i).right.hom.app (op U)
      ((ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op U) a)) = 0
    dsimp only [ConormalGradedAlgebra.symmetricComparison]
    rw [(ConormalGradedAlgebra.presentation i).symmetricComparison.exists.choose_spec]
    have h := congrArg (fun q ↦ q.val.app (op U) a) (augmentation_inclusion i)
    change (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom.hom.app (op U))
        ((ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
          (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a)) = 0
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
      (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a) = 0 at h
    rw [h, map_zero]
  · exact (exists_quasiCoherentSymmetricAlgebra_core Z
      (ConormalGradedAlgebra.piece i 1)
      (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
        (op (VectorBundleZeroSection.baseObject Z))).obj) 0).exists.choose_spec

/-- The specified normal-bundle inclusion is the Cartesian zero fibre and respects z.
Source: sk-thm-dnc, canonical pair at zero
(blueprint: def-trf-section-normal-fibre-map).
Proof: the homogeneous-normalized Rees comparison respects projection and augmentation.
The symmetric comparison fixes constants and degree-one generators, so its relative
Spec respects the projection and the zero section. Paste its isomorphism with the
actual Rees zero-fibre square. The augmentation identity gives the section equation. -/
theorem normalFibre_spec {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    IsPullback (normalFibreInclusion d g s hs) (normalProjection d g s hs)
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) ∧
    normalZero d g s hs ≫ normalFibreInclusion d g s hs =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection := by
  have := conormalRank d g s hs
  have := conormalSymmetricIsIso d g s hs
  let E := VectorBundleZeroSection.antiEquivalence S
  let A := VectorBundleZeroSection.algebraObject S d (ConormalGradedAlgebra.piece s 1)
  let B := PurityNormalBundle.algebraObject s
  let f : A ≅ B := ObjectProperty.isoMk _
    (asIso (ConormalGradedAlgebra.symmetricComparison s))
  let fOver := (ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
    ((E.inverse.mapIso f).unop)
  let fScheme := (Over.forget S).mapIso fOver
  let e := Etale.FiniteSmoothPurity.reesConeComparison s ≪≫ fScheme
  have hp : e.hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
      Scheme.Hom.normalConeProj g s := by
    change (Etale.FiniteSmoothPurity.reesConeComparison s).hom ≫
      fScheme.hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) = _
    rw [show fScheme.hom ≫ VectorBundleZeroSection.π S d
        (ConormalGradedAlgebra.piece s 1) = PurityNormalBundle.projection s from
      Over.w fOver.hom,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec s).1,
      Scheme.Hom.purityNormalProjection_eq s g hs]
  have hz : PurityNormalBundle.zeroSection s ≫ fScheme.hom =
      VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
    have h :
        E.inverse.map f.hom ≫
          E.functor.preimage ((E.counitIso.app B).hom ≫
            ObjectProperty.homMk (PurityNormalBundle.augmentationToBase s)) =
        E.functor.preimage ((E.counitIso.app A).hom ≫
          ObjectProperty.homMk (VectorBundleZeroSection.augmentationToBase S
            (ConormalGradedAlgebra.piece s 1))) := by
      apply E.functor.map_injective
      simp only [Functor.map_comp, Functor.map_preimage]
      have hn := E.counitIso.hom.naturality f.hom
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      erw [← Category.assoc, hn, Category.assoc]
      apply congrArg (fun q ↦ (E.counitIso.app A).hom ≫ q)
      apply ObjectProperty.hom_ext
      exact augmentation_comparison s
    exact congrArg (fun q ↦ q.unop.hom.left) h
  have hz' : s.normalConeZeroSection ≫ e.hom =
      VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
    rw [show e.hom = (Etale.FiniteSmoothPurity.reesConeComparison s).hom ≫
        fScheme.hom from rfl, ← Category.assoc,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec s).2.1, hz]
  have he : e = normalBundleIso d g s hs := by
    unfold normalBundleIso
    rfl
  have hp' : (normalBundleIso d g s hs).hom ≫ normalProjection d g s hs =
      Scheme.Hom.normalConeProj g s := by
    simpa only [he, normalProjection] using hp
  have hz'' : s.normalConeZeroSection ≫ (normalBundleIso d g s hs).hom =
      normalZero d g s hs := by
    simpa only [he, normalZero] using hz'
  constructor
  · apply (Scheme.Hom.isPullback_normalConeToDeformationSpace g s).of_iso
      (normalBundleIso d g s hs) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id, normalFibreInclusion,
        Iso.hom_inv_id_assoc]
    · simpa only [Iso.refl_hom, Category.comp_id] using hp'.symm
    · simp
    · simp
  · rw [normalFibreInclusion, ← hz'', Category.assoc, Iso.hom_inv_id_assoc]
    exact Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace (s := s)

/-- The finite-rank bundle projection is quasi-compact.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-normal-fibre-map).
Proof: relative Spec is affine, and affine morphisms are quasi-compact. -/
theorem normalProjectionQuasiCompact {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ)
    (g : V ⟶ S) [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : QuasiCompact (normalProjection d g s hs) := by
  have := conormalRank d g s hs
  have : IsAffineHom (normalProjection d g s hs) :=
    (VectorBundleZeroSection.over S d (ConormalGradedAlgebra.piece s 1)).property
  infer_instance

/-- Eta is the counit-defined exceptional comparison for the specified normal bundle.
Source: sk-thm-dnc, opening paragraph
(blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalFibreMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (normalProjection d g s hs)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj (family A g s) ⟶
      sectionInvariant A (normalProjection d g s hs) (normalZero d g s hs) :=
  letI := normalProjectionQuasiCompact d g s hs
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) (normalProjection d g s hs)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) (normalFibreInclusion d g s hs)
    (normalFibre_spec d g s hs).1 s.deformationSpaceSection (normalZero d g s hs)
    (normalFibre_spec d g s hs).2
end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
