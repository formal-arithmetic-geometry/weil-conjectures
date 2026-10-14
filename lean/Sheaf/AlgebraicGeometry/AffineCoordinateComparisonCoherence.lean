/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.InducedCategory
public import Sheaf.Algebra.Homology.KFlatModuleBaseChange
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Composition of affine-coordinate comparisons
Source: Stacks Project, Tags 08DW, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-coordinate-comparison-coherence). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- An affine coordinate and its specified localized tilde functor. All data are supplied.
Source: the affine-coordinate square in Stacks, Tag 08DW(2).
(blueprint: lem-pc-affine-coordinate-comparison-coherence). -/
structure AffineComparisonCoordinate where
  A : CommRingCat.{u}
  X : Scheme.{u}
  σ : Spec A ≅ X
  d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X
  hd : DerivedCategory.Q ⋙ d.functor ≅
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q
  H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X
  hH : H ≅
    (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) _ _ _ _
      (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
        (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙ d.functor

/-- The acyclic-tensor criterion for a supplied model; no model is chosen.
Source: Stacks Project, Tag 06Y1.
(blueprint: lem-pc-affine-coordinate-comparison-coherence). -/
abbrev AffineComparisonKFlat (A : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
    (CochainComplex.mapBifunctor L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} A))).Acyclic

/-- Comparison on the full category of two labelled models, including cross morphisms.
Source: Stacks Project, Tag 08DW(2), natural affine comparison.
(blueprint: lem-pc-affine-coordinate-comparison-coherence). -/
abbrev AffineCoordinateComparisonFamily : Type _ :=
  ∀ (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A) (p : b.X ⟶ a.X),
    b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom →
    ∀ (M N : CochainComplex (ModuleCat.{u} a.A) ℤ),
      AffineComparisonKFlat a.A M → AffineComparisonKFlat a.A N →
      (inducedFunctor (fun q : Bool ↦ cond q M N) ⋙
        (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ b.H ≅
      inducedFunctor (fun q : Bool ↦ cond q M N) ⋙ a.H ⋙ derivedPullback p)

/-- Naturality form of one object triangle: propagation of any supplied identification.
Source: Stacks Project, Tag 0D5S, and naturality of the composition comparison.
(blueprint: lem-pc-affine-coordinate-comparison-coherence). -/
def AffineComparisonTransportTriangle
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U) (t : K ≅ B.obj J) : Prop :=
  ∀ (U' : D) (a : U ≅ U') (J' : T) (K' : V)
    (e₁ : J' ≅ L.obj U') (e₂ : K' ≅ N.obj U') (e₁₂ : K' ≅ B.obj J'),
    B.mapIso e₁.symm ≪≫ e₁₂.symm = κ.app U' ≪≫ e₂.symm →
    t ≪≫ B.mapIso (δ₁ ≪≫ L.mapIso a ≪≫ e₁.symm) ≪≫ e₁₂.symm =
      δ₂ ≪≫ N.mapIso a ≪≫ e₂.symm

omit [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem affineComparisonTransportTriangle_of_comp
    {D T V : Type*} [Category D] [Category T] [Category V]
    (L : D ⥤ T) (B : T ⥤ V) (N : D ⥤ V) (κ : L ⋙ B ≅ N)
    {U : D} {J : T} {K : V}
    (δ₁ : J ≅ L.obj U) (δ₂ : K ≅ N.obj U) (t : K ≅ B.obj J)
    (hδ : t ≪≫ B.mapIso δ₁ ≪≫ κ.app U = δ₂) :
    AffineComparisonTransportTriangle L B N κ δ₁ δ₂ t := by
  intro U' a J' K' e₁ e₂ e₁₂ he
  apply Iso.ext
  have hd := congrArg Iso.hom hδ
  have hh := congrArg Iso.hom he
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom] at hd hh ⊢
  simp only [Functor.map_comp, Category.assoc] at hd hh ⊢
  rw [hh]
  have hn := κ.hom.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (B.map (L.map a.hom)), hn]
  simpa only [Category.assoc] using
    congrArg (fun v ↦ v ≫ N.map a.hom ≫ e₂.inv) hd

/-- Affine-coordinate comparisons can be made simultaneously and respect composition.
Source: Stacks Project, Tag 08DW(2), Tag 06Y1 and Tag 0D5S.
(blueprint: lem-pc-affine-coordinate-comparison-coherence).

Proof: fix the counits used by perfectHomComposition. At a K-flat tilde complex
these are invertible: the original derived-pullback counit is invertible by tilde
K-flatness, and uniqueness of left-derived functors transfers this to the fixed
counit. Compose its inverse with the natural tilde/scalar-extension comparison.
For an affine coordinate isomorphism, pushforward is an exact equivalence with
inverse tensor pullback. Localize that equivalence and use hd to identify d;
transport the resulting comparison using hH at both ends. For each commuting
square this gives the displayed natural isomorphism on all K-flat models, then
restrict to the full induced category of the two labels. For a composable pair,
scalar extension preserves K-flatness by Tag 06Y1, so both successive counits
are invertible. The defining counit equation of perfectHomComposition identifies
successive derived comparisons with the direct one. The underived equation is
tensor reassociation: on pure tensors it sends c tensor (b tensor m) to cb tensor m.
It agrees with ModuleCat.extendScalarsComp by the pinned extension/restriction
adjunction. Transport through the coordinate equivalences; their adjacent unit
and counit factors cancel, and naturality cancels hH and its inverse. Equality
of the composite ring and scheme maps gives the two eqToIso factors below.
Thus the iso equation holds at each label, retaining every cross morphism.
There is no boundedness or flatness assumption; coincident labels, identity maps,
zero models and zero rings satisfy the same calculation. -/
theorem exists_affineCoordinateComparisonFamily :
    ∃ δ : AffineCoordinateComparisonFamily.{u, w},
      ∀ (a b c : AffineComparisonCoordinate.{u, w})
        (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
        (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
        (hr : q ≫ p = r)
        (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
        (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
        (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
        (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
        (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N),
        (c.H.mapIso
          (eqToIso (congrArg (fun t ↦
              ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj
                M) hc) ≪≫
            (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
              M) ≪≫
          (δ b c ψ q hq
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app true ≪≫
          (derivedPullback q).mapIso ((δ a b φ p hp M N hM hN).app true) ≪≫
          (perfectHomComposition q p).app (a.H.obj M) ≪≫
          (eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
            (a.H.obj M) =
          (δ a c χ r hs M N hM hN).app true) ∧
        (c.H.mapIso
          (eqToIso (congrArg (fun t ↦
              ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj
                N) hc) ≪≫
            (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
              N) ≪≫
          (δ b c ψ q hq
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
            (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
            (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app false ≪≫
          (derivedPullback q).mapIso ((δ a b φ p hp M N hM hN).app false) ≪≫
          (perfectHomComposition q p).app (a.H.obj N) ≪≫
          (eqToIso (congrArg (fun t ↦ derivedPullback t) hr)).app
            (a.H.obj N) =
          (δ a c χ r hs M N hM hN).app false) := by sorry


/-- Affine-coordinate comparisons with the naturality form of their composition law.
Source: Stacks Project, Tags 08DW(2), 06Y1 and 0D5S.
(blueprint: lem-pc-affine-coordinate-comparison-coherence).

Proof: fix the counits defining perfectHomComposition. On a K-flat tilde complex
these are invertible, by the affine K-flat computation and uniqueness of left-derived
functors. Compose the inverse counit with the natural tilde/scalar-extension comparison.
For an affine coordinate, pushforward is an exact equivalence with inverse tensor
pullback. Localize it, identify d by hd, and conjugate the comparisons by hH. Restrict
this natural construction to the full induced category on the two labels; it retains
cross morphisms even for coincident models. Scalar extension preserves K-flatness.
For composable squares the defining composite-counit equation identifies successive
comparisons with the direct comparison. Underived tensor reassociation sends a pure
tensor c tensor (b tensor m) to cb tensor m, and the pinned adjunction identifies this
with ModuleCat.extendScalarsComp. Adjacent coordinate units and counits and hH factors
cancel by naturality. The equalities hc and hr insert the displayed equality transports.
Consequently t followed by pullback of the first delta and the composition component
is the direct delta, at each label. To obtain the stated transport predicate, let a
be any supplied identification at the bottom. Expand functoriality of mapIso, use the
supplied equation on e₁,e₂,e₁₂, and move a through κ by naturality. Substitute the
composition identity just established. This proves the displayed equation without
choosing any bottom object, diagram, cocone or target model. Zero complexes, identity
maps, coincident labels, zero rings and empty spectra use the same equation. -/
theorem exists_affineCoordinateComparisonTransportFamily :
    ∃ δ : AffineCoordinateComparisonFamily.{u, w},
      ∀ (a b c : AffineComparisonCoordinate.{u, w})
        (φ : a.A →+* b.A) (ψ : b.A →+* c.A) (χ : a.A →+* c.A)
        (hc : χ = ψ.comp φ) (p : b.X ⟶ a.X) (q : c.X ⟶ b.X) (r : c.X ⟶ a.X)
        (hr : q ≫ p = r)
        (hp : b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom)
        (hq : c.σ.hom ≫ q = Spec.map (CommRingCat.ofHom ψ) ≫ b.σ.hom)
        (hs : c.σ.hom ≫ r = Spec.map (CommRingCat.ofHom χ) ≫ a.σ.hom)
        (M N : CochainComplex (ModuleCat.{u} a.A) ℤ)
        (hM : AffineComparisonKFlat a.A M) (hN : AffineComparisonKFlat a.A N),
        AffineComparisonTransportTriangle (derivedPullback p) (derivedPullback q)
          (derivedPullback r)
          (perfectHomComposition q p ≪≫ eqToIso (congrArg (fun t ↦ derivedPullback t) hr))
          ((δ a b φ p hp M N hM hN).app true)
          ((δ a c χ r hs M N hM hN).app true)
          (c.H.mapIso
            (eqToIso (congrArg (fun t ↦
                ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≪≫
              (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
                M) ≪≫
            (δ b c ψ q hq
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app true) ∧
        AffineComparisonTransportTriangle (derivedPullback p) (derivedPullback q)
          (derivedPullback r)
          (perfectHomComposition q p ≪≫ eqToIso (congrArg (fun t ↦ derivedPullback t) hr))
          ((δ a b φ p hp M N hM hN).app false)
          ((δ a c χ r hs M N hM hN).app false)
          (c.H.mapIso
            (eqToIso (congrArg (fun t ↦
                ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj N) hc) ≪≫
              (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp φ ψ) (.up ℤ)).app
                N) ≪≫
            (δ b c ψ q hq
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
              (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj N)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ M hM)
              (CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat φ N hN)).app false)
      := by
  obtain ⟨δ, hδ⟩ := exists_affineCoordinateComparisonFamily.{u, w}
  refine ⟨δ, ?_⟩
  intro a b c φ ψ χ hc p q r hr hp hq hs M N hM hN
  have hh := hδ a b c φ ψ χ hc p q r hr hp hq hs M N hM hN
  constructor
  · apply affineComparisonTransportTriangle_of_comp
    simpa only [NatIso.trans_app, Iso.trans_assoc, Functor.comp_obj,
      inducedFunctor_obj, cond_true, cond_false] using hh.1
  · apply affineComparisonTransportTriangle_of_comp
    simpa only [NatIso.trans_app, Iso.trans_assoc, Functor.comp_obj,
      inducedFunctor_obj, cond_true, cond_false] using hh.2

end AlgebraicGeometry
