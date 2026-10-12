/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.GlobalDerivedHom
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
REPAIR: Construct affineDerivedExtensionAdjunction and canonicalPullbackAdjunction
with fixed canonical data; follow coord/hollow-definitions.md (class 2), claim/adapt
users and record the definition change.
 # The affine global derived Hom base-change comparison
Source: Stacks Project, perfect.tex, Tag 0AA7 (blueprint:
def-pc-affine-global-hom-base-change-map).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The ring map of a morphism between affine schemes, using canonical section
identifications. Source: Stacks Tag 0AA7
(blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineBaseRingMap {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) : R →+* B :=
  ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso B).hom).hom

/-- Exact restriction from global sections to the affine base ring.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
abbrev affineGlobalSectionsRestriction {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :=
  ModuleCat.restrictScalars.{u} (R := R)
    (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom

/-- Underived global sections with the action of the affine base.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
abbrev affineGlobalSections {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) :=
  RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ affineGlobalSectionsRestriction f

/-- Derived global sections followed by exact restriction to the base.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
abbrev affineDerivedGlobalSections {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :=
  schemeDerivedGlobalSections X ⋙ (affineGlobalSectionsRestriction f).mapDerivedCategory

/-- The unit-compatible comparison for deriving global sections before exact restriction.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineGlobalSectionsDerivedIso {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :
    (affineGlobalSections f).rightDerivedFunctor ≅ affineDerivedGlobalSections f :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) (affineGlobalSectionsRestriction f)

/-- The two exact restrictions commute with deriving global sections on the fibre product.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineBaseChangedSectionsDerivedIso {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    (affineGlobalSections (pullback.snd f g) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctor ≅
      affineDerivedGlobalSections (pullback.snd f g) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (affineGlobalSections (pullback.snd f g))
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
    Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (pullback.snd f g))
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory

/-- Global derived Hom over the base ring, by restriction of scalars.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def schemeGlobalDerivedHomOver {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :
    (schemeDerivedCategory X)ᵒᵖ × schemeDerivedCategory X ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  schemeGlobalDerivedHom X ⋙ (affineGlobalSectionsRestriction f).mapDerivedCategory

/-- Derived extension of scalars, chosen from its adjunction with restriction
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map).
Proof: resolve complexes of R-modules by K-flat complexes and apply the existing
ModuleCat.extendScalars termwise. Extension preserves quasi-isomorphisms between
K-flat resolutions. The extension/restriction adjunction on complexes descends to
localizations: restriction is exact, and K-flat resolutions compute the left derived
extension. Thus derived extension is left adjoint to exact derived restriction. -/
theorem exists_affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    ∃ E : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B),
      Nonempty (E ⊣ (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory) := by
  sorry

/-- Derived tensor with B, chosen as the left adjoint of exact restriction.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineDerivedExtension {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  Classical.choose (exists_affineDerivedExtension g)

/-- The derived extension/restriction adjunction.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def affineDerivedExtensionAdjunction {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R) :
    affineDerivedExtension g ⊣
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory :=
  Classical.choice (Classical.choose_spec (exists_affineDerivedExtension g))

/-- The canonical pullback adjunction selected by the normalized derived-adjunction theorem.
Its Hom equivalence is pinned to the underived tensor-pullback adjunction, the shared
left-derived counit and the right-derived unit by exists_schemeDerivedAdjunction.
Source: Stacks Tags 0096 and 079W
(blueprint: def-pc-affine-global-hom-base-change-map). -/
def canonicalPullbackAdjunction {T S : Scheme.{u}} (g : T ⟶ S) :
    derivedPullback g ⊣ schemeDerivedDirectImage g :=
  Classical.choose (exists_schemeDerivedAdjunction g
    (hAdd := (Classical.choose exists_derivedPullbackComposition) g)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g))

set_option linter.unusedSectionVars false in
-- Retain the original module-category instance in the public theorem signature.
/-- Existence of tensor/internal-Hom adjunctions with the normalized evaluation counit.
The inverse Hom equivalences satisfy the shared K-flat representative equation: the
chain evaluation is specified on every summand using the recorded sheaf tensor-Hom
currying, then localized using the fixed internal-Hom factorization and K-injective
resolution map. The counit is this same uncurrying applied to the identity.
Source: Stacks, cohomology.tex, Tag 08DJ (lemma-internal-hom)
(blueprint: def-pc-affine-global-hom-base-change-map).
Proof: use exists_canonicalDerivedTensorHom from
 def-pc-canonical-derived-tensor-hom-bijection. Its naturality gives an adjunction
for each fixed K by the natural Hom-bijection construction. The adjunction's inverse
Hom equivalence is the chosen family, so its counit is that family applied to the
identity of RHom(K,L). The representative equation in IsCanonicalDerivedTensorHom
identifies this counit with localized Hom-complex evaluation: choose a K-flat
representative of RHom(K,L), represent the identity into the fixed K-injective Hom
model, and uncurry its components by the recorded sheaf tensor-Hom adjunction.
The total-tensor summand formula fixes every sign; localization and the inverse
resolution map give the required equality. Naturality transports it to all objects. -/
theorem exists_canonicalTensorHomAdjunction (S : Scheme.{u}) :
    ∃ b : ∀ K : schemeDerivedCategory S, tensorRight K ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj (op K),
      IsCanonicalDerivedTensorHom S (fun A K L => ((b K).homEquiv A L).symm) ∧
      ∀ K L : schemeDerivedCategory S,
        (b K).counit.app L =
          schemeDerivedTensorHomEquiv S
            ((derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).obj (op K, L)) K L (𝟙 _) := by
  let e := schemeDerivedTensorHomEquiv S
  have he : IsCanonicalDerivedTensorHom S e :=
    Classical.choose_spec (exists_canonicalDerivedTensorHom S)
  let core (K : schemeDerivedCategory S) : Adjunction.CoreHomEquiv
      (tensorRight K)
      ((Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj
          (op K)) :=
    { homEquiv := fun A L => (e A K L).symm
      homEquiv_naturality_left_symm := by
        intro A' A L a h
        change e A' K L (a ≫ h) = (a ▷ K) ≫ e A K L h
        have hn := he.1 A A' K K L L a (𝟙 K) (𝟙 L) h
        erw [op_id, ← CategoryTheory.prod_id', CategoryTheory.Functor.map_id,
          Category.comp_id, tensorHom_id, Category.comp_id] at hn
        exact hn
      homEquiv_naturality_right := by
        intro A L L' h c
        apply (e A K L').injective
        change e A K L' ((e A K L').symm (h ≫ c)) =
          e A K L' ((e A K L).symm h ≫
            (derivedInternalHom (Opens.grothendieckTopology S)
              S.toRingedSpace.sheaf).map (𝟙 (op K), c))
        simpa only [op_id, id_tensorHom_id, Category.comp_id,
          Category.id_comp, Equiv.apply_symm_apply] using
          (he.1 A A K K L L' (𝟙 A) (𝟙 K) c ((e A K L).symm h)).symm }
  let b (K : schemeDerivedCategory S) := Adjunction.mkOfHomEquiv (core K)
  have hb (A K L : schemeDerivedCategory S) :
      ((b K).homEquiv A L).symm = e A K L := by
    simp only [b, Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  refine ⟨b, ?_, ?_⟩
  · have hbfun : (fun A K L => ((b K).homEquiv A L).symm) = e := by
      funext A K L
      exact hb A K L
    rw [hbfun]
    exact he
  · intro K L
    exact ((b K).homEquiv_symm_id L).symm.trans
      (congrArg (fun q => q (𝟙 _)) (hb _ K L))

/-- The tensor/internal-Hom adjunction selected with the K-flat/K-injective
Hom-complex evaluation normalization, rather than from an unrestricted adjunction package.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-affine-global-hom-base-change-map). -/
def canonicalTensorHomAdjunction (S : Scheme.{u}) (K : schemeDerivedCategory S) :
    tensorRight K ⊣
      (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology S) S.toRingedSpace.sheaf)).obj (op K) :=
  (Classical.choose (exists_canonicalTensorHomAdjunction S)) K

/-- The canonical comparison is specified by four equations, not mere existence of
an arrow. Gamma satisfies the evaluation-mate equation of the shared internal-Hom
pullback adjunction; s is the identity on underived sections; c commutes with the
right-derived units (in particular on K-injective complexes). Phi is their composite.
Source: Stacks Tags 0AA7, 08I3 and 0D5T
(blueprint: def-pc-affine-global-hom-base-change-map).
Proof:
1. Use the normalized adjunction of def-pc-derived-base-change-map for a and the
   tensor comparison of def-pc-derived-pullback-tensor-comparison for t. Use the shared
   evaluation-normalized internal-Hom adjunctions for bS and bT. Pull back evaluation
   and transpose twice, as in lem-pc-derived-internal-hom-pullback-adjunction, to construct gamma.
2. On sheaves the sections of pushforward on X are sections on the inverse image
   of the whole space, namely X'. The two R-actions agree by pullback.condition;
   this gives s, acting as identity on sections, naturally in the module sheaf.
3. The composition mechanism of lem-pc-ringed-spaces-derived-direct-image-composition
   and lem-pc-derived-sections-pushforward-comparison gives c. Compute on K-injective
   resolutions and use the underived identity s; the composite right-derived units
   give the displayed equation. Exact scalar restriction commutes with derivation
   by affineGlobalSectionsDerivedIso and affineBaseChangedSectionsDerivedIso.
4. Apply restricted RΓ_X to gamma at (M,K), then c at the pulled-back internal Hom.
   This defines phi and gives the last equation. No Tor independence is used. -/
theorem exists_globalHomPullbackComparison
    {R B : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (hK : schemeDerivedQCohProperty X K) :
    ∃ (φ : (schemeGlobalDerivedHomOver f).obj (op M, K) ⟶
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.obj
          ((schemeGlobalDerivedHomOver (pullback.snd f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M),
              (derivedPullback (pullback.fst f g)).obj K))),
      ∃ (a : derivedPullback (pullback.fst f g) ⊣ schemeDerivedDirectImage (pullback.fst f g))
      (bS : ∀ K : schemeDerivedCategory X, tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf)).obj
            (op K))
      (bT : ∀ K : schemeDerivedCategory (pullback f g), tensorRight K ⊣
        (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology (pullback f g).toRingedSpace) (pullback
            f g).toRingedSpace.sheaf)).obj
            (op K))
      (t : tensor (schemeDerivedCategory X) ⋙ derivedPullback (pullback.fst f g) ≅
        (derivedPullback (pullback.fst f g)).prod (derivedPullback (pullback.fst f g)) ⋙ tensor
          (schemeDerivedCategory (pullback f g)))
      (γ : derivedInternalHom (Opens.grothendieckTopology X) X.toRingedSpace.sheaf ⟶
        (derivedPullback (pullback.fst f g)).op.prod (derivedPullback (pullback.fst f g)) ⋙
          derivedInternalHom (Opens.grothendieckTopology (pullback f g).toRingedSpace) (pullback
            f g).toRingedSpace.sheaf ⋙
            schemeDerivedDirectImage (pullback.fst f g))
      (s : RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom ⋙
          affineGlobalSections f ≅
        affineGlobalSections (pullback.snd f g) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
      (c : schemeDerivedDirectImage (pullback.fst f g) ⋙
          affineDerivedGlobalSections f ≅
        affineDerivedGlobalSections (pullback.snd f g) ⋙
          (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory),
      a = canonicalPullbackAdjunction (pullback.fst f g) ∧
      (∀ K : schemeDerivedCategory X, bS K = canonicalTensorHomAdjunction X K) ∧
      (∀ K : schemeDerivedCategory (pullback f g),
        bT K = canonicalTensorHomAdjunction (pullback f g) K) ∧
      IsCanonicalPullbackTensorComparison (pullback.fst f g)
        (fun E K => t.hom.app (E, K)) ∧
      (∀ K L : schemeDerivedCategory X,
        (a.homEquiv
            ((derivedInternalHom (Opens.grothendieckTopology X)
              X.toRingedSpace.sheaf).obj (op K, L))
            ((derivedInternalHom (Opens.grothendieckTopology (pullback f g).toRingedSpace)
              (pullback f g).toRingedSpace.sheaf).obj
                (op ((derivedPullback (pullback.fst f g)).obj K), (derivedPullback (pullback.fst
                  f g)).obj L))).symm
            (γ.app (op K, L)) =
          (bT ((derivedPullback (pullback.fst f g)).obj K)).homEquiv
            ((derivedPullback (pullback.fst f g)).obj
              ((derivedInternalHom (Opens.grothendieckTopology X)
                X.toRingedSpace.sheaf).obj (op K, L))) ((derivedPullback (pullback.fst f g)).obj L)
            (t.inv.app
                ((derivedInternalHom (Opens.grothendieckTopology X)
                  X.toRingedSpace.sheaf).obj (op K, L), K) ≫
              (derivedPullback (pullback.fst f g)).map ((bS K).counit.app L))) ∧
      (∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
          (x : (affineGlobalSections (pullback.snd f g)).obj F),
        (s.hom.app F) x = x) ∧
      (∀ J : HomotopyCategory
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
        (Functor.rightDerivedFunctorCompUnit
            (RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom)
            (affineGlobalSections f)).app J ≫
          (affineGlobalSectionsDerivedIso f).hom.app
            ((schemeDerivedDirectImage (pullback.fst f g)).obj (DerivedCategory.Qh.obj J)) ≫
          c.hom.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
          (affineGlobalSections (pullback.snd f g) ⋙
            ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
          (affineBaseChangedSectionsDerivedIso f g).hom.app (DerivedCategory.Qh.obj J)) ∧
      φ = (affineDerivedGlobalSections f).map (γ.app (op M, K)) ≫
        c.hom.app
          ((derivedInternalHom (Opens.grothendieckTopology (pullback f g).toRingedSpace)
            (pullback f g).toRingedSpace.sheaf).obj
              (op ((derivedPullback (pullback.fst f g)).obj M),
                (derivedPullback (pullback.fst f g)).obj K)) := by
  sorry

/-- Restricted global sections of gamma followed by the canonical pushforward comparison.
The chosen phi satisfies all equations of exists_globalHomPullbackComparison.
Source: Stacks Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map). -/
def globalHomPullbackComparison
    {R B : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (hK : schemeDerivedQCohProperty X K) :
    (schemeGlobalDerivedHomOver f).obj (op M, K) ⟶
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.obj
        ((schemeGlobalDerivedHomOver (pullback.snd f g)).obj
          (op ((derivedPullback (pullback.fst f g)).obj M),
            (derivedPullback (pullback.fst f g)).obj K)) :=
  Classical.choose (exists_globalHomPullbackComparison f g M K hM hK)

/-- The canonical affine global RHom comparison: the adjoint, under derived extension of
scalars along `g` and exact restriction of scalars, of the global RHom map induced by
`Lg_X^*`. Source: Stacks, Tag 0AA7 (blueprint: def-pc-affine-global-hom-base-change-map).
-/
def affineGlobalHomBaseChangeMap
    {R B : CommRingCat.{u}} {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (M K : schemeDerivedCategory X) (hM : Scheme.IsPerfect X M)
    (hK : schemeDerivedQCohProperty X K) :
    (affineDerivedExtension g).obj ((schemeGlobalDerivedHomOver f).obj (op M, K)) ⟶
      (schemeGlobalDerivedHomOver (pullback.snd f g)).obj
        (op ((derivedPullback (pullback.fst f g)).obj M),
          (derivedPullback (pullback.fst f g)).obj K) :=
  (affineDerivedExtensionAdjunction g).homEquiv
    ((schemeGlobalDerivedHomOver f).obj (op M, K))
    ((schemeGlobalDerivedHomOver (pullback.snd f g)).obj
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj K)) |>.symm
    (globalHomPullbackComparison f g M K hM hK)

end AlgebraicGeometry
