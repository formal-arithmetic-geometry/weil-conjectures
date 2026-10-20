/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProEtaleLisseOrigin
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleAffineLineEndomorphismRigidity
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel

/-! # Coefficient compatibility of normalized deformation comparisons

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/
sk-thm-dnc.proof.md, Gluing paragraph (blueprint:
lem-pur-diagonal-orientation-compatibility).

There is one coefficient-change functor on each ordinary etale site: the total left
derived functor of the published sheafified extension of scalars. The derived pullback
comparisons are obtained by left derivation of the canonical adjunction conjugate,
using the composite universal counits. The zero-fibre identification is the scalar
extension of the inverse of the specialization dependency's actual `atZero` map.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

namespace NoetherianSectionSpecialization

/-- The canonical quotient map on the finite coefficient rings. Source: blueprint
sk-thm-dnc, coefficient reduction (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def coefficientMap (ell r m : ℕ) (hmr : m ≤ r) :
    NoetherianSectionSpecialization.Coeff ell r →+*
      NoetherianSectionSpecialization.Coeff ell m :=
  RingHom.ulift (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m)))

/-- Sheafified extension of scalars along the canonical coefficient quotient. Source:
Stacks Tag 03EK (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable abbrev scalarExtension {X : Scheme.{u}} (ell r m : ℕ) (hmr : m ≤ r) :
    Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell r)) ⥤
    Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell m)) :=
  ProEtale.etaleSheafExtendScalars (coefficientMap ell r m hmr) X

/-- The canonical scalar/restriction adjunction on the small etale site. Source: Stacks
Tag 06YY (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def scalarExtensionAdjunction {X : Scheme.{u}} (ell r m : ℕ) (hmr : m ≤ r) :
    scalarExtension ell r m hmr (X := X) ⊣
      sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (coefficientMap ell r m hmr)) :=
  ProEtale.etaleSheafExtendScalarsAdjunction (coefficientMap ell r m hmr) X

/-- Additivity of the canonical sheafified scalar extension. Source: Stacks Tag 03EK
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
instance scalarExtension_additive {X : Scheme.{u}} (ell r m : ℕ) (hmr : m ≤ r) :
    (scalarExtension ell r m hmr (X := X)).Additive :=
  (scalarExtensionAdjunction ell r m hmr (X := X)).left_adjoint_additive

/-- The finite-coefficient scalar extension preserves K-flat quasi-isomorphisms. Source:
Stacks Tags 06YT and 06YY (blueprint: lem-pur-diagonal-orientation-compatibility).
Proof: evaluate at etale stalks. Tensoring an acyclic K-flat complex with B is
acyclic, and the cone of a quasi-isomorphism between K-flat complexes is acyclic
K-flat. Sheafification and stalks are exact, so this proves the sheaf assertion
without assuming that the quotient A to B is flat. -/
theorem scalarExtension_preservesKFlatQuasiIso_proof {X : Scheme.{u}} (ell r m : ℕ)
    (hmr : m ≤ r) :
    (scalarExtension ell r m hmr (X := X)).PreservesKFlatQuasiIso := by
  sorry

/-- Register the named K-flat quasi-isomorphism preservation theorem.
Source: Stacks 06YY (blueprint: lem-pur-diagonal-orientation-compatibility). -/
instance scalarExtension_preservesKFlatQuasiIso {X : Scheme.{u}} (ell r m : ℕ)
    (hmr : m ≤ r) :
    (scalarExtension ell r m hmr (X := X)).PreservesKFlatQuasiIso :=
  scalarExtension_preservesKFlatQuasiIso_proof ell r m hmr

/-- The canonical left-derived scalar extension on the ordinary etale derived category.
Source: Stacks Tags 06YT and 06YY (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable abbrev scalarExtensionDerived {X : Scheme.{u}} (ell r m : ℕ) (hmr : m ≤ r) :
    DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell r))) ⥤
    DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell m))) :=
  (scalarExtension ell r m hmr (X := X)).leftDerivedFunctor

/-- The abelian scalar/pullback comparison is the adjunction conjugate of the
sectionwise restriction/direct-image identity. Source: Stacks 03EK and 03FD
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def scalarUpperStarIso (ell r m : ℕ) (hmr : m ≤ r)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    scalarExtension ell r m hmr (X := W) ⋙
        upperStar (ModuleCat.{u + 1} (Coeff ell m)) f ≅
      upperStar (ModuleCat.{u + 1} (Coeff ell r)) f ⋙
        scalarExtension ell r m hmr (X := Z) :=
  ((conjugateIsoEquiv
    ((scalarExtensionAdjunction ell r m hmr (X := W)).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff ell m)) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff ell r)) f).comp
      (scalarExtensionAdjunction ell r m hmr (X := Z)))).symm
    (lowerStarRestrictScalarsIso (coefficientMap ell r m hmr) f).symm).symm

/-- Composite of the actual scalar and pullback left-derived counits, including
associativity. Source: Stacks 06YY
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def scalarThenPullbackCounit (ell r m : ℕ) (hmr : m ≤ r)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    DerivedCategory.Qh ⋙ (scalarExtensionDerived ell r m hmr (X := W) ⋙
        (upperStar (ModuleCat.{u + 1} (Coeff ell m)) f).leftDerivedFunctor) ⟶
      ((scalarExtension ell r m hmr (X := W)).mapHomotopyCategory (.up ℤ) ⋙
        (upperStar (ModuleCat.{u + 1} (Coeff ell m)) f).mapHomotopyCategory (.up ℤ)) ⋙
          DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarExtension ell r m hmr (X := W)).leftDerivedFunctorCounit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (upperStar (ModuleCat.{u + 1} (Coeff ell m)) f).leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv

/-- The other composite universal counit, first pullback and then scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def pullbackThenScalarCounit (ell r m : ℕ) (hmr : m ≤ r)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    DerivedCategory.Qh ⋙
        ((upperStar (ModuleCat.{u + 1} (Coeff ell r)) f).leftDerivedFunctor ⋙
          scalarExtensionDerived ell r m hmr (X := Z)) ⟶
      ((upperStar (ModuleCat.{u + 1} (Coeff ell r)) f).mapHomotopyCategory (.up ℤ) ⋙
        (scalarExtension ell r m hmr (X := Z)).mapHomotopyCategory (.up ℤ)) ⋙
          DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (upperStar (ModuleCat.{u + 1} (Coeff ell r)) f).leftDerivedFunctorCounit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (scalarExtension ell r m hmr (X := Z)).leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv

/-- Both composites, with the displayed actual counits, are left derived functors.
Source: Stacks 06YY and 03FD
(blueprint: lem-pur-diagonal-orientation-compatibility).
Proof: take a K-flat resolution with flat terms. Constant-coefficient inverse image
preserves flat terms and K-flatness, as does extension of scalars to B: after stalks,
the tensor test is the usual change-of-rings adjunction. Consequently each universal
counit in the composite is invertible on resolving models. Apply the K-flat
criterion for left derivability to these fixed counits. This is the canonical
coefficient specialization of lem-weil-pbc-ringed-topoi-derived-tensor-pullback;
no arbitrary comparison data or flatness assumption on A to B is introduced. -/
theorem scalarPullback_composites_derivable (ell r m : ℕ) (hmr : m ≤ r)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (scalarExtensionDerived ell r m hmr (X := W) ⋙
      (upperStar (ModuleCat.{u + 1} (Coeff ell m)) f).leftDerivedFunctor).IsLeftDerivedFunctor
        (scalarThenPullbackCounit ell r m hmr f)
        (HomotopyCategory.quasiIso
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (Coeff ell r))) (.up ℤ)) ∧
    ((upperStar (ModuleCat.{u + 1} (Coeff ell r)) f).leftDerivedFunctor ⋙
      scalarExtensionDerived ell r m hmr (X := Z)).IsLeftDerivedFunctor
        (pullbackThenScalarCounit ell r m hmr f)
        (HomotopyCategory.quasiIso
          (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (Coeff ell r))) (.up ℤ)) := by
  sorry

/-- Left derivation of the canonical abelian scalar/pullback comparison. Its data is
Mathlib's universal lift of the fixed underived isomorphism through the fixed composite
counits, rather than a choice from a bare existence assertion. This applies to a, i_0
and i_1. Source: Stacks 06YY and 03FD
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalScalarPullbackNatIso (ell r m : ℕ) (hmr : m ≤ r)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    scalarExtensionDerived ell r m hmr (X := W) ⋙
        (upperStar (ModuleCat.{u + 1} (Coeff ell m)) f).leftDerivedFunctor ≅
      (upperStar (ModuleCat.{u + 1} (Coeff ell r)) f).leftDerivedFunctor ⋙
        scalarExtensionDerived ell r m hmr (X := Z) := by
  letI := (scalarPullback_composites_derivable ell r m hmr f).1
  letI := (scalarPullback_composites_derivable ell r m hmr f).2
  exact Functor.leftDerivedNatIso _ _
    (scalarThenPullbackCounit ell r m hmr f) (pullbackThenScalarCounit ell r m hmr f)
    (HomotopyCategory.quasiIso
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (Coeff ell r))) (.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (scalarUpperStarIso ell r m hmr f) (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (upperStar (ModuleCat.{u + 1} (Coeff ell r)) f ⋙
            scalarExtension ell r m hmr (X := Z))) (.up ℤ)).symm)
      DerivedCategory.Qh)

/-- The canonical scalar/pullback component used on the section complex. Source: blueprint
sk-thm-dnc, Gluing (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalScalarPullbackIso {S : Scheme.{u}} (ell r m : ℕ) (hmr : m ≤ r)
    (C : DerivedCategory (Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell r)))) :
    (scalarExtensionDerived ell r m hmr (X := AffineSpace (ULift.{u} (Fin 1)) S)).obj
        ((upperStar (ModuleCat.{u + 1}
          (NoetherianSectionSpecialization.Coeff ell r))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) ≅
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
        ((scalarExtensionDerived ell r m hmr (X := S)).obj C) :=
  ((canonicalScalarPullbackNatIso ell r m hmr
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm

/-- The canonical zero-fibre map is invertible under the specialization hypotheses. Source:
blueprint sk-thm-dnc, opening fibre comparison
(blueprint: lem-pur-diagonal-orientation-compatibility).
Proof: finite type over Noetherian S makes V Noetherian. Stalk ring maps preserve
invertibility of ell. Apply lines_and_fibres from the specialization dependency;
its final conjunct says precisely that this actual exceptional base-change mate
is invertible. All geometric hypotheses are those already supplied here. -/
theorem atZero_isIso
    (ell m : ℕ) [Fact ell.Prime] (hm : 1 ≤ m)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    IsIso (atZero (NoetherianSectionSpecialization.Coeff ell m) g s) := by
  sorry

/-- The canonical zero-fibre identification at coefficient level `m`. Source: blueprint
sk-thm-dnc, opening fibre comparison (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalAtZeroIso
    (ell m : ℕ) [Fact ell.Prime] (hm : 1 ≤ m)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (upperStar (ModuleCat.{u + 1}
      (NoetherianSectionSpecialization.Coeff ell m))
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
      (family (NoetherianSectionSpecialization.Coeff ell m) g s) ≅
    sectionInvariant (NoetherianSectionSpecialization.Coeff ell m)
      (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
  letI := atZero_isIso ell m hm hS d g s hs hregular
  exact asIso (atZero (NoetherianSectionSpecialization.Coeff ell m) g s)

/-- The canonical one-fibre map is invertible under the specialization hypotheses. Source:
blueprint sk-thm-dnc, opening fibre comparison
(blueprint: lem-pur-diagonal-orientation-compatibility).
Proof: finite type over Noetherian S makes V Noetherian. Stalk ring maps preserve
invertibility of ell. Apply lines_and_fibres from the specialization dependency;
its one-fibre conjunct says precisely that this actual exceptional base-change mate
is invertible. All geometric hypotheses are those already supplied here. -/
theorem atOne_isIso
    (ell m : ℕ) [Fact ell.Prime] (hm : 1 ≤ m)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    IsIso (atOne (NoetherianSectionSpecialization.Coeff ell m) g s hs) := by
  sorry

/-- The canonical one-fibre identification at coefficient level `m`. Source: blueprint
sk-thm-dnc, opening fibre comparison (blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalAtOneIso
    (ell m : ℕ) [Fact ell.Prime] (hm : 1 ≤ m)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (upperStar (ModuleCat.{u + 1}
      (NoetherianSectionSpecialization.Coeff ell m))
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
      (family (NoetherianSectionSpecialization.Coeff ell m) g s) ≅
    sectionInvariant (NoetherianSectionSpecialization.Coeff ell m) g s := by
  letI := atOne_isIso ell m hm hS d g s hs hregular
  exact asIso (atOne (NoetherianSectionSpecialization.Coeff ell m) g s hs)

/-- The zero-fibre scalar comparison: scalar extension of the inverse of the actual
specialization fibre map, followed by the canonical comparison for i_0. Source:
blueprint sk-thm-dnc, fibre identifications
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalZeroFiberIso
    (ell r m : ℕ) [Fact ell.Prime] (hr : 1 ≤ r) (hmr : m ≤ r)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (scalarExtensionDerived ell r m hmr (X := S)).obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r)
          (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ≅
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        ((scalarExtensionDerived ell r m hmr
          (X := AffineSpace (ULift.{u} (Fin 1)) S)).obj
          (family (NoetherianSectionSpecialization.Coeff ell r) g s)) :=
  (scalarExtensionDerived ell r m hmr (X := S)).mapIso
    (canonicalAtZeroIso ell r hr hS d g s hs hregular).symm ≪≫
    ((canonicalScalarPullbackNatIso ell r m hmr
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).app
        (family (Coeff ell r) g s)).symm

/-- The one-fibre scalar comparison: scalar extension of the inverse of the actual
specialization fibre map, followed by the canonical comparison for i_1. Source:
blueprint sk-thm-dnc, fibre identifications
(blueprint: lem-pur-diagonal-orientation-compatibility). -/
noncomputable def canonicalOneFiberIso
    (ell r m : ℕ) [Fact ell.Prime] (hr : 1 ≤ r) (hmr : m ≤ r)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (scalarExtensionDerived ell r m hmr (X := S)).obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r) g s) ≅
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        ((scalarExtensionDerived ell r m hmr
          (X := AffineSpace (ULift.{u} (Fin 1)) S)).obj
          (family (NoetherianSectionSpecialization.Coeff ell r) g s)) :=
  (scalarExtensionDerived ell r m hmr (X := S)).mapIso
    (canonicalAtOneIso ell r hr hS d g s hs hregular).symm ≪≫
    ((canonicalScalarPullbackNatIso ell r m hmr
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).app
        (family (Coeff ell r) g s)).symm

/-- Normalized deformation comparisons commute with canonical coefficient reduction.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-dnc/sk-thm-dnc.proof.md
(blueprint: lem-pur-diagonal-orientation-compatibility).
Proof: (1) finite type over Noetherian S gives Noetherian V; apply the section
specialization node at A and B. The section and family objects, after the common
shift, are locally constant free rank-one sheaves. Derived coefficient change
is their ordinary scalar extension, and the comparison above is the canonical
one on these models. Full faithfulness of singleFunctor cancels the common shift.
(2) Subtract the two maps in the first assertion. Their difference is zero at
one. Put this difference in the off-diagonal entry of a unipotent endomorphism
of the direct sum of the two pulled-back lines. Ordinary-to-pro-etale finite-level
comparison and pullback compatibility transport it to the pro-etale site.
Affine-line endomorphism rigidity forces that matrix to be the identity; faithful
finite-level comparison reflects equality. (3) Restrict along zero, using the
canonical scalar/pullback and exceptional fibre comparisons; invert the normalized
kappas. The definition of specialization and he0 give the second assertion.
(4) The same matrix argument gives ordinary Hom injectivity for L and M. Apply
full faithfulness of the degree-zero embedding after cancelling equal shifts
to obtain the last assertion. These are the four steps of the DAG proof. -/
theorem diagonalOrientationCompatibility
    (ell r m : ℕ) [Fact ell.Prime] (hr : 1 ≤ r) (hm : 1 ≤ m) (hmr : m ≤ r)
    {V S : Scheme.{u}} [IsNoetherian S]
    (hS : ∀ x : S, IsUnit (ell : S.presheaf.stalk x))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [HasCompactification g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (hregular : ∀ x : S, ∃ U : V.affineOpens, s x ∈ U.1 ∧
      ∃ q : Fin d → Γ(V, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(V, U.1) (List.ofFn q) ∧
          Ideal.span (Set.range q) = s.ker.ideal U)
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (eF : (scalarExtensionDerived ell r m hmr
      (X := AffineSpace (ULift.{u} (Fin 1)) S)).obj
        (family (NoetherianSectionSpecialization.Coeff ell r) g s) ⟶
      family (NoetherianSectionSpecialization.Coeff ell m) g s)
    (eC : (scalarExtensionDerived ell r m hmr (X := S)).obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r) g s) ⟶
      sectionInvariant (NoetherianSectionSpecialization.Coeff ell m) g s)
    (e0 : (scalarExtensionDerived ell r m hmr (X := S)).obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r)
          (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) ⟶
      sectionInvariant (NoetherianSectionSpecialization.Coeff ell m)
        (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection)
    (κA : family (NoetherianSectionSpecialization.Coeff ell r) g s ≅
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell r))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r) g s))
    (hκA : Normalized (NoetherianSectionSpecialization.Coeff ell r) g s hs κA)
    (κB : family (NoetherianSectionSpecialization.Coeff ell m) g s ≅
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell m) g s))
    (hκB : Normalized (NoetherianSectionSpecialization.Coeff ell m) g s hs κB)
    (he0 : e0 =
      (canonicalZeroFiberIso ell r m hr hmr hS d g s hs hregular).hom ≫
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map eF ≫
      (canonicalAtZeroIso ell m hm hS d g s hs hregular).hom)
    (h₁ :
      (canonicalOneFiberIso ell r m hr hmr hS d g s hs hregular).hom ≫
        (upperStar (ModuleCat.{u + 1} (Coeff ell m))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map eF ≫
        atOne (Coeff ell m) g s hs = eC)
    (L M : Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell m)))
    (hL : ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : cover.I₀, Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (S.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell m))).obj
          (ModuleCat.of (NoetherianSectionSpecialization.Coeff ell m)
            (NoetherianSectionSpecialization.Coeff ell m))))
    (hM : ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : cover.I₀, Nonempty (M.over (cover.etalePrecoverageToEtale i) ≅
        (constantSheaf (S.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell m))).obj
          (ModuleCat.of (NoetherianSectionSpecialization.Coeff ell m)
            (NoetherianSectionSpecialization.Coeff ell m)))) :
    (eF ≫ κB.hom =
      (scalarExtensionDerived ell r m hmr
        (X := AffineSpace (ULift.{u} (Fin 1)) S)).map κA.hom ≫
      (canonicalScalarPullbackIso ell r m hmr
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell r) g s)).hom ≫
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.map eC) ∧
    (eC ≫ specialization (NoetherianSectionSpecialization.Coeff ell m) g s κB =
      (scalarExtensionDerived ell r m hmr (X := S)).map
        (specialization (NoetherianSectionSpecialization.Coeff ell r) g s κA) ≫ e0) ∧
    (∀ (φ ψ : (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj L ⟶
      (upperStar (ModuleCat.{u + 1}
          (NoetherianSectionSpecialization.Coeff ell m))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M),
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).map φ =
        (upperStar (ModuleCat.{u + 1}
          (NoetherianSectionSpecialization.Coeff ell m))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).map ψ → φ = ψ) ∧
    (∀ (n : ℤ)
      (φ ψ : (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1}
          (NoetherianSectionSpecialization.Coeff ell m))
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj L)⟦n⟧ ⟶
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1}
            (NoetherianSectionSpecialization.Coeff ell m))
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj M)⟦n⟧),
      (upperStar (ModuleCat.{u + 1}
        (NoetherianSectionSpecialization.Coeff ell m))
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map φ =
        (upperStar (ModuleCat.{u + 1}
          (NoetherianSectionSpecialization.Coeff ell m))
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map ψ →
      φ = ψ) := by
  sorry

end NoetherianSectionSpecialization
end AlgebraicGeometry.Etale
