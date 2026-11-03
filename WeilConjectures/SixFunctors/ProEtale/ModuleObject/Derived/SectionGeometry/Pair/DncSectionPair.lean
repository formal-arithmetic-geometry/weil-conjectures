/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionGeometry.CondensedSectionBaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Actual geometric pairs used by the native deformation comparisons

Source: latest blueprint lem-pur-dnc-section-geometry, clauses (1)--(5).
The structure only bundles the standing geometric hypotheses. Every construction below
specifies its schemes, projection and section before supplying their geometric certificates.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry

/-- Packaging of exactly the smooth separated finite-type closed-section situation.
Source: def-pur-dnc-section-family (blueprint: lem-pur-dnc-section-geometry). -/
structure Pair (D : WeilConjectures.FiniteFieldDatum.{u}) where
  B : Over (Spec (.of D.k))
  V : Over (Spec (.of D.k))
  [base_ft : LocallyOfFiniteType B.hom]
  [base_qc : QuasiCompact B.hom]
  [base_sep : IsSeparated B.hom]
  [source_ft : LocallyOfFiniteType V.hom]
  [source_qc : QuasiCompact V.hom]
  [source_sep : IsSeparated V.hom]
  g : V ⟶ B
  [smooth : Smooth g.left]
  [separated : IsSeparated g.left]
  [finite_type : LocallyOfFiniteType g.left]
  [qc : QuasiCompact g.left]
  s : B ⟶ V
  [closed : IsClosedImmersion s.left]
  section_eq : s ≫ g = 𝟙 B
attribute [instance] Pair.base_ft Pair.base_qc Pair.base_sep Pair.source_ft Pair.source_qc
  Pair.source_sep Pair.smooth Pair.separated Pair.finite_type Pair.qc Pair.closed

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

/-- The literal Rees pair; all certificates come from the repaired family dependency.
Source: def-pur-dnc-section-family (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.rees (Q : Pair D) : Pair D :=
  let H := condensedDncDomain D Q.B Q.V Q.g Q.s Q.section_eq
  { B := condensedDncBase D Q.B
    V := condensedDncSource D Q.B Q.V Q.g Q.s
    base_ft := H.1
    base_qc := H.2.1
    base_sep := H.2.2.1
    source_ft := H.2.2.2.1
    source_qc := H.2.2.2.2.1
    source_sep := H.2.2.2.2.2.1
    g := condensedDncMap D Q.B Q.V Q.g Q.s
    smooth := H.2.2.2.2.2.2.1
    separated := H.2.2.2.2.2.2.2.1
    finite_type := H.2.2.2.2.2.2.2.2.1
    qc := H.2.2.2.2.2.2.2.2.2.1
    s := condensedDncSection D Q.B Q.V Q.g Q.s Q.section_eq
    closed := H.2.2.2.2.2.2.2.2.2.2.1
    section_eq := H.2.2.2.2.2.2.2.2.2.2.2 }

/-- The normal bundle with its given field map.
Source: def-pur-normal-bundle (blueprint: lem-pur-dnc-section-geometry (1)). -/
abbrev Pair.normalSource (Q : Pair D) : Over (Spec (.of D.k)) :=
  Over.mk (Scheme.Hom.normalConeProj Q.g.left Q.s.left ≫ Q.B.hom)

/-- The zero section of the actual normal cone, over the given field.
Source: def-pur-normal-bundle (blueprint: lem-pur-dnc-section-geometry (1)). -/
def Pair.normalSection (Q : Pair D) : Q.B ⟶ Q.normalSource :=
  Over.homMk Q.s.left.normalConeZeroSection (by
    change Q.s.left.normalConeZeroSection ≫
      (Scheme.Hom.normalConeProj Q.g.left Q.s.left ≫ Q.B.hom) = Q.B.hom
    rw [← Category.assoc,
      Scheme.Hom.normalConeZeroSection_normalConeProj
        (congrArg (fun f ↦ f.left) Q.section_eq), Category.id_comp])

/-- The normal projection's domain certificates, without additional assumptions.
Source: sk-lem-geometry (1),(2) (blueprint: lem-pur-dnc-section-geometry).
Proof: centred coordinates make I/I^2 locally free. The normal projection is the
rank-d vector bundle and is the zero base change of the smooth Rees projection.
Both schemes are separated finite type over the fixed field. Its zero section is
closed. This also applies to varying smooth dimension, dimension zero and empty bases. -/
theorem Pair.normalProperties (Q : Pair D) :
    LocallyOfFiniteType Q.normalSource.hom ∧ QuasiCompact Q.normalSource.hom ∧
    IsSeparated Q.normalSource.hom ∧
    Smooth (Scheme.Hom.normalConeProj Q.g.left Q.s.left) ∧
    IsSeparated (Scheme.Hom.normalConeProj Q.g.left Q.s.left) ∧
    LocallyOfFiniteType (Scheme.Hom.normalConeProj Q.g.left Q.s.left) ∧
    QuasiCompact (Scheme.Hom.normalConeProj Q.g.left Q.s.left) ∧
    IsClosedImmersion Q.normalSection.left := by
  sorry

/-- The actual normal pair; only its geometric certificates are postponed.
Source: sk-lem-geometry (1) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.normal (Q : Pair D) : Pair D :=
  let H := Q.normalProperties
  { B := Q.B
    V := Q.normalSource
    base_ft := inferInstance
    base_qc := inferInstance
    base_sep := inferInstance
    source_ft := H.1
    source_qc := H.2.1
    source_sep := H.2.2.1
    g := Over.homMk (Scheme.Hom.normalConeProj Q.g.left Q.s.left) rfl
    smooth := H.2.2.2.1
    separated := H.2.2.2.2.1
    finite_type := H.2.2.2.2.2.1
    qc := H.2.2.2.2.2.2.1
    s := Q.normalSection
    closed := H.2.2.2.2.2.2.2
    section_eq := Over.OverMorphism.ext
      (Scheme.Hom.normalConeZeroSection_normalConeProj
        (congrArg (fun f ↦ f.left) Q.section_eq)) }

/-- The canonical base-changed pair, at the scheme fibre product.
Source: sk-lem-geometry (3),(5) (blueprint: lem-pur-dnc-section-geometry). -/
abbrev Pair.changedSource (Q : Pair D) (B' : Over (Spec (.of D.k))) (b : B' ⟶ Q.B) :
    Over (Spec (.of D.k)) :=
  Over.mk (pullback.snd Q.g.left b.left ≫ B'.hom)

/-- The induced section is the literal pullback lift (b*s,id).
Source: sk-lem-geometry (5) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.changedSection (Q : Pair D) (B' : Over (Spec (.of D.k))) (b : B' ⟶ Q.B) :
    B' ⟶ Q.changedSource B' b :=
  Over.homMk (Scheme.Hom.baseChangeSection Q.g.left Q.s.left
    (congrArg (fun f ↦ f.left) Q.section_eq) b.left) (by
      change Scheme.Hom.baseChangeSection Q.g.left Q.s.left
        (congrArg (fun f ↦ f.left) Q.section_eq) b.left ≫
          (pullback.snd Q.g.left b.left ≫ B'.hom) = B'.hom
      rw [← Category.assoc, Scheme.Hom.baseChangeSection_snd, Category.id_comp])

/-- The base-changed pair has the same standing geometric domain, for arbitrary b.
Source: sk-lem-geometry (5) (blueprint: lem-pur-dnc-section-geometry).
Proof: base change preserves smoothness, separatedness, finite type and closed
immersions. Compose the projection with the field structure of B'. No flatness
is needed. The pullback-lift equations give the section law. -/
theorem Pair.changedProperties (Q : Pair D) (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ Q.B) :
    LocallyOfFiniteType (Q.changedSource B' b).hom ∧
    QuasiCompact (Q.changedSource B' b).hom ∧
    IsSeparated (Q.changedSource B' b).hom ∧
    Smooth (pullback.snd Q.g.left b.left) ∧
    IsSeparated (pullback.snd Q.g.left b.left) ∧
    LocallyOfFiniteType (pullback.snd Q.g.left b.left) ∧
    QuasiCompact (pullback.snd Q.g.left b.left) ∧
    IsClosedImmersion (Q.changedSection B' b).left := by
  sorry

/-- The actual base-changed pair, including its fixed closed section.
Source: sk-lem-geometry (5) (blueprint: lem-pur-dnc-section-geometry). -/
def Pair.changed (Q : Pair D) (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ Q.B) : Pair D :=
  let H := Q.changedProperties B' b
  { B := B'
    V := Q.changedSource B' b
    base_ft := inferInstance
    base_qc := inferInstance
    base_sep := inferInstance
    source_ft := H.1
    source_qc := H.2.1
    source_sep := H.2.2.1
    g := Over.homMk (pullback.snd Q.g.left b.left) rfl
    smooth := H.2.2.2.1
    separated := H.2.2.2.2.1
    finite_type := H.2.2.2.2.2.1
    qc := H.2.2.2.2.2.2.1
    s := Q.changedSection B' b
    closed := H.2.2.2.2.2.2.2
    section_eq := Over.OverMorphism.ext (Scheme.Hom.baseChangeSection_snd
      Q.g.left Q.s.left (congrArg (fun f ↦ f.left) Q.section_eq) b.left) }

/-- The standard pair with its zero section, with no orientation data.
Source: sk-lem-geometry (4) (blueprint: lem-pur-dnc-section-geometry). -/
def standard (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (d : ℕ) : Pair D where
  B := B
  V := Over.mk ((AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) ≫ B.hom)
  base_ft := inferInstance
  base_qc := inferInstance
  base_sep := inferInstance
  source_ft := by
    change LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  source_qc := by
    change QuasiCompact ((AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  source_sep := by
    change IsSeparated ((AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) ≫ B.hom)
    infer_instance
  g := Over.homMk (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) rfl
  smooth := by
    change Smooth (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
    exact SmoothOfRelativeDimension.smooth (Nat.card (ULift.{u} (Fin d))) _
  separated := by
    change IsSeparated (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
    infer_instance
  finite_type := by
    change LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
    infer_instance
  qc := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
    infer_instance
  s := Over.homMk (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left) (by
    change AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left ≫
      ((AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left) ≫ B.hom) = B.hom
    rw [← Category.assoc, AffineSpace.zeroSection_over, Category.id_comp])
  closed := by
    change IsClosedImmersion (AffineSpace.zeroSection (ULift.{u} (Fin d)) B.left)
    infer_instance
  section_eq := Over.OverMorphism.ext (AffineSpace.zeroSection_over _ _)

/-- Base change preserves the fixed relative dimension, including nonflat base change.
Source: sk-lem-geometry (5) (blueprint: lem-pur-dnc-section-geometry).
Proof: the changed projection is the actual pullback second projection; apply
stability of SmoothOfRelativeDimension under base change. -/
instance Pair.changed_relativeDimension (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] (B' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
    (b : B' ⟶ Q.B) : SmoothOfRelativeDimension d (Q.changed B' b).g.left := by
  change SmoothOfRelativeDimension d (pullback.snd Q.g.left b.left)
  infer_instance

/-- The standard affine d-space pair has the specified relative dimension d.
Source: sk-lem-geometry (4) (blueprint: lem-pur-dnc-section-geometry).
Proof: use the affine-space dimension instance and the cardinality of ULift (Fin d). -/
instance standard_relativeDimension (B : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom] (d : ℕ) :
    SmoothOfRelativeDimension d (standard B d).g.left := by
  change SmoothOfRelativeDimension d (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left)
  simpa using (inferInstance : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin d)))
    (AffineSpace (ULift.{u} (Fin d)) B.left ↘ B.left))

end AlgebraicGeometry.ProEtale.CondensedRing.SectionGeometry
