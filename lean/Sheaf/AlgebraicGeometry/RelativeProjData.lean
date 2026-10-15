/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Relative Proj construction data

Source: blueprint, Nagata compactification, sketch data, Relative Proj, order 12
(blueprint: def-nagata-relative-proj); Stacks Project, Constructions, Tag 01LH.

The input records the underlying quasi-coherent algebra and its homogeneous sheaves,
with the direct-sum identification and its multiplication and unit equations. On affine
opens the sections of this sum are the sum of sections. The local schemes are ordinary
Proj schemes. Relative gluing over the basis of all affine opens records overlaps by
pullback squares; intersections need not be affine. The output includes every affine
restriction identification. No existence of the output is asserted here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- A quasi-coherent commutative graded algebra sheaf, including the identification of
its underlying module with the sheaf direct sum of its homogeneous pieces.
The last two equations say that this identification respects the given graded algebra.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
structure RelativeProjAlgebra (X : Scheme.{u}) where
  algebra : QuasiCoherentAlgebra X
  piece : ℕ → X.Modules
  graded : GradedSheafAlgebra piece
  decomposition : (∐ piece) ≅ algebra.obj.toModule
  mul_eq : ∀ (U : X.Opens) (m n : ℕ)
    (a : (piece m).val.obj (op U)) (b : (piece n).val.obj (op U)),
    ((Sigma.ι piece (m + n) ≫ decomposition.hom).val.app (op U))
        (graded.mul m n U a b) =
      (@id (algebra.obj.right.obj.obj (op U))
        (((Sigma.ι piece m ≫ decomposition.hom).val.app (op U)) a)) *
        (@id (algebra.obj.right.obj.obj (op U))
          (((Sigma.ι piece n ≫ decomposition.hom).val.app (op U)) b))
  unit_eq : ∀ (U : X.Opens) (r : Γ(X, U)),
    ((Sigma.ι piece 0 ≫ decomposition.hom).val.app (op U))
        (graded.unit.val.app (op U) r) = algebra.obj.hom.hom.app (op U) r

namespace RelativeProjAlgebra

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- The actual section ring of the input algebra on an affine open, not a chosen model.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
abbrev sections (V : X.affineOpens) : CommRingCat.{u} :=
  A.algebra.obj.right.obj.obj (op V.1)

/-- The homogeneous section subgroup is the image of the homogeneous-sheaf inclusion.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def sectionGrade (V : X.affineOpens) (n : ℕ) : AddSubgroup (A.sections V) :=
  (((Sigma.ι A.piece n ≫ A.decomposition.hom).val.app (op V.1)).hom.toAddMonoidHom).range

/-- The degree-zero unit belongs to the degree-zero subgroup.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: apply `unit_eq` to 1 and use that the algebra structure map preserves 1. -/
theorem sectionGrade_one (V : X.affineOpens) : 1 ∈ A.sectionGrade V 0 := by
  sorry

/-- Homogeneous multiplication adds degrees.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: lift both elements to their homogeneous sheaves and apply `mul_eq`. -/
theorem sectionGrade_mul (V : X.affineOpens) (m n : ℕ)
    (a b : A.sections V) (ha : a ∈ A.sectionGrade V m) (hb : b ∈ A.sectionGrade V n) :
    a * b ∈ A.sectionGrade V (m + n) := by
  sorry

/-- On an affine open the homogeneous section subgroups are an internal direct sum.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: every piece is a direct summand of the quasi-coherent underlying module, hence
quasi-coherent. On an affine open the equivalence with modules preserves coproducts.
Apply sections to `decomposition`; the resulting map from the direct sum is bijective.
The inclusions are injective, so replacing each piece by its image gives this internal sum. -/
theorem sectionGrade_internal (V : X.affineOpens) :
    DirectSum.IsInternal (A.sectionGrade V) := by
  sorry

/-- The induced grading on the section ring. The decomposition is the unique inverse of
the bijective recomposition map, not data selected from an unrestricted existence claim.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
noncomputable instance sectionGradedRing (V : X.affineOpens) :
    GradedRing (A.sectionGrade V) where
  toDecomposition := (A.sectionGrade_internal V).chooseDecomposition
  one_mem := A.sectionGrade_one V
  mul_mem := A.sectionGrade_mul V

/-- Restriction of the algebra sheaf preserves every homogeneous subgroup.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: the maps from the homogeneous sheaves to the total algebra are sheaf morphisms;
their naturality carries an element in the image to the image of its restriction. -/
theorem restriction_mem {V W : X.affineOpens} (h : W ≤ V) (n : ℕ)
    (a : A.sections V) (ha : a ∈ A.sectionGrade V n) :
    (A.algebra.obj.right.obj.map (homOfLE h).op).hom a ∈ A.sectionGrade W n := by
  sorry

/-- The graded section restriction homomorphism.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def restriction {V W : X.affineOpens} (h : W ≤ V) :
    A.sectionGrade V →+*ᵍ A.sectionGrade W where
  toRingHom := (A.algebra.obj.right.obj.map (homOfLE h).op).hom
  map_mem := fun {n} {a} ha ↦ A.restriction_mem h n a ha

/-- Affine restriction extends the irrelevant ideal to the irrelevant ideal.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: quasi-coherence identifies each homogeneous piece on W with base change from V.
Thus every positive-degree section on W is a finite linear combination of restrictions
of positive-degree sections on V. These sections generate the target irrelevant ideal. -/
theorem irrelevant_le {V W : X.affineOpens} (h : W ≤ V) :
    HomogeneousIdeal.irrelevant (A.sectionGrade W) ≤
      (HomogeneousIdeal.irrelevant (A.sectionGrade V)).map (A.restriction h) := by
  sorry

/-- The structural unit of the section algebra has degree zero.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj).
Proof: `unit_eq` exhibits its image as the inclusion of a section of the zeroth piece. -/
theorem unit_mem (V : X.affineOpens) (r : Γ(X, V.1)) :
    (A.algebra.obj.hom.hom.app (op V.1)).hom r ∈ A.sectionGrade V 0 := by
  sorry

/-- The base-ring homomorphism into degree zero; it need not be an isomorphism.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def unitZero (V : X.affineOpens) : Γ(X, V.1) →+* A.sectionGrade V 0 where
  toFun r := ⟨(A.algebra.obj.hom.hom.app (op V.1)).hom r, A.unit_mem V r⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' r s := Subtype.ext (map_add _ r s)
  map_mul' r s := Subtype.ext (map_mul _ r s)

/-- The local model on an affine open is Proj of its graded section ring.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def localProj (V : X.affineOpens) : Scheme.{u} := Proj (A.sectionGrade V)

/-- The local structural map is the degree-zero Proj map followed by the spectrum map
of the unit into degree zero and the canonical affine identification.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def localBase (V : X.affineOpens) : A.localProj V ⟶ V.1.toScheme :=
  Proj.toSpecZero (A.sectionGrade V) ≫ Spec.map (CommRingCat.ofHom (A.unitZero V)) ≫
    V.2.isoSpec.inv

/-- The local transition is precisely the Proj map of section restriction. Its standard
chart maps are the degree-zero homogeneous localization maps in Mathlib's `Proj.map`.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def localTransition {V W : X.affineOpens} (h : W ≤ V) :
    A.localProj W ⟶ A.localProj V :=
  Proj.map (A.restriction h) (A.irrelevant_le h)

end RelativeProjAlgebra

/-- Relative Proj construction datum over the chosen cover of all affine opens.
`gluing` includes the functor identity and composition laws and the equifibered squares:
these identify the overlaps with inverse-image open subschemes and encode the identity,
inverse and triple-overlap cocycle laws on affine refinements. `localIso`, `local_over`
and `local_transition` specify the local models, their degree-zero structural maps and
the restriction-induced overlap maps. The glued scheme and morphism are `gluing.glued`
and `gluing.toBase`. `restrictionIso` and its equations are the universal affine
restriction identifications and their compatibility. No existence is assumed or asserted.
Source: blueprint, Relative Proj, order 12; Stacks, Tag 01LH
(blueprint: def-nagata-relative-proj). -/
structure RelativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X) where
  gluing : Scheme.Cover.RelativeGluingData X.directedAffineCover
  localIso : ∀ V : X.affineOpens, gluing.functor.obj V ≅ A.localProj V
  local_over : ∀ V : X.affineOpens,
    (localIso V).hom ≫ A.localBase V = gluing.natTrans.app V
  local_transition : ∀ (V W : X.affineOpens) (h : W ≤ V),
    gluing.functor.map (homOfLE h) ≫ (localIso V).hom =
      (localIso W).hom ≫ A.localTransition h
  restrictionIso : ∀ V : X.affineOpens,
    (gluing.toBase ⁻¹ᵁ V.1).toScheme ≅ A.localProj V
  restriction_ι : ∀ V : X.affineOpens,
    (restrictionIso V).hom ≫ (localIso V).inv ≫ colimit.ι gluing.functor V =
      (gluing.toBase ⁻¹ᵁ V.1).ι
  restriction_over : ∀ V : X.affineOpens,
    (restrictionIso V).hom ≫ A.localBase V ≫ V.1.ι =
      (gluing.toBase ⁻¹ᵁ V.1).ι ≫ gluing.toBase
  restriction_compatibility : ∀ (V W : X.affineOpens) (h : W ≤ V),
    (restrictionIso W).inv ≫
        gluing.glued.homOfLE (gluing.toBase.preimage_mono h) ≫
          (restrictionIso V).hom = A.localTransition h

namespace RelativeProjData

variable {X : Scheme.{u}} {A : RelativeProjAlgebra X} (D : RelativeProjData A)

/-- The relative Proj scheme obtained by the specified relative scheme gluing.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def proj : Scheme.{u} := D.gluing.glued

/-- The structural morphism of the specified relative Proj.
Source: blueprint, Relative Proj, order 12 (blueprint: def-nagata-relative-proj). -/
def π : D.proj ⟶ X := D.gluing.toBase

end RelativeProjData

end AlgebraicGeometry
