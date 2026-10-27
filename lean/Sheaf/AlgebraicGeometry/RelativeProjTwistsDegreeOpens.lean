/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension

/-! # Twists and degree-generated opens on relative Proj

Source: Stacks Project, Constructions, Tags 01NR, 01MS, equation-Ud, and 01NY
(blueprint: lem-sfb-relative-proj-twists-degree-opens).

The output record packages the integer twists and the actual tensor-pullback section maps.
Normalization uses the existing locally-fraction sheaves on each affine-base chart.
The degree opens are explicit unions of images of standard opens. Iterated multiplication
is constructed recursively, including its degree-zero unit. No twist is chosen from an
unrestricted existence assertion, and no finite generation or degree-zero equality is used.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry.RelativeProjAlgebra

variable {X : Scheme.{u}} (A : RelativeProjAlgebra X)

/-- The degree-d open is the union of the images of all degree-d standard opens.
Source: Stacks, equation-Ud and 01NY
(blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def degreeOpen (d : ℕ) : A.affineData.relProj.Opens :=
  ⨆ V : X.affineOpens, ⨆ a : A.affineData.grading V d,
    A.affineData.relProjι V ''ᵁ Proj.basicOpen (A.affineData.grading V) a.val

/-- A homogeneous section as an element of the actual section grading.
Source: Stacks, 01NR (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def sectionElement (V : X.affineOpens) (n : ℕ) (b : Γ(A.piece n, V.1)) :
    A.grade V n :=
  ⟨@id (A.sections V) ((Sigma.ι A.piece n ≫ A.decomposition.hom).app V.1 b), ⟨b, rfl⟩⟩

/-- The relative twists, multiplication, unit, homogeneous-section maps and affine
identifications. Laws and normalization are stated separately, so this record assumes
none of the existence assertion. The input is the existing graded algebra sheaf and its
canonical affine-basis relative Proj.
Source: Stacks, 01NR (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
structure TwistSystem where
  E : ℤ → A.affineData.relProj.Modules
  unit : 𝟙_ A.affineData.relProj.Modules ≅ E 0
  mul : ∀ i j : ℤ, E i ⊗ E j ⟶ E (i + j)
  η : ∀ n : ℕ, (tensorPullback A.affineData.relProjHom).obj (A.piece n) ⟶ E n
  chart : ∀ (V : X.affineOpens) (j : ℤ),
    (E j).restrict (A.affineData.relProjι V) ≅ Proj.twist (A.affineData.grading V) j

variable {A}

/-- Express a global section in an affine-base twist chart, after ordinary restriction.
Source: Stacks, 01NR, theta_U (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.chartSection (D : A.TwistSystem) (V : X.affineOpens) (j : ℤ)
    (U : A.affineData.relProj.Opens) (s : Γ(D.E j, U)) :
    Γ(Proj.twist (A.affineData.grading V) j, A.affineData.relProjι V ⁻¹ᵁ U) :=
  (D.chart V j).hom.app _
    ((D.E j).presheaf.map (homOfLE ((A.affineData.relProjι V).image_preimage_le U)).op s)

/-- Homogeneous multiplication evaluated on sections via the sheaf tensor product.
Source: Stacks, equation-multiply (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.multiply (D : A.TwistSystem) {i j : ℤ}
    {U : A.affineData.relProj.Opens} (s : Γ(D.E i, U)) (t : Γ(D.E j, U)) :
    Γ(D.E (i + j), U) :=
  (D.mul i j).app U (tmulSection s t)

/-- The adjoint homogeneous-section map, using the actual section 1 tensor b.
Source: Stacks, 01NR (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.homogeneousSection (D : A.TwistSystem) (n : ℕ) (U : X.Opens)
    (b : Γ(A.piece n, U)) : Γ(D.E n, A.affineData.relProjHom ⁻¹ᵁ U) :=
  (D.η n).app _ (tensorPullbackSection A.affineData.relProjHom (A.piece n) U b)

/-- The canonical iterated multiplication into degree k*d, with the unit for k=0.
Source: Stacks, equation-multiply and 01MS
(blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.power (D : A.TwistSystem) (d : ℕ) :
    ∀ k : ℕ, (D.E d).tensorPow k ⟶ D.E ((k * d : ℕ) : ℤ)
  | 0 => D.unit.hom ≫ eqToHom (congrArg D.E (by simp))
  | k + 1 => (D.E d ◁ D.power d k) ≫ D.mul d (k * d) ≫
      eqToHom (congrArg D.E (by push_cast; ring))

/-- Tensor the actual a-fold multiplication n times, without choosing any map.
Source: Stacks, 01NY, degree-divisibility comparison
(blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.groupedPower (D : A.TwistSystem) (d a : ℕ) :
    ∀ n : ℕ, ((D.E d).tensorPow a).tensorPow n ⟶ (D.E (a * d)).tensorPow n
  | 0 => 𝟙 _
  | n + 1 => D.power d a ⊗ₘ D.groupedPower d a n

/-- Normalization on the affine charts, including all integer products, the unit,
the actual section a/1, and coefficientwise restriction of fractions along every
further affine-base restriction. The last equality gives identity and cocycle
compatibility as well, since the coefficient restriction homomorphisms compose.
Source: Stacks, 01NR, 01NO, 01NP
(blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
structure TwistSystem.Normalized (D : A.TwistSystem) : Prop where
  quasiCoherent : ∀ j : ℤ, (D.E j).IsQuasicoherent
  associative : ∀ (i j k : ℤ) (U : A.affineData.relProj.Opens)
    (s : Γ(D.E i, U)) (t : Γ(D.E j, U)) (r : Γ(D.E k, U)),
    HEq (D.multiply (D.multiply s t) r) (D.multiply s (D.multiply t r))
  commutative : ∀ (i j : ℤ) (U : A.affineData.relProj.Opens)
    (s : Γ(D.E i, U)) (t : Γ(D.E j, U)), HEq (D.multiply s t) (D.multiply t s)
  unit_left : ∀ (j : ℤ) (U : A.affineData.relProj.Opens) (s : Γ(D.E j, U)),
    HEq (D.multiply (D.unit.hom.app U (unitSectionsEquiv U 1)) s) s
  unit_right : ∀ (j : ℤ) (U : A.affineData.relProj.Opens) (s : Γ(D.E j, U)),
    HEq (D.multiply s (D.unit.hom.app U (unitSectionsEquiv U 1))) s
  graded_unit : ∀ (U : X.Opens) (r : Γ(X, U)),
    D.homogeneousSection 0 U (A.graded.unit.val.app (op U) r) =
      D.unit.hom.app _ (unitSectionsEquiv _ (A.affineData.relProjHom.app U r))
  graded_mul : ∀ (m n : ℕ) (U : X.Opens)
    (b : Γ(A.piece m, U)) (c : Γ(A.piece n, U)),
    HEq (D.homogeneousSection (m + n) U (A.graded.mul m n U b c))
      (D.multiply (D.homogeneousSection m U b) (D.homogeneousSection n U c))
  unit : ∀ V : X.affineOpens,
    (restrictFunctor (A.affineData.relProjι V)).map D.unit.hom ≫ (D.chart V 0).hom =
      (restrictUnitIso (A.affineData.relProjι V)).hom ≫ Proj.unitToTwistZero
  mul : ∀ (V : X.affineOpens) (i j : ℤ) (U : A.affineData.relProj.Opens)
    (s : Γ(D.E i, U)) (t : Γ(D.E j, U))
    (x : A.affineData.relProjι V ⁻¹ᵁ U),
    ((D.chartSection V (i + j) U ((D.mul i j).app U (tmulSection s t))).val x).val =
      ((D.chartSection V i U s).val x).val * ((D.chartSection V j U t).val x).val
  homogeneous : ∀ (V : X.affineOpens) (n : ℕ) (b : Γ(A.piece n, V.1)),
    HEq (D.chartSection V n (A.affineData.relProjHom ⁻¹ᵁ V.1)
      ((D.η n).app _ (tensorPullbackSection A.affineData.relProjHom (A.piece n) V.1 b)))
      ((Proj.unitToTwist (A := A.affineData.obj V)
        (𝒜 := A.affineData.grading V) (d := n) (f := (A.sectionElement V n b).val)
        (A.sectionElement V n b).property).app ⊤ (unitSectionsEquiv ⊤ 1))
  restriction : ∀ (V W : X.affineOpens) (h : W ≤ V) (j : ℤ)
    (U : A.affineData.relProj.Opens) (s : Γ(D.E j, U))
    (x : A.affineData.relProjι W ⁻¹ᵁ U)
    (y : A.affineData.relProjι V ⁻¹ᵁ U)
    (hy : y.val = (A.affineData.relProjFunctor.map (homOfLE h)) x.val),
    ((D.chartSection W j U s).val x).val =
      Localization.localRingHom _ _ (A.affineData.res h).toRingHom
        (by rw [hy]; rfl)
        ((D.chartSection V j U s).val y).val

/-- A normalized isomorphism respects the fixed affine identifications and all the
algebra and homogeneous-section maps. Restricting its chart equation again gives the
same equation on every overlap, including nonaffine overlaps by affine refinement.
Source: Stacks, 01NR (blueprint: lem-sfb-relative-proj-twists-degree-opens). -/
def TwistSystem.Respects (D D' : A.TwistSystem) (e : ∀ j : ℤ, D.E j ≅ D'.E j) : Prop :=
  (∀ (V : X.affineOpens) (j : ℤ),
    (restrictFunctor (A.affineData.relProjι V)).map (e j).hom ≫ (D'.chart V j).hom =
      (D.chart V j).hom) ∧
  D.unit.hom ≫ (e 0).hom = D'.unit.hom ∧
  (∀ i j : ℤ, D.mul i j ≫ (e (i + j)).hom =
    ((e i).hom ⊗ₘ (e j).hom) ≫ D'.mul i j) ∧
  ∀ n : ℕ, D.η n ≫ (e n).hom = D'.η n

/-- Twists glue with their canonical maps and unique normalized identifications. The
positive degree opens descend, cover, and increase under positive multiples. On each,
the indicated twist is a line, its actual iterated multiplication is invertible, and
the actual degree-d map is a sheaf surjection. On Y_d the degree-ad sections, expressed
using the multiplication isomorphism for E_d, have exactly their Veronese indices.

Source: Stacks Project, Constructions, 01NR, 01MS, equation-Ud, and 01NY
(blueprint: lem-sfb-relative-proj-twists-degree-opens).

Proof:
1. Degreewise quasi-coherent affine section base change identifies section restrictions
   with scalar extension (lem-weil-pbc-quasi-coherent-affine-section-base-change).
   Apply lem-sfb-proj-scalar-extension-twist-comparison to the twists and their products;
   lem-nagata-proj-affine-restriction identifies the underlying transition scheme maps.
   Restriction composition gives identity and cocycle equations.
2. On intersections of affine base opens refine by affine opens; normalized comparisons
   agree after further refinement. Glue the integer twists and their maps using
   lem-weil-pbc-glue-sheaves-of-modules. Quasi-coherence is local, by clause (c) of
   lem-weil-pbc-proj-graded-module-sheaf-exists applied to shifted graded modules.
3. Multiplication of localized fractions is bilinear and restriction-compatible. Its
   sheaf tensor factorization (lem-pc-sites-sheaf-tensor-bilinear-universal) glues. Unit,
   associativity and commutativity hold on fractions; the zeroth twist is the unit.
4. The sections a/1 agree under affine restriction. Their adjoints for the normalized
   tensor pullback define eta. Unit and products commute by the fraction identities.
   Gluing the composites of chart identifications gives the unique isomorphism of two
   normalized systems; it respects eta, the unit and products by local verification.
5. Degree-d section base change says every target section is a finite linear combination
   of restricted degree-d sections. A prime avoids such a combination only if it avoids
   one summand. Thus the standard-open unions pull back to one another, by
   lem-nagata-affine-proj-scalar-extension, and descend to the displayed degreeOpen.
6. On D_+(f), deg(f)=d>0, f is a frame of E_d, with inverse multiplication by f^(-1).
   The k-fold multiplication sends f tensor ... tensor f to f^k, hence is invertible;
   k=0 is the unit. Eta_d sends f to this frame and is locally surjective.
7. Every Proj point avoids a positive-degree element, so the degree opens cover. Since
   D_+(f)=D_+(f^a), Y_d is contained in Y_ad. Under the power identifications both
   degree-adn maps send b to b/1, with coefficient b/f^(an). This proves the tensor and
   Veronese compatibility, including n=0, without finite generation or A_0=O_X. -/
theorem exists_twists_degreeOpens (A : RelativeProjAlgebra X) :
    ∃ D : A.TwistSystem, D.Normalized ∧
      (∀ D' : A.TwistSystem, D'.Normalized → ∃! e : ∀ j : ℤ, D.E j ≅ D'.E j,
        D.Respects D' e) ∧
      (∀ (V : X.affineOpens) (d : ℕ), 0 < d →
        A.affineData.relProjι V ⁻¹ᵁ A.degreeOpen d =
          ⨆ a : A.affineData.grading V d, Proj.basicOpen (A.affineData.grading V) a.val) ∧
      (⨆ d : {d : ℕ // 0 < d}, A.degreeOpen d.val) = ⊤ ∧
      (∀ (d a : ℕ), 0 < d → 0 < a → A.degreeOpen d ≤ A.degreeOpen (a * d)) ∧
      (∀ d : ℕ, 0 < d →
        ((D.E d).restrict (A.degreeOpen d).ι).IsInvertible ∧
        (∀ k : ℕ, IsIso ((restrictFunctor (A.degreeOpen d).ι).map (D.power d k))) ∧
        Epi ((restrictFunctor (A.degreeOpen d).ι).map (D.η d))) ∧
      (∀ (d a n : ℕ), 0 < d → 0 < a →
        (restrictFunctor (A.degreeOpen d).ι).map
            (((D.E d).tensorPowMulIso a n).hom ≫
              D.groupedPower d a n ≫ D.power (a * d) n) =
          (restrictFunctor (A.degreeOpen d).ι).map
            (D.power d (a * n) ≫ eqToHom (congrArg D.E (by push_cast; ring)))) := by
  sorry

end AlgebraicGeometry.RelativeProjAlgebra
