module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # The localized graded comparison on the generated open

Source: Stacks Project, Constructions, Tags 01NK and 01N8
(blueprint: lem-trf-proj-localized-graded-comparison).

The auxiliary declarations spell out the domain, actual homogeneous fractions, and the
sectionwise form of the comparison. Multiplication compatibility is tested on pulled-back
pure tensors; these generate the tensor pullback locally. The chart normalization is written
after multiplying by the denominator, so it needs no arbitrary choice of a division map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Proj

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]

/-- The actual section `b / f^q` of `𝒪(m)` on `D₊(f)`, including `q = 0`.
Source: Stacks, Tags 01M7 and 01NK (blueprint: lem-trf-proj-localized-graded-comparison). -/
noncomputable def comparisonFraction (m e q : ℕ) (f : 𝒜 e) (b : 𝒜 (m + q * e)) :
    Γ(twist 𝒜 (m : ℤ), basicOpen 𝒜 f.val) :=
  ⟨fun x ↦ HomogeneousLocalization.degreePart.mk b
      ⟨f.val ^ q, SetLike.pow_mem_graded q f.property⟩
      (x.val.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.property q)
      (by simp only [smul_eq_mul, Nat.cast_add]; omega),
    ProjectiveSpectrum.Twist.isLocallyFraction_mk
      (by simp only [smul_eq_mul, Nat.cast_add]; omega) b
      ⟨f.val ^ q, SetLike.pow_mem_graded q f.property⟩
      (fun x ↦ x.val.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.property q)⟩

/-- Multiplication of homogeneous twist sections, with no degree-generation assumption.
Source: Stacks, Tags 01MN and 01NK (blueprint: lem-trf-proj-localized-graded-comparison).
This is the section pairing defining `μᴾ`, directly on the existing locally-fraction sheaf. -/
noncomputable def comparisonProduct (m n : ℕ) (V : (Proj 𝒜).Opens)
    (s : Γ(twist 𝒜 (m : ℤ), V)) (t : Γ(twist 𝒜 (n : ℤ), V)) :
    Γ(twist 𝒜 ((m + n : ℕ) : ℤ), V) :=
  ⟨fun x ↦ ⟨s.val x * t.val x,
      (Nat.cast_add m n (R := ℤ)).symm ▸
        HomogeneousLocalization.mul_mem_degreePart (s.val x).property (t.val x).property⟩,
    ProjectiveSpectrum.Twist.isLocallyFraction_mul (Nat.cast_add m n (R := ℤ)).symm
      s.property t.property⟩

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable {T : Scheme.{u}} (L : T.Modules) [L.IsInvertible]
variable (ψ : 𝒜 →+*ᵍ sectionRingGrade L)

/-- The union of the positive-degree generating opens `T_{ψ(f)}`.
Source: Stacks, Tag 01NK (blueprint: lem-trf-proj-localized-graded-comparison). -/
noncomputable def projComparisonDomain : T.Opens :=
  ⨆ (e : ℕ) (_ : 0 < e) (f : 𝒜 e), generatingLocus (ψ f.val e)

/-- Restriction of a homogeneous image to an ambient open; the graded map ensures that
its degree component is the whole homogeneous image.
Source: Stacks, Tag 01NK (blueprint: lem-trf-proj-localized-graded-comparison). -/
noncomputable def projComparisonImage (n : ℕ) (a : A) (W : T.Opens) :
    Γ(L.tensorPow n, W) :=
  (L.tensorPow n).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ψ a n)

/-- Families of actual module maps from pulled-back twists to restricted tensor powers.
Source: Stacks, Tag 01NK (blueprint: lem-trf-proj-localized-graded-comparison). -/
abbrev ProjComparisonFamily
    (r : (projComparisonDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜) :=
  ∀ m : ℕ, (tensorPullback r).obj (Proj.twist 𝒜 (m : ℤ)) ⟶
    (L.tensorPow m).restrict (projComparisonDomain 𝒜 L ψ).ι

/-- Evaluate the comparison on the actual pullback `1 ⊗ s`, identifying restriction
sections with sections on their ambient image open through `restrictAppIso`.
Source: Stacks, Tag 01NK (blueprint: lem-trf-proj-localized-graded-comparison). -/
noncomputable def projComparisonValue
    (r : (projComparisonDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜)
    (θ : ProjComparisonFamily 𝒜 L ψ r) (m : ℕ) (V : (Proj 𝒜).Opens)
    (s : Γ(Proj.twist 𝒜 (m : ℤ), V)) :
    Γ(L.tensorPow m, (projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ V)) :=
  ((L.tensorPow m).restrictAppIso (projComparisonDomain 𝒜 L ψ).ι (r ⁻¹ᵁ V)).hom
    ((θ m).app (r ⁻¹ᵁ V) (tensorPullbackSection r (Proj.twist 𝒜 (m : ℤ)) V s))

/-- The homogeneous-fraction normalization, after multiplying by the free denominator.
Source: Stacks, Tags 01NK and 01N8 (blueprint: lem-trf-proj-localized-graded-comparison).
On the specified preimage of `D₊(f)`, multiplication by `ψ(f)^q` is invertible, so this
is precisely the division formula, rather than a choice of an arbitrary chart map. -/
def ProjComparisonChartNormalized
    (r : (projComparisonDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜)
    (θ : ProjComparisonFamily 𝒜 L ψ r) : Prop :=
  ∀ (m e : ℕ) (_he : 0 < e) (f : 𝒜 e) (q : ℕ) (b : 𝒜 (m + q * e)),
    (L.tensorPowAddIso m (q * e)).inv.app
        ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val))
        (tmulSection
          (projComparisonValue 𝒜 L ψ r θ m (Proj.basicOpen 𝒜 f.val)
            (Proj.comparisonFraction 𝒜 m e q f b))
          (projComparisonImage 𝒜 L ψ (q * e) (f.val ^ q)
            ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val)))) =
      projComparisonImage 𝒜 L ψ (m + q * e) b.val
        ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val))

/-- The unique normalized family from pulled-back Proj twists to the tensor powers on
the positive-degree generated open. The clauses give normalization, restriction (hence
agreement on overlaps), global homogeneous sections, the unit, multiplication, and
uniqueness among all chart-normalized families.

Source: Stacks Project, Constructions, Tags 01NK and 01N8
(blueprint: lem-trf-proj-localized-graded-comparison).

Proof:
1. On `W_f = T_{ψ(f)}`, define the map on fractions by `b/f^q ↦ ψ(b)/ψ(f)^q`.
   If two fractions agree, a power of `f` kills their cross difference. Apply `ψ`
   and cancel the invertible multiplications by `ψ(f)` on `W_f`. This proves
   well-definedness even when `f` is a zero divisor. Here the twisting-sheaf charts
   are those of def-weil-pbc-proj-twisting-sheaf and the free denominators are given
   by def-sc-section-generating-locus.
2. Common denominators prove additivity. The given scalar formula for `r` and the
   multiplication of def-sc-invertible-section-ring prove semilinearity, so the
   chart map takes values in the pushforward module with its prescribed scalars.
3. For `D₊(g) ⊆ D₊(f)`, lem-weil-pbc-proj-graded-module-sheaf-exists gives
   `g^k = af` and the restriction `b/f^q ↦ a^q b/g^(kq)`. Apply `ψ` and multiply
   by the invertible denominators to see that the chart maps commute with this
   restriction. In particular they agree on `D₊(fg)`.
4. The standard opens form a basis. Extend the compatible maps to a sheaf map
   `𝒪(m) ⟶ r_*(L^m|U)` by lem-weil-pbc-sheaf-morphism-on-basis. Check linearity
   on the basis and transpose by lem-pc-module-pullback-adjunction. Its normalized
   unit is the actual section `1 ⊗ s`, used in projComparisonValue. This yields
   the required module maps and their restriction compatibility.
5. Taking `q = 0` sends every global homogeneous section to its image under `ψ`.
   In degree zero the map is `r^sharp`, which gives the unit. Products of fractions
   satisfy `(b/f^q)(c/f^t) = bc/f^(q+t)` and `ψ(bc) = ψ(b)ψ(c)`. Thus the two
   multiplication arrows agree on pulled-back pure tensors. Such tensors locally
   generate the tensor pullback, and bilinearity gives equality of the whole
   sheaf maps under the canonical tensor-pullback comparison. The multiplication
   clause below is exactly this test on pure tensors for every open and sections.
6. Transpose any other chart-normalized family by the same adjunction. Its maps
   agree on every fraction on the standard-open basis, so basis uniqueness makes
   the transposes equal. The adjunction bijection gives equality of the families.
   All arguments cover the empty generated open, degree zero, and arbitrary
   nonnegative gradings; no degree-generation or quasi-compactness is used. -/
theorem existsUnique_proj_localized_graded_comparison
    (r : (projComparisonDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜)
    (hr_preimage : ∀ (e : ℕ) (_he : 0 < e) (f : 𝒜 e),
      (projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val) =
        generatingLocus (ψ f.val e))
    (hr_formula : ∀ (e : ℕ) (_he : 0 < e) (f : 𝒜 e) (q : ℕ) (b : 𝒜 (q • e)),
      ((projComparisonDomain 𝒜 L ψ).ι.appIso (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val)).inv
          (r.app (Proj.basicOpen 𝒜 f.val)
            (Proj.awayToSection 𝒜 f.val
              (HomogeneousLocalization.Away.mk 𝒜 f.property q b.val b.property))) •
          projComparisonImage 𝒜 L ψ (q • e) (f.val ^ q)
            ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val)) =
        projComparisonImage 𝒜 L ψ (q • e) b.val
          ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 f.val))) :
    ∃ θ : ProjComparisonFamily 𝒜 L ψ r,
      ProjComparisonChartNormalized 𝒜 L ψ r θ ∧
      (∀ (m : ℕ) (V W : (Proj 𝒜).Opens) (h : W ≤ V)
        (s : Γ(Proj.twist 𝒜 (m : ℤ), V)),
        projComparisonValue 𝒜 L ψ r θ m W
            ((Proj.twist 𝒜 (m : ℤ)).presheaf.map (homOfLE h).op s) =
          (L.tensorPow m).presheaf.map
            (homOfLE (Scheme.Hom.image_mono (projComparisonDomain 𝒜 L ψ).ι
              ((Opens.map r.base).monotone h))).op
            (projComparisonValue 𝒜 L ψ r θ m V s)) ∧
      (∀ (m : ℕ) (b : 𝒜 m),
        projComparisonValue 𝒜 L ψ r θ m ⊤
            ((Proj.unitToTwist b.property ≫
              eqToHom (congrArg (Proj.twist 𝒜) (zero_add (m : ℤ)))).app ⊤
                (1 : Γ(Proj 𝒜, ⊤))) =
          projComparisonImage 𝒜 L ψ m b.val
            ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ ⊤))) ∧
      (∀ (V : (Proj 𝒜).Opens) (a : Γ(Proj 𝒜, V)),
        projComparisonValue 𝒜 L ψ r θ 0 V
            (Scheme.Modules.Hom.app (Proj.unitToTwistZero (𝒜 := 𝒜)) V
              (unitSectionsEquiv V a)) =
          unitSectionsEquiv
            ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ V))
            (((projComparisonDomain 𝒜 L ψ).ι.appIso (r ⁻¹ᵁ V)).inv (r.app V a))) ∧
      (∀ (m n : ℕ) (V : (Proj 𝒜).Opens)
        (s : Γ(Proj.twist 𝒜 (m : ℤ), V)) (t : Γ(Proj.twist 𝒜 (n : ℤ), V)),
        projComparisonValue 𝒜 L ψ r θ (m + n) V (Proj.comparisonProduct 𝒜 m n V s t) =
          (L.tensorPowAddIso m n).inv.app
            ((projComparisonDomain 𝒜 L ψ).ι ''ᵁ (r ⁻¹ᵁ V))
            (tmulSection (projComparisonValue 𝒜 L ψ r θ m V s)
              (projComparisonValue 𝒜 L ψ r θ n V t))) ∧
      (∀ θ' : ProjComparisonFamily 𝒜 L ψ r,
        ProjComparisonChartNormalized 𝒜 L ψ r θ' → θ' = θ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
