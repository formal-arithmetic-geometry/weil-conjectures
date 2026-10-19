/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# The twist comparison for a graded map into an invertible section ring

Source: Stacks Project, Constructions, Tags 01NK and 01N8
(blueprint: lem-trf-proj-invertible-map-twist-iso).

The canonical map and its comparison are specified together by the inverse images of
basic opens, the images of homogeneous sections, and graded multiplication. These are
the characterizing properties in Tag 01NK. The conclusion concerns their restriction
to an arbitrary generated open, including the empty open.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable {T : Scheme.{u}} (L : T.Modules) [L.IsInvertible]

/-- The union `U(ψ)` of positive-degree generating loci, Stacks Tag 01NK
(blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def projSectionMapDomain (ψ : A →+* InvertibleSectionRing L) : T.Opens :=
  ⨆ (e : ℕ) (_he : 0 < e) (a : 𝒜 e), generatingLocus ((ψ a) e)

/-- Restrict a global section to any open in an open subscheme. Stacks Tag 01NK,
restriction in the section diagram (blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def projRestrictSection {M : T.Modules} (V : T.Opens) (W : V.toScheme.Opens)
    (s : Γ(M, ⊤)) : Γ(M.restrict V.ι, W) :=
  (M.restrictAppIso V.ι W).inv
    (M.presheaf.map (homOfLE (le_top : V.ι ''ᵁ W ≤ ⊤)).op s)

/-- The canonical tensor-pullback section `1 ⊗ s`, on the inverse image of the open
where `s` is given. This uses the abelian inverse-image unit and the module sheafification
unit of the recorded tensor pullback, without choosing an adjunction. Stacks Tags 0095,
0096 and 01NK (blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def projTensorPullbackSection {X Y : Scheme.{u}} (r : X ⟶ Y) (M : Y.Modules)
    (W : Y.Opens) (s : Γ(M, W)) : Γ((tensorPullback r).obj M, r ⁻¹ᵁ W) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} (tensorPullbackRingMap r)
      (TopCat.Sheaf.inverseImageModule r.base Y.sheaf M))).app (op (r ⁻¹ᵁ W))
    ((1 : X.sheaf.obj.obj (op (r ⁻¹ᵁ W))) ⊗ₜ[
      (TopCat.Sheaf.inverseImageRing r.base Y.sheaf).obj.obj (op (r ⁻¹ᵁ W)),
      ((tensorPullbackRingMap r).hom.app (op (r ⁻¹ᵁ W))).hom]
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (TopologicalSpace.Opens.map r.base) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app
          ((SheafOfModules.toSheaf _).obj M)).hom.app (op W) s))

/-- The section `a/1` of `O(d)`, using the recorded `Proj.unitToTwist`. Stacks Tag 01MM
and Tag 01NK (2) (blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def projHomogeneousTwistSection (d : ℕ) (a : 𝒜 d) : Γ(Proj.twist 𝒜 (d : ℤ), ⊤) :=
  (Proj.unitToTwist a.property ≫
    eqToHom (congrArg (Proj.twist 𝒜) (zero_add (d : ℤ)))).app ⊤
      (unitSectionsEquiv ⊤ 1)

/-- Tensor multiplication on restrictions of the powers of `L`. The restriction
identifications transport the existing tensor-section product and `tensorPowAddIso`.
Stacks Tags 01NK and 01N8 (blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def projRestrictedPowerMul (V : T.Opens) (i j : ℕ) (W : V.toScheme.Opens)
    (s : Γ((L.tensorPow i).restrict V.ι, W))
    (t : Γ((L.tensorPow j).restrict V.ι, W)) :
    Γ((L.tensorPow (i + j)).restrict V.ι, W) :=
  ((L.tensorPow (i + j)).restrictAppIso V.ι W).inv
    ((L.tensorPowAddIso i j).inv.app (V.ι ''ᵁ W)
      (tmulSection (((L.tensorPow i).restrictAppIso V.ι W).hom s)
        (((L.tensorPow j).restrictAppIso V.ι W).hom t)))

/-- The degree-`n` homogeneous-section normalization of the comparison. Stacks Tag
01NK (2) (blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def ProjTwistComparisonPreservesSections (ψ : A →+* InvertibleSectionRing L)
    (V : T.Opens) (r : V.toScheme ⟶ Proj 𝒜) (n : ℕ)
    (θ : (tensorPullback r).obj (Proj.twist 𝒜 (n : ℤ)) ⟶ (L.tensorPow n).restrict V.ι) :
    Prop :=
  ∀ a : 𝒜 n,
    θ.app (r ⁻¹ᵁ ⊤)
      (projTensorPullbackSection r (Proj.twist 𝒜 (n : ℤ)) ⊤
        (projHomogeneousTwistSection 𝒜 n a)) =
      projRestrictSection V (r ⁻¹ᵁ ⊤) ((ψ a) n)

/-- Graded multiplication compatibility, tested on sections of the twists on every
open. The pointwise product is multiplication in homogeneous localizations, so this
includes arbitrary fractions, not only the global homogeneous sections. Pure tensors
generate the sheaf tensor product, making this precisely equality of the multiplication
maps after tensor pullback. Stacks Tag 01NK, graded algebra map `θ`
(blueprint: lem-trf-proj-invertible-map-twist-iso). -/
def ProjTwistComparisonMultiplicative (V : T.Opens) (r : V.toScheme ⟶ Proj 𝒜)
    (θ : ∀ n : ℕ,
      (tensorPullback r).obj (Proj.twist 𝒜 (n : ℤ)) ⟶ (L.tensorPow n).restrict V.ι) : Prop :=
  ∀ (i j : ℕ) (W : (Proj 𝒜).Opens)
    (s : Γ(Proj.twist 𝒜 (i : ℤ), W)) (t : Γ(Proj.twist 𝒜 (j : ℤ), W))
    (st : Γ(Proj.twist 𝒜 ((i + j : ℕ) : ℤ), W)),
    (∀ x : W,
      ((st.val x).val : Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) =
        (s.val x).val * (t.val x).val) →
    (θ (i + j)).app (r ⁻¹ᵁ W)
      (projTensorPullbackSection r (Proj.twist 𝒜 ((i + j : ℕ) : ℤ)) W st) =
      projRestrictedPowerMul L V i j (r ⁻¹ᵁ W)
        ((θ i).app (r ⁻¹ᵁ W)
          (projTensorPullbackSection r (Proj.twist 𝒜 (i : ℤ)) W s))
        ((θ j).app (r ⁻¹ᵁ W)
          (projTensorPullbackSection r (Proj.twist 𝒜 (j : ℤ)) W t))

/-- On a degree-`d` generated open, the canonical Proj comparison is an isomorphism,
uniquely determined among all module maps by its homogeneous-section normalization.
The same comparison family respects multiplication in every pair of nonnegative degrees.
Source: Stacks, Constructions, Tag 01NK, final assertion and its graded algebra map;
Tag 01N8, construction and uniqueness (blueprint: lem-trf-proj-invertible-map-twist-iso).

Proof, following the six steps of the DAG node:
1. On the generating open of `ψ(f)`, extend the graded map by sending `b/f^q` to
`ψ(b)/ψ(f)^q`. Its degree-zero part gives the local scheme map. Localization forces
this formula; the maps agree on overlaps and glue to the canonical `r` and comparison.
The global section `b/1` maps to `ψ(b)` by the twisting-sheaf chart description.
2. Degree-`d` generation covers `V` by the generating loci of the images of `A_d`:
a generating family of a rank-one module over a local ring contains a unit coefficient.
This uses invertibility, tensor powers, and the generating-locus definition, without
quasi-compactness or a finite subcover.
3. On `D_+(a)`, multiplication by `a` identifies the structure sheaf with `O(d)`;
its inverse multiplies by the homogeneous fraction `a⁻¹`. The graded-module sheaf
chart description and restriction maps make these inverse sheaf maps.
4. Tensor pullback carries this basis to `1 ⊗ a`. The comparison sends it to `ψ(a)`,
which is a free generator by nonvanishing_section_trivializes. The comparison is the
identity in these bases, so its local inverses glue to an inverse on `V`.
5. Any other module map with the stated normalization agrees on each basis `1 ⊗ a`.
Linearity and the covering sheaf condition imply equality, including on empty `V`.
6. Multiplication sends `(b/f^p)(c/f^q)` to `bc/f^(p+q)`. The localized formula and
multiplicativity of `ψ` give the same product in the tensor-power section ring.
Tensor pullback extends this identity bilinearly; sheafification gives equality of
maps and gluing gives the displayed compatibility on all opens and in all degrees. -/
theorem exists_proj_invertible_map_twist_iso (ψ : A →+* InvertibleSectionRing L)
    (hψ : ∀ (n : ℕ) (a : A), a ∈ 𝒜 n → ψ a ∈ sectionRingGrade L n)
    (d : ℕ) (hd : 0 < d) (V : T.Opens) (hV : V ≤ projSectionMapDomain 𝒜 L ψ)
    (hgen : V ≤ ⨆ a : 𝒜 d, generatingLocus ((ψ a) d)) :
    ∃ (r : V.toScheme ⟶ Proj 𝒜)
      (θ : ∀ n : ℕ,
        (tensorPullback r).obj (Proj.twist 𝒜 (n : ℤ)) ⟶ (L.tensorPow n).restrict V.ι),
      (∀ (e : ℕ) (_he : 0 < e) (a : 𝒜 e),
        V.ι ''ᵁ (r ⁻¹ᵁ Proj.basicOpen 𝒜 a.val) = V ⊓ generatingLocus ((ψ a) e)) ∧
      (∀ n : ℕ, ProjTwistComparisonPreservesSections 𝒜 L ψ V r n (θ n)) ∧
      ProjTwistComparisonMultiplicative 𝒜 L V r θ ∧
      IsIso (θ d) ∧
      (∀ τ : (tensorPullback r).obj (Proj.twist 𝒜 (d : ℤ)) ⟶ (L.tensorPow d).restrict V.ι,
        ProjTwistComparisonPreservesSections 𝒜 L ψ V r d τ → τ = θ d) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
