/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Exactness of ordinary middle extension at one pure weight

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-exact/
p-dl-a1-exact.md and p-dl-a1-exact.proof.md, Steps 1--5
(blueprint: p-dl-a1-exact).

The curve may be non-quasi-compact and non-separated. The existing finite-type
coefficient and purity interfaces are used on finite-type open models. The geometric
base change and Frobenius below merely expose their existing constructions without
the unused global quasi-compactness arguments. Purity is tested by the recorded
NativeL2.Pure on every finite-type open, as in the local argument of the source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CurvePureExactness

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- Geometric base change, including non-quasi-compact models: the exact pullback used
by FiniteFieldDatum.geometricFiber, without its finite-type packaging arguments.
Source: rem-dl-a1-conventions and p-dl-a1-exact, geometric schemes U and C
(blueprint: p-dl-a1-exact). -/
abbrev fiber (X₀ : Over (Spec (.of D.k₀))) : Over (Spec (.of D.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀

/-- The same geometric Frobenius as FiniteFieldDatum.geometricFrobenius. Its construction
uses the existing Galois base-change map and its inverse, and needs no quasi-compactness.
Source: rem-dl-a1-conventions; def-weil-frobenius-detailed
(blueprint: p-dl-a1-exact). -/
def frobenius (X₀ : Over (Spec (.of D.k₀))) : Aut (fiber D X₀).left :=
  letI := Fintype.ofFinite D.k₀
  { hom := D.galoisMap X₀.hom (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
    inv := D.galoisMap X₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    hom_inv_id := (D.galoisMap_inverse X₀.hom _).1
    inv_hom_id := (D.galoisMap_inverse X₀.hom _).2 }

/-- Actual condensed Weil modules on the geometric curve, using the recorded fixed-pair
category and pulled-back finite-subextension-valued Qbar coefficient ring.
Source: rem-dl-a1-conventions, Weil-sheaf paragraph (blueprint: p-dl-a1-exact). -/
abbrev Modules (X₀ : Over (Spec (.of D.k₀))) :=
  condensedWeilModules (Profinite.padicAlgClRingObj l) (frobenius D X₀).hom

/-- The actual base change of a model morphism, as in NativeL2.geometricMap.
Source: p-dl-a1-exact, the geometric open immersion (blueprint: p-dl-a1-exact). -/
abbrev geometricMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :
    (fiber D X₀).left ⟶ (fiber D Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- The geometric Frobenius square for this actual base-change morphism.
Source: p-dl-a1-exact.proof.md, Step 1, operation structures
(blueprint: p-dl-a1-exact).
Proof: compose with each fibre-product projection. The model projection on both
sides is the original map after projection. The coefficient projection on both sides
is projection followed by Spec of inverse q-power Frobenius. Pullback uniqueness
therefore gives the square, with no geometric finiteness hypothesis. -/
theorem frobeniusSquare {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :
    CommSq (frobenius D X₀).hom (geometricMap D f₀)
      (geometricMap D f₀) (frobenius D Y₀).hom := by
  let := Fintype.ofFinite D.k₀
  refine ⟨?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, geometricMap, Over.pullback_map_left, pullback.lift_fst]
    simp only [← Category.assoc, frobenius]
    rw [(D.galoisMap_projections _ _).1]
    rw [Category.assoc, (D.galoisMap_projections _ _).1]
    simp only [pullback.lift_fst]
  · simp only [Category.assoc, geometricMap, Over.pullback_map_left, pullback.lift_snd]
    simp only [frobenius]
    rw [(D.galoisMap_projections _ _).2]
    rw [(D.galoisMap_projections _ _).2]
    rw [← Category.assoc, pullback.lift_snd]

/-- Ordinary direct image with its canonical Frobenius base-change mate. On finite-type
models its objects are exactly NativeL2.middleWeilImage, with the same carrier and maps.
The two horizontal Frobenius maps are isomorphisms, so their base-change mate is invertible.
Source: def-wf-middle-extension, ordinary direct image; p-dl-a1-exact displayed sequence
(blueprint: p-dl-a1-exact). -/
abbrev directImage {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :
    Modules D l X₀ ⥤ Modules D l Y₀ :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
      (frobeniusSquare D f₀)))

/-- Restrict a Weil module along the model open by the existing module inverse image
and its canonical Frobenius square comparison. No extra Weil structure is chosen.
Source: p-dl-a1-exact.proof.md, Step 1, restriction to finite-type affine opens
(blueprint: p-dl-a1-exact). -/
abbrev restriction {X₀ Y₀ : Over (Spec (.of D.k₀))} (a₀ : X₀ ⟶ Y₀) :
    Modules D l Y₀ ⥤ Modules D l X₀ :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (frobeniusSquare D a₀)).symm

/-- The recorded punctual-purity predicate on every finite-type open model. This
extends its domain to a locally finite-type curve without adding global finiteness.
Every closed point has a finite-type affine neighbourhood, so this tests exactly the
same local Frobenius eigenvalues as NativeL2.Pure, including all compatible lifts.
Source: def-weil-punctual-weights; p-dl-a1-exact.proof.md, Step 1
(blueprint: p-dl-a1-exact). -/
def pureOnFiniteTypeOpens (X₀ : Over (Spec (.of D.k₀))) (M : Modules D l X₀)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ (V₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    (a₀ : V₀ ⟶ X₀) [IsOpenImmersion a₀.left],
    NativeL2.Pure D l V₀ ((restriction D l a₀).obj M) iota w

/-- Ordinary middle extension is exact on a short exact sequence of lisse Weil sheaves
whose outer terms are punctually pure of one common real weight. The three
constructibility assertions say that this is indeed a sequence of Weil sheaves;
exactness is expressed under their exact full inclusion into ambient Weil modules.
Source: latest blueprint, p-dl-a1-exact.md and p-dl-a1-exact.proof.md, Steps 1--5
(blueprint: p-dl-a1-exact).
Proof: restrict to finite-type affine opens W of C. The underlying derived triangle
and H0 identification give j_*F1 → j_*F → j_*F2 → R1j_*F1, with Weil-equivariant
connecting map delta and delta zero on U. Constructible images and exact closed
fibres reduce delta=0 to vector spaces. Split geometric components by finite constant
extension to apply connected-curve boundary estimates, treating rank zero separately.
At each missing closed point, write Q=#kappa(t)>1. Semicontinuity bounds eigenvalues
of j_*F2 by |iota(alpha)|² ≤ Q^w. Apply semicontinuity to F1 dual, boundary duality,
and the Tate scalar Q^(-1): target eigenvalues satisfy |iota(gamma)|² ≥ Q^(w+2).
The image of delta is a quotient of the source and a subspace of the target, stable
under invertible Frobenius. Spectrum exactness would place each of its eigenvalues
between Q^(w+2) and Q^w. This is impossible. Triangularization supplies an eigenvalue
for any nonzero finite-dimensional image, so every image fibre is zero. Closed-fibre
detection gives delta=0 on W; the resulting short exact sequences glue over C.
No separatedness, global quasi-compactness, or geometric connectedness is imposed. -/
theorem shortExact_directImage (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {U₀ C₀ Z₀ : Over (Spec (.of D.k₀))}
    [SmoothOfRelativeDimension 1 C₀.hom]
    (j₀ : U₀ ⟶ C₀) [IsOpenImmersion j₀.left] [QuasiCompact j₀.left]
    [IsDominant j₀.left]
    (i₀ : Z₀ ⟶ C₀) [IsClosedImmersion i₀.left]
    (hcomplement : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ)
    (S : ShortComplex (Modules D l U₀)) (hS : S.ShortExact)
    (h₁ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₁.carrier)
    (h : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₂.carrier)
    (h₂ : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) S.X₃.carrier)
    (w : ℝ) (p₁ : pureOnFiniteTypeOpens D l U₀ S.X₁ iota w)
    (p₂ : pureOnFiniteTypeOpens D l U₀ S.X₃ iota w) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (fiber D C₀).left
      ((directImage D l j₀).obj S.X₁).carrier ∧
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (fiber D C₀).left
      ((directImage D l j₀).obj S.X₂).carrier ∧
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (fiber D C₀).left
      ((directImage D l j₀).obj S.X₃).carrier ∧
    (S.map (directImage D l j₀)).ShortExact := by
  sorry

end WeilConjectures.CurvePureExactness
