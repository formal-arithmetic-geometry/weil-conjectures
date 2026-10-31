/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.RationalStalkExact

/-! # The canonical pullback fibre comparison and its closed return square

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2.
(blueprint: lem-fd-weil-pullback-fibre-return).

The comparison is constructed from the existing normalized pullback compositor.
The remaining assertion concerns only its compatibility with return operators;
residue-field arithmetic, heart preservation and eigenvalues are separate arguments.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The inverse normalized compositor at compatible geometric points, followed by
point realization and H^0, naturally on the Weil heart. The point equality fixes
all transports, so this definition chooses no arbitrary fibre isomorphism.
Source: blueprint Step 2, the canonical c_(f,z)
(blueprint: lem-fd-weil-pullback-fibre-return). -/
def fdWeilPullbackFibreComparison
    (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (h : z ≫ zlFiberMap D f₀ = x) :
    zlWeilPull D c.l c.different c.Qbar f₀ ⋙
        wfSheafFibre c.l c.Qbar D c.different X₀ z ≅
      wfSheafFibre c.l c.Qbar D c.different Y₀ x := by
  let hS := frobeniusPointPrimeInvertible D c.l c.different
  let hX := sfWeilPrimeInvertible D c.l c.different X₀
  let hY := sfWeilPrimeInvertible D c.l c.different Y₀
  subst x
  let H := DerivedCategory.coefficientQbarCohomology c.l c.Qbar 0
  let P := pointQbarFibre D c.l c.different c.Qbar
  let T := wfHeartForget c.l c.Qbar D c.different Y₀ ⋙
    (sfCommonStageHeartProperty c.l (D.geometricFiber Y₀).left c.Qbar).ι
  let α := (@zlPullComp c.l _ c.Qbar _ _ _ _ _ _ hS hX hY
    z (zlFiberMap D f₀)).symm
  exact Functor.isoWhiskerLeft T (Functor.isoWhiskerRight α (P ⋙ H))

/-- The canonical fibre comparison intertwines the two closed return operators.
This is only the return-square assertion: it makes no assertion about closed images,
finite residue extensions, heart preservation, or characteristic-polynomial roots.
Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight,
lem-fd-realified-kernel-real.proof.md, Step 2; Weil II (1.1.7)--(1.1.10).
(blueprint: lem-fd-weil-pullback-fibre-return).

Proof:
1. At one finite coefficient field represent the object and its Weil isomorphism;
enlarge once so that both inverse equations hold. Use rationalPullbackFibreComparison
with its simultaneous normalized integral comparison system. Its prescribed component
is the inverse compositor used in fdWeilPullbackFibreComparison.
2. Let d be the degree of the image point over k₀, and e the residue degree of f₀
at z. The residue-field tower law identifies the degree of z with de. Both chosen
geometric points return after de steps. Apply fdPullbackWeilReturnSquare at that
length. Its beta and iterate equation are exactly the induced Weil structure of
zlWeilPull and its iterates after normalization.
3. Apply fdRationalReturnBlockPower at the image point with block length d and e
blocks. It identifies the image-point return at de with the e-th power of the
closed return at d; the same-length square now gives the desired power equation.
4. The scalar square of rationalPullbackFibreComparison and all four equations of
localFrobeniusCoefficientExtension identify this equation after coefficient
extension, including identity extensions and arbitrary towers. Therefore it descends
to the actual common-stage category, independently of the finite representative.
5. The recorded normalizations identify these common-stage return maps with
wfClosedFrobenius. Apply coefficient H^0; functoriality preserves compositions and
powers. Its image of the normalized compositor is precisely the comparison defined
above. This proves the displayed equation, also for zero stalks and e=1. -/
theorem fdWeilPullbackFibreReturn
    [IsSeparated X₀.hom] [IsSeparated Y₀.hom] (f₀ : X₀ ⟶ Y₀)
    (z : {z : X₀.left // z ∈ closedPoints X₀.left})
    (hx : f₀.left.base z.val ∈ closedPoints Y₀.left)
    (ιz : X₀.left.residueField z.val →+* D.k)
    (hz : ιz.comp (X₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
    (ιx : Y₀.left.residueField (f₀.left.base z.val) →+* D.k)
    (hxι : ιx.comp (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val)) =
      algebraMap D.k₀ D.k)
    (h : localClosedPoint D X₀ z ιz hz ≫ zlFiberMap D f₀ =
      localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hxι)
    (F : sfCommonStageWeilSheaf D c.l c.different Y₀ c.Qbar) :
    wfSheafClosedFrobenius c.l c.Qbar D c.different X₀
        ((zlWeilPull D c.l c.different c.Qbar f₀).obj F) z ιz hz ≫
      (fdWeilPullbackFibreComparison D c X₀ Y₀ f₀
        (localClosedPoint D X₀ z ιz hz)
        (localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hxι) h).hom.app F =
    (fdWeilPullbackFibreComparison D c X₀ Y₀ f₀
      (localClosedPoint D X₀ z ιz hz)
      (localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hxι) h).hom.app F ≫
      ModuleCat.ofHom
        ((wfSheafClosedFrobenius c.l c.Qbar D c.different Y₀ F
          ⟨f₀.left.base z.val, hx⟩ ιx hxι).hom ^ f₀.left.residueDegree z.val) := by sorry

end WeilConjectures
