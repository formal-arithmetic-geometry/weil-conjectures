/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeilTateTwist.WeilTateTwistConventions
public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Affine-line and weight conventions with condensed coefficients

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
rem-dl-a1-conventions.md, all definition paragraphs (blueprint: rem-dl-a1-conventions).

The carrier of a Weil sheaf is a constructible module over the pulled-back
finite-subextension-valued condensed algebraic closure. The Weil structure uses
geometric Frobenius. Constancy forgets that structure, whereas irreducibility
and extension across infinity retain it. Ordinary direct image and its shift use
the recorded module direct image, retaining higher images in derived formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.DeligneLaumon.AffineLine

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]

/-- The standard affine line over the finite field; the dual line is another copy.
Source: rem-dl-a1-conventions, opening paragraph (blueprint: rem-dl-a1-conventions). -/
abbrev baseLine : Scheme.{u} := affineLine D.k₀

/-- The fixed geometric affine line, using the recorded geometric base change.
Source: rem-dl-a1-conventions, A = A_0 tensor k (blueprint: rem-dl-a1-conventions). -/
abbrev geometricLine :=
  pullback (baseLine D ↘ Spec (.of D.k₀))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- The geometric fibre without a finiteness restriction on the model.
Source: rem-dl-a1-conventions, U = U_0 tensor k (blueprint: rem-dl-a1-conventions). -/
abbrev geometricScheme (T₀ : Over (Spec (.of D.k₀))) :=
  pullback T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

variable (U₀ : Over (Spec (.of D.k₀)))

/-- Constructible actual condensed modules with an isomorphism Fr^* F to F.
This full subcategory uses exactly the coefficient-heart constructibility predicate.
Source: rem-dl-a1-conventions, Weil-sheaf paragraph
(blueprint: rem-dl-a1-conventions). -/
abbrev WeilSheaf := ObjectProperty.FullSubcategory
  (fun F : condensedWeilModules (Profinite.padicAlgClRingObj ell)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D U₀).hom ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (geometricScheme D U₀) F.carrier)

variable {D ell U₀}

/-- Lisse means pro-etale locally free of finite rank, including rank zero.
Source: rem-dl-a1-conventions, Weil-sheaf paragraph
(blueprint: rem-dl-a1-conventions). -/
abbrev IsLisse (F : WeilSheaf D ell U₀) : Prop :=
  IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F.obj.carrier

section Weights

variable [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]

/-- The punctual upper weight bound replaces equality by less than or equal to.
It does not mean existence of a mixed filtration.
Source: rem-dl-a1-conventions, purity paragraph (blueprint: rem-dl-a1-conventions). -/
def WeightAtMost (F : WeilSheaf D ell U₀) (iota : PadicAlgCl ell →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : {x : U₀.left // x ∈ closedPoints U₀.left})
    (i : U₀.left.residueField x.val →+* D.k)
    (hi : i.comp (U₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl ell)),
    Module.End.HasEigenvalue (NativeL2.closedOperator D ell U₀ F.obj x i hi).hom α →
      ‖iota α.down‖ ≤ (Nat.card (U₀.left.residueField x.val) : ℝ) ^ (w / 2)

/-- The fixed coefficient prime is a unit in every geometric residue field.
Source: rem-dl-a1-conventions, ell different from the characteristic
(blueprint: rem-dl-a1-conventions).
Proof: the residue field is a field over k through the geometric structure map.
It therefore has characteristic p. The prime ell differs from p, so its image
is nonzero and hence a unit. This also applies when the scheme has no points. -/
theorem coefficientPrimeIsUnit (hEll : ell ≠ D.p) :
    ∀ x : geometricScheme D U₀, IsUnit (ell : (geometricScheme D U₀).residueField x) := by
  sorry

/-- The published root-normalized twist, restricted to the constructible Weil heart.
Source: rem-dl-a1-conventions, Tate normalization (blueprint: rem-dl-a1-conventions). -/
def tateTwist (hEll : ell ≠ D.p) (F : WeilSheaf D ell U₀) (m : ℤ) :
    WeilSheaf D ell U₀ :=
  letI : ∀ x : (D.geometricFiber U₀).left,
      Invertible (ell : (D.geometricFiber U₀).left.residueField x) :=
    fun x ↦ (coefficientPrimeIsUnit hEll x).invertible
  (CondensedRing.WeilTateTwist.heart ell .closure
    (CondensedRing.StrictWeilCondensed.modelFrobenius D U₀) m).obj F

/-- The (-1) twist raises both punctual weights and their upper bounds by two.
Source: rem-dl-a1-conventions, Tate normalization (blueprint: rem-dl-a1-conventions).
Proof: apply lem-tw-tate-twist-weight-shift to the specified root-normalized twist.
At a closed point of degree d, geometric Frobenius on the (-1) line has scalar
q^d = q_x. Tensoring multiplies every eigenvalue by q_x, so its complex absolute
value is multiplied by q_x. This changes w/2 to (w+2)/2 in both the equality
and inequality. The argument includes zero fibres and makes no semisimplicity claim. -/
theorem negativeOne_weight_shift (hEll : ell ≠ D.p) (F : WeilSheaf D ell U₀)
    (_hF : IsLisse F) (iota : PadicAlgCl ell →+* ℂ) (w : ℝ) :
    (Pure F iota w → Pure (tateTwist hEll F (-1)) iota (w + 2)) ∧
    (WeightAtMost F iota w → WeightAtMost (tateTwist hEll F (-1)) iota (w + 2)) := by
  sorry

end Weights

/-- Nonzero simplicity among lisse Weil sheaves: every lisse Weil subsheaf is
zero or the entire sheaf. No condition on arbitrary non-lisse subsheaves is imposed.
Source: rem-dl-a1-conventions, irreducible-lisse paragraph
(blueprint: rem-dl-a1-conventions). -/
def IsIrreducibleLisse (F : WeilSheaf D ell U₀) : Prop :=
  IsLisse F ∧ ¬ IsZero F.obj ∧
    ∀ (G : WeilSheaf D ell U₀) (i : G.obj ⟶ F.obj), Mono i → IsLisse G →
      IsZero G.obj ∨ IsIso i

/-- A nonzero lisse Weil sheaf on a smooth curve has a nonzero proper Weil subsheaf.
Source: rem-dl-a1-conventions, distinction from simplicity in all Weil sheaves
(blueprint: rem-dl-a1-conventions).
Proof: choose a closed point on a positive-rank component and remove it. Extension
by zero of the restriction is constructible and carries the induced Weil structure,
since the removed closed point is defined over k_0. The open/closed localization
sequence gives its monomorphism into F. Restriction to the nonempty complement
shows that it is nonzero; the stalk at the removed point is zero while the stalk
of F has positive rank, so this monomorphism is not an isomorphism. This uses
lem-zl-condensed-open-extension-local and the exact open/closed sequence, as in
step 4 of the node's recorded proof. -/
theorem lisse_has_proper_subsheaf [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom] [SmoothOfRelativeDimension 1 U₀.hom]
    (_hEll : ell ≠ D.p) (F : WeilSheaf D ell U₀) (_hF : IsLisse F)
    (_hne : ¬ IsZero F.obj) :
    ∃ (G : WeilSheaf D ell U₀) (i : G.obj ⟶ F.obj),
      Mono i ∧ ¬ IsZero G.obj ∧ ¬ IsIso i := by
  sorry

/-- On every connected geometric open the underlying module is a finite sum of
coefficient units, equivalently p_V^* of a finite-dimensional constant vector space.
The isomorphism is of modules and imposes no restriction on the Weil operator.
Source: rem-dl-a1-conventions, geometric-constancy paragraph
(blueprint: rem-dl-a1-conventions). -/
def IsGeometricallyConstant (F : WeilSheaf D ell U₀) : Prop :=
  ∀ V : (geometricScheme D U₀).Opens, ConnectedSpace V →
    ∃ n : ℕ, Nonempty ((CondensedRing.upperStar
      (Profinite.padicAlgClRingObj ell) V.ι).obj F.obj.carrier ≅
      Mod.finiteFree (condensedRingObj (Profinite.padicAlgClRingObj ell) V.toScheme) n)

variable {C₀ : Over (Spec (.of D.k₀))}

/-- The canonical base change of a morphism of models.
Source: rem-dl-a1-conventions, geometric convention (blueprint: rem-dl-a1-conventions). -/
abbrev geometricMap (j₀ : U₀ ⟶ C₀) : geometricScheme D U₀ ⟶ geometricScheme D C₀ :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left

/-- The actual geometric Frobenius commutes with every map of models.
Source: rem-dl-a1-conventions, geometric convention (blueprint: rem-dl-a1-conventions).
Proof: both composites fix the projection to the model and have coefficient projection
followed by Spec of inverse q-power. The pullback universal property identifies them. -/
theorem frobeniusSquare (j₀ : U₀ ⟶ C₀) :
    CommSq (CondensedRing.StrictWeilCondensed.modelFrobenius D U₀).hom
      (geometricMap j₀) (geometricMap j₀)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D C₀).hom := by
  sorry

/-- Ordinary module direct image on the actual geometric fibres.
Source: rem-dl-a1-conventions, ordinary j_* paragraph
(blueprint: rem-dl-a1-conventions). -/
abbrev ordinaryDirectImage (j₀ : U₀ ⟶ C₀) (F : WeilSheaf D ell U₀) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
    (geometricMap j₀)).obj F.obj.carrier

/-- The expression (j_*F)[1]: ordinary image, degree-zero inclusion, then shift.
Source: rem-dl-a1-conventions, intermediate-extension expression
(blueprint: rem-dl-a1-conventions). -/
abbrev shiftedOrdinaryDirectImage (j₀ : U₀ ⟶ C₀) (F : WeilSheaf D ell U₀) :=
  ((DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ (1 : ℤ)).obj
    (ordinaryDirectImage j₀ F))

/-- Restrict an actual Weil module using the canonical Frobenius square comparison.
Source: rem-dl-a1-conventions, lisse extension with its Weil structure
(blueprint: rem-dl-a1-conventions). -/
def restrictWeil (j₀ : U₀ ⟶ C₀) :
    condensedWeilModules (Profinite.padicAlgClRingObj ell)
        (CondensedRing.StrictWeilCondensed.modelFrobenius D C₀).hom ⥤
      condensedWeilModules (Profinite.padicAlgClRingObj ell)
        (CondensedRing.StrictWeilCondensed.modelFrobenius D U₀).hom :=
  Endofunctor.IsoAlgebra.mapOfNatIso
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj ell)
      (frobeniusSquare j₀)).symm

/-- The finite-field model of a projective-line open.
Source: rem-dl-a1-conventions, U_0 union infinity
(blueprint: rem-dl-a1-conventions). -/
abbrev projectiveOpenModel (D : FiniteFieldDatum.{u})
    (W : (ProjectiveLine (Spec (.of D.k₀))).Opens) : Over (Spec (.of D.k₀)) :=
  Over.mk (W.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))

/-- Extension to precisely the open U_0 union infinity, with its lisse Weil structure.
The image equation fixes the extension domain and the factorization fixes restriction.
Source: rem-dl-a1-conventions, unramified-at-infinity paragraph
(blueprint: rem-dl-a1-conventions). -/
def IsUnramifiedAtInfinity (F : WeilSheaf D ell U₀)
    (j : U₀.left ⟶ baseLine D) [IsOpenImmersion j] : Prop :=
  ∃ W : (ProjectiveLine (Spec (.of D.k₀))).Opens,
    (W : Set (ProjectiveLine (Spec (.of D.k₀)))) =
      Set.range (j ≫ ProjectiveLine.affineChart (Spec (.of D.k₀))).base ∪
        ((ProjectiveLine.affineChart (Spec (.of D.k₀))).opensRange : Set _)ᶜ ∧
    ∃ (f₀ : U₀ ⟶ projectiveOpenModel D W),
      f₀.left ≫ W.ι = j ≫ ProjectiveLine.affineChart (Spec (.of D.k₀)) ∧
      ∃ G : WeilSheaf D ell (projectiveOpenModel D W),
        IsLisse G ∧ Nonempty ((restrictWeil f₀).obj G.obj ≅ F.obj)

end WeilConjectures.DeligneLaumon.AffineLine
