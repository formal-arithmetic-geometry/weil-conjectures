module

public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDatum
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # The relative multiplicative group

Source: Stacks Project, Groupoids, Tag 022U; the relative Laurent-spectrum construction.
(blueprint: def-sfb-relative-multiplicative-group)
This uses the Laurent Hopf algebra over the global-section ring and its actual
base change, so works for every base scheme without a field hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.RelativeMultiplicativeGroup

/-- The Laurent Hopf scheme over the global-section affine base, without a field
restriction. Source: Stacks Tag 022U; Moret-Bailly I §2
(blueprint: def-sfb-relative-multiplicative-group). -/
abbrev affineMultiplicative (S : Scheme.{u}) : Over (Spec Γ(S, ⊤)) :=
  (Spec (.of (LaurentPolynomial Γ(S, ⊤)))).asOver (Spec Γ(S, ⊤))


/-- The actual relative multiplicative scheme, obtained by base change of the Laurent
Hopf scheme. Source: Stacks Tag 022U; Moret-Bailly I §2
(blueprint: def-sfb-relative-multiplicative-group). -/
abbrev laurentModel (S : Scheme.{u}) : Over S :=
  (Over.pullback S.toSpecΓ).obj (affineMultiplicative S)


/-- The pulled-back Laurent Hopf group law. Source: Stacks Tag 022U
(blueprint: def-sfb-relative-multiplicative-group). -/
instance laurentModelGroup (S : Scheme.{u}) : GrpObj (laurentModel S) :=
  ((Over.pullback S.toSpecΓ).mapGrp.obj (Grp.mk (affineMultiplicative S))).grp


/-- The already defined punctured affine line, with its actual projection.
Source: Stacks Tag 022U (blueprint: def-sfb-relative-multiplicative-group). -/
abbrev multiplicative (S : Scheme.{u}) : Over S :=
  Over.mk ((Etale.multiplicativeGroup S).ι ≫
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))

/-- The Laurent coordinate on its explicit affine pullback model.
Source: Stacks Tag 022U (blueprint: def-sfb-relative-multiplicative-group). -/
def laurentCoordinate (S : Scheme.{u}) : Γ((laurentModel S).left, ⊤) :=
  (pullback.fst (affineMultiplicative S).hom S.toSpecΓ).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial Γ(S, ⊤)))).inv (LaurentPolynomial.T 1))

/-- The coordinate-preserving comparison with the existing punctured affine line is
unique. Source: Stacks Tag 022U (blueprint: def-sfb-relative-multiplicative-group).
Proof: on an affine open Spec R of S both schemes are Spec R[t,t inverse].
The identity of R and the prescribed image of t uniquely determine the coordinate
ring map and its inverse. These maps commute with localization on smaller affine
opens, so glue uniquely. Their composites are identity on R and t and hence are
identity scheme morphisms. The coordinate equation fixes the comparison uniquely. -/
theorem comparison_existsUnique (S : Scheme.{u}) :
    ∃! e : laurentModel S ≅ multiplicative S,
      e.hom.left.appTop (Etale.multiplicativeGroupCoord S :
        Γ((Etale.multiplicativeGroup S).toScheme, ⊤)) = laurentCoordinate S := by
  sorry

/-- The comparison fixed uniquely by the Laurent coordinate, never an arbitrary
isomorphism. Source: Stacks Tag 022U (blueprint: def-sfb-relative-multiplicative-group). -/
def comparison (S : Scheme.{u}) : laurentModel S ≅ multiplicative S :=
  Classical.choose (comparison_existsUnique S)

/-- The Laurent Hopf group law on the existing punctured line, transported through
its uniquely normalized coordinate comparison. Source: Stacks Tag 022U
(blueprint: def-sfb-relative-multiplicative-group). -/
instance multiplicativeGroup (S : Scheme.{u}) : GrpObj (multiplicative S) :=
  GrpObj.ofIso (comparison S)

/-- The existing tautological unit evaluated at a generalized point.
Source: Stacks Tag 022U (blueprint: def-sfb-relative-multiplicative-group). -/
def scalar {S : Scheme.{u}} {T : Over S} (a : T ⟶ multiplicative S) : Γ(T.left, ⊤) :=
  a.left.appTop (Etale.multiplicativeGroupCoord S :
    Γ((Etale.multiplicativeGroup S).toScheme, ⊤))

end AlgebraicGeometry.RelativeMultiplicativeGroup
