/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary

/-!
# Finite-field quasi-separated proper/open pasting

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting).

The statement uses the native condensed coefficient, derived module operations, open
lower-shriek, normalized proper/open pasting package, and native compactification
reindexing map.  No separatedness, Cartesian condition, density condition, or
invertibility of `Gamma` is added.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.classDefReducibility false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing
open CondensedOpenProper

/-- The standing scope of the statement: a structure of `X` over `Spec k` which is locally
of finite type, quasi-compact and quasi-separated.  No separatedness is assumed.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting). -/
class QcqsFiniteType (k : Type u) [Field k] (X : Scheme.{u}) : Type (u + 1) where
  hOver : X.Over (Spec (CommRingCat.of k))
  hLocallyOfFiniteType : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))
  hQuasiCompact : QuasiCompact (X ↘ Spec (CommRingCat.of k))
  hQuasiSeparated : QuasiSeparated (X ↘ Spec (CommRingCat.of k))

attribute [instance] QcqsFiniteType.hOver QcqsFiniteType.hLocallyOfFiniteType
  QcqsFiniteType.hQuasiCompact QcqsFiniteType.hQuasiSeparated

/-- The refinement comparison obtained from the Gamma map on the square
`c₁.i, 𝟙 X, u.hom, c₂.i`, followed by the native proper compositor and the
congruence induced by `u.hom_g`.  This is the actual comparison whose equality
with the native clopen-projector refinement map is asserted below.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting).
-/
def refinementGamma
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (units : OpenUnits Λ)
    (u : c₁.Refinement c₂) :
    (CompactificationReindexing.F Λ c₂) ⟶ (CompactificationReindexing.F Λ c₁) := by
  let sq : CommSq c₁.i (𝟙 X) u.hom c₂.i := ⟨u.i_hom⟩
  let m : CondensedOpenProper.J Λ c₂.i ⟶
      CondensedOpenProper.J Λ c₁.i ⋙ CondensedOpenProper.R Λ u.hom :=
    Functor.whiskerRight (CondensedOpenProper.rId Λ X).inv
        (CondensedOpenProper.J Λ c₂.i) ≫
      CondensedOpenProper.gamma Λ units sq
  exact
    Functor.whiskerRight m (CondensedOpenProper.R Λ c₂.g) ≫
      Functor.whiskerLeft (CondensedOpenProper.J Λ c₁.i)
        ((CondensedOpenProper.rComp Λ u.hom c₂.g).hom ≫
          (eqToIso (congrArg (CondensedOpenProper.R Λ) u.hom_g)).hom)

/-- The qcqs finite-type proper/open laws, with canonical open units and the inverse
open-map exchange.  Every scheme binder carries the explicit finite-type, quasi-compact,
quasi-separated structure over `k`; no unrestricted `Pasting` package is quantified.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting).
-/
structure QcqsFinitePasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] : Type (u + 3) where
  units : OpenUnits Λ
  B : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j'],
    IsPullback a j' j b → (J Λ j ⋙ P Λ b ≅ P Λ a ⋙ J Λ j')
  B_normalized : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b), (B sq).inv = openMap Λ sq.toCommSq
  gamma_vertical : ∀ {U W Y Z V T : Scheme.{u}}
    [QcqsFiniteType k U] [QcqsFiniteType k W] [QcqsFiniteType k Y]
    [QcqsFiniteType k Z] [QcqsFiniteType k V] [QcqsFiniteType k T]
    {j : U ⟶ W} {i : Y ⟶ Z} {l : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion l]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact l]
    [IsProper p₁] [IsProper p₂] [IsProper r₁] [IsProper r₂]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ l)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) l)
    (K : D Λ U),
    (gamma Λ units q).app K =
      (J Λ l).map ((rComp Λ p₁ p₂).inv.app K) ≫
      (gamma Λ units q₂).app ((R Λ p₁).obj K) ≫
      (R Λ r₂).map ((gamma Λ units q₁).app K) ≫
      (rComp Λ r₁ r₂).hom.app ((J Λ j).obj K)
  gamma_horizontal : ∀ {U W V Y Z T : Scheme.{u}}
    [QcqsFiniteType k U] [QcqsFiniteType k W] [QcqsFiniteType k V]
    [QcqsFiniteType k Y] [QcqsFiniteType k Z] [QcqsFiniteType k T]
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact j₁] [QuasiCompact j₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper p] [IsProper r] [IsProper s]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂)) (K : D Λ U),
    (gamma Λ units q).app K =
      (jComp Λ i₁ i₂).inv.app ((R Λ p).obj K) ≫
      (J Λ i₂).map ((gamma Λ units q₁).app K) ≫
      (gamma Λ units q₂).app ((J Λ j₁).obj K) ≫
      (R Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  gamma_vertical_id : ∀ {U W : Scheme.{u}} [QcqsFiniteType k U] [QcqsFiniteType k W]
    (j : U ⟶ W) [IsOpenImmersion j] [QuasiCompact j]
    (sq : CommSq j (𝟙 U) (𝟙 W) j) (K : D Λ U),
    (gamma Λ units sq).app K =
      (J Λ j).map ((rId Λ U).hom.app K) ≫ (rId Λ W).inv.app ((J Λ j).obj K)
  gamma_horizontal_id : ∀ {U Y : Scheme.{u}} [QcqsFiniteType k U] [QcqsFiniteType k Y]
    (p : U ⟶ Y) (sq : CommSq (𝟙 U) p p (𝟙 Y)) (K : D Λ U),
    (gamma Λ units sq).app K =
      (jId Λ Y).hom.app ((R Λ p).obj K) ≫ (R Λ p).map ((jId Λ U).inv.app K)
  cube : ∀ {U W Y Z U' W' Y' Z' : Scheme.{u}}
    [QcqsFiniteType k U] [QcqsFiniteType k W] [QcqsFiniteType k Y]
    [QcqsFiniteType k Z] [QcqsFiniteType k U'] [QcqsFiniteType k W']
    [QcqsFiniteType k Y'] [QcqsFiniteType k Z']
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact j'] [QuasiCompact i'] [IsIso b]
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (_hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY)
    (K : BoundedConstructible (condensedRingObj Λ U))
    (_hD :
      boundedConstructible (condensedRingObj Λ Z)
          ((J Λ i).obj ((R Λ p).obj K.obj)) ∧
      boundedConstructible (condensedRingObj Λ Z)
          ((R Λ r).obj ((J Λ j).obj K.obj)) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((P Λ b).obj ((J Λ i).obj ((R Λ p).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((P Λ b).obj ((R Λ r).obj ((J Λ j).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((R Λ r').obj ((P Λ aW).obj ((J Λ j).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((R Λ r').obj ((J Λ j').obj ((P Λ aU).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((J Λ i').obj ((P Λ aY).obj ((R Λ p).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ Y')
          ((P Λ aY).obj ((R Λ p).obj K.obj)) ∧
      boundedConstructible (condensedRingObj Λ Y')
          ((R Λ p').obj ((P Λ aU).obj K.obj)) ∧
      boundedConstructible (condensedRingObj Λ Z')
          ((J Λ i').obj ((R Λ p').obj ((P Λ aU).obj K.obj))) ∧
      boundedConstructible (condensedRingObj Λ W')
          ((J Λ j').obj ((P Λ aU).obj K.obj))) ,
    (P Λ b).map ((gamma Λ units q).app K.obj) ≫
      (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K.obj) ≫
      (R Λ r').map ((B qj).hom.app K.obj) =
    (B qi).hom.app ((R Λ p).obj K.obj) ≫
      (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K.obj) ≫
      (gamma Λ units q').app ((P Λ aU).obj K.obj)

/-- The finite-field proper/open package required by the node.

The existential data are the canonical normalized open units and the qcqs finite-type
proper/open laws.  The refinement equality is stated only for separated finite-type
compactification maps, as required by the native reindexing construction.
Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting).
-/
def FiniteFieldQcqsProperOpenPasting
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) : Prop :=
  ∃ data : QcqsFinitePasting (Profinite.padicAlgClRingObj.{u} ell) D.k,
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f] (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂),
      refinementGamma (Profinite.padicAlgClRingObj.{u} ell) data.units u =
      CompactificationReindexing.refinement (Profinite.padicAlgClRingObj.{u} ell) u

/-- Finite-field quasi-separated proper/open pasting with native refinement normalization.

Proof steps, corresponding to the eight proof records in the DAG:

1. The finite-field fibre datum fixes `k₀ = F_q`, `k = algebraic closure k₀`, and
`ell ≠ char(k₀)`.  The condensed coefficient, pulled-back coefficient modules,
ordinary module-derived operations, and open lower-shriek are exactly the cited
interfaces.  The internal-module transport and exact derived-transformation
pasting identify their section-ring realizations, units, counits, and compositors
with the native `P`, `R`, and `J` operations, so every square is in the stated
quasi-separated finite-type scope.

2. For a proper/open square, form `V = W ×_Z Y` with projections `t`, `q` and
section `s = (j,p)`.  Base change makes `t` open and `q` proper; proper-over-separated
makes `s` proper, and proper immersion closed plus `t s = j` makes the image of `s`
clopen.  Clopen module gluing and its unbounded derived localization identify `J_s`
with the zero-insertion right adjoint and hence with `R_s`; the direct-image
compositor gives `R_q J_s ≅ R_p`.  The canonical open restriction is therefore the
specified support map `lambda_Q`, without assuming that `Q` is Cartesian.

3. Let `pi_s` be the first-coordinate projector.  The normalized open exchange
constructs `A_Q : P_r J_i → J_j P_p` by applying `B` and inserting `J_s pi_s`.
The proper adjunction mate has the explicit formula
`R_r(J_j eps_p) ; R_r(A_Q R_p) ; eta_r J_i R_p`; under the open-adjunction
transpose the unit/counit cancel and `pi_s` is exactly the clopen inclusion/projection,
so this mate is the specified `Gamma_Q`.

4. Fully faithful open extension can be cancelled after applying `B`.  On the
clopen decomposition the two coordinates detect morphism equality; the projector
is `(1,0)` on the section and zero on the complement.  This coordinate calculation
proves the vertical, horizontal, and identity equations for `A_Q`, with the native
open compositors and pullback coherence.

5. Apply the two mate-pasting formulas to those `A_Q` equations and to
`G_Q = Gamma_Q`.  The normalized composite adjunctions identify the derived
compositors with the specified conjugates, giving the vertical and horizontal
`Gamma` laws and the two identity normalizations.  The closed tensor and
Grothendieck-module results ensure these are equalities of the stated natural
transformations.

6. Pull the clopen factorization back along the arbitrary scheme isomorphism `b`.
The section and complementary component pull back, and clopen localization identifies
both pulled-back projectors with `(1,0)`.  Exact pullback and the open/proper base
change comparisons give the inverse-image cube, including its canonical fibre-product
maps, on the displayed bounded-constructible inputs.

7. Take proper-adjunction mates of that inverse-image cube.  The mates of the two
pullback comparisons are exactly `Ex_r` and `Ex_p`, while the mates of `A_Q` and
`A_Q'` are `Gamma_Q` and `Gamma_Q'`.  The resulting equality is the displayed
`B/Ex/Gamma` cube.  Only canonical open comparisons and fibre-product
identifications are inverted; neither a proper exchange nor `Gamma` is assumed
invertible.

8. For a separated finite-type compactification refinement, the open fibre-product
section is clopen and gives the native refinement adjunct, identity on the section
and zero on its complementary component.  The mate calculation in steps 2--3
identifies its proper mate with `Gamma` on the refinement square.  Whiskering by
the second proper map and applying the direct-image compositor and the congruence
along `u.hom_g` is exactly the native `CompactificationReindexing.refinement` map.

Source: `literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/`
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-thm-dl-general-sheaf/lem-zl-composition-weight-bound.proof.md`, proof paragraph 1
(blueprint: lem-zl-finite-field-qcqs-proper-open-pasting).
-/
theorem finiteFieldQcqsProperOpenPasting
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) : FiniteFieldQcqsProperOpenPasting D ell _hEll := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
