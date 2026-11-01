/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Geometric bounded constructible open/proper pasting

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-reduction-to-the-relative-affine-line/sk-prop-wgen-relative-line/
lem-zl-shriek-composition.md and its composition and Frobenius proof; subordinate normalized
open/proper coherence in part-six-operations/sec-six-functors-basics/sec-brown-construction/
sec-construction-of-rf/sk-thm-sf-comp-composition/sk-thm-sf-comp-composition.proof.md
(canonicity, associativity and base change). Stacks Tags 0F7B--0F7F give the finite torsion
analogue.
(blueprint: lem-zl-condensed-open-proper-pasting).

The existing ambient functors and compositors are reused. Inverses below are taken at individual
components, so the asserted laws need no invertibility on arbitrary unbounded objects. The main
statement specializes to condensed Qbar_l, separated finite-type schemes over the fixed geometric
field, and bounded constructible inputs. All displayed scheme maps are arbitrary scheme maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse component of the specified open-adjunction mate. The existing total inverse
agrees with the unique inverse whenever the component is invertible; no isomorphism on the full
unbounded category is assumed.
Source: blueprint composition proof, open exchange (a)
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def openExchangeComponent {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq a j' j b) (K : D Λ U) :
    (P Λ b).obj ((J Λ j).obj K) ⟶ (J Λ j').obj ((P Λ a).obj K) :=
  comparisonInverse ((openMap Λ sq).app K)

/-- Open restriction of direct image on the open support, followed by the inverse open unit.
The restriction factor is the recorded module-adjunction mate. For a Cartesian square, or a
commutative square with proper verticals, invertibility is asserted only at the stipulated inputs.
Source: blueprint composition proof, support restriction in (b); Stacks Tag 0F7B
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def supportRestrictionComponent {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] (sq : CommSq j p r i) (K : D Λ U) :
    (P Λ i).obj ((R Λ r).obj ((J Λ j).obj K)) ⟶ (R Λ p).obj K :=
  (derivedDirectImageOpenRestriction Λ sq).app ((J Λ j).obj K) ≫
    (R Λ p).map (comparisonInverse
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K))

/-- The open-adjunction transpose of inverse support restriction, at the given input. Taking the
inverse at the component avoids an assertion on all ambient objects. The formula is also total on
outer mixed pastes; the main statement gives its laws on bounded constructible inputs.
Source: blueprint composition proof, Gamma in (b); Stacks Tag 0F7B
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def properOpenComponent {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i) (K : D Λ U) :
    (J Λ i).obj ((R Λ p).obj K) ⟶ (R Λ r).obj ((J Λ j).obj K) :=
  (J Λ i).map (comparisonInverse (supportRestrictionComponent Λ sq K)) ≫
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).counit.app
      ((R Λ r).obj ((J Λ j).obj K))

/-- Precisely the comparison laws (a)--(c) on separated finite-type schemes over the geometric
field and bounded constructible inputs. The coefficient parameter here defines a predicate; the
existence theorem below asserts it only for the single condensed Qbar_l coefficient ring.
Source: blueprint composition and Frobenius compatibility proof; Stacks Tags 0F7B--0F7F
(blueprint: lem-zl-condensed-open-proper-pasting). -/
structure GeometricBoundedPasting (F : WeilConjectures.FiniteFieldDatum.{u}) : Prop where
  /-- Open adjunction units used in the support-restriction formula are invertible. -/
  open_unit_isIso : ∀ {U W : SepFinType F.k} (j : U.obj.left ⟶ W.obj.left) [IsOpenImmersion j]
    (K : D Λ U.obj.left), boundedConstructible (condensedRingObj Λ U.obj.left) K →
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K)
  /-- Clause (a): the specified mate is invertible at each bounded constructible input. -/
  open_isIso : ∀ {U' U W' W : SepFinType F.k} {a : U'.obj.left ⟶ U.obj.left}
    {j' : U'.obj.left ⟶ W'.obj.left}
    {j : U.obj.left ⟶ W.obj.left} {b : W'.obj.left ⟶ W.obj.left} [IsOpenImmersion j]
    [IsOpenImmersion j']
    (sq : IsPullback a j' j b) (K : D Λ U.obj.left),
    boundedConstructible (condensedRingObj Λ U.obj.left) K → IsIso ((openMap Λ sq.toCommSq).app K)
  /-- Naturality of the inverse open exchange on bounded constructible inputs. -/
  B_natural : ∀ {U' U W' W : SepFinType F.k} {a : U'.obj.left ⟶ U.obj.left}
    {j' : U'.obj.left ⟶ W'.obj.left}
    {j : U.obj.left ⟶ W.obj.left} {b : W'.obj.left ⟶ W.obj.left} [IsOpenImmersion j]
    [IsOpenImmersion j']
    (sq : IsPullback a j' j b) (K L : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K)
    (_hL : boundedConstructible (condensedRingObj Λ U.obj.left) L) (f : K ⟶ L),
    (P Λ b).map ((J Λ j).map f) ≫ openExchangeComponent Λ sq.toCommSq L =
      openExchangeComponent Λ sq.toCommSq K ≫ (J Λ j').map ((P Λ a).map f)
  /-- Identity vertical maps give the canonical identity exchange. -/
  B_id : ∀ {U W : SepFinType F.k} (j : U.obj.left ⟶ W.obj.left) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U.obj.left) j j (𝟙 W.obj.left)) (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    openExchangeComponent Λ sq.toCommSq K = (pId Λ W.obj.left).hom.app ((J Λ j).obj K) ≫
      (J Λ j).map ((pId Λ U.obj.left).inv.app K)
  /-- Identity opens give the canonical identity exchange. -/
  B_open_id : ∀ {X Y : SepFinType F.k} (f : X.obj.left ⟶ Y.obj.left)
    (sq : IsPullback f (𝟙 X.obj.left) (𝟙 Y.obj.left) f) (K : D Λ Y.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ Y.obj.left) K),
    openExchangeComponent Λ sq.toCommSq K = (P Λ f).map ((jId Λ Y.obj.left).hom.app K) ≫
      (jId Λ X.obj.left).inv.app ((P Λ f).obj K)
  /-- Cartesian pasting along successive arbitrary base maps. -/
  B_vertical : ∀ {U₀ U₁ U₂ W₀ W₁ W₂ : SepFinType F.k}
    {a₁ : U₁.obj.left ⟶ U₀.obj.left} {a₂ : U₂.obj.left ⟶ U₁.obj.left}
    {b₁ : W₁.obj.left ⟶ W₀.obj.left} {b₂ : W₂.obj.left ⟶ W₁.obj.left}
    {j₀ : U₀.obj.left ⟶ W₀.obj.left} {j₁ : U₁.obj.left ⟶ W₁.obj.left}
    {j₂ : U₂.obj.left ⟶ W₂.obj.left}
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (q₁ : IsPullback a₁ j₁ j₀ b₁) (q₂ : IsPullback a₂ j₂ j₁ b₂)
    (q : IsPullback (a₂ ≫ a₁) j₂ j₀ (b₂ ≫ b₁)) (K : D Λ U₀.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U₀.obj.left) K),
    openExchangeComponent Λ q.toCommSq K =
      (pComp Λ b₂ b₁).hom.app ((J Λ j₀).obj K) ≫
      (P Λ b₂).map (openExchangeComponent Λ q₁.toCommSq K) ≫
      openExchangeComponent Λ q₂.toCommSq ((P Λ a₁).obj K) ≫
      (J Λ j₂).map ((pComp Λ a₂ a₁).inv.app K)
  /-- Cartesian pasting along successive opens. -/
  B_horizontal : ∀ {U U' V V' W W' : SepFinType F.k}
    {a : U'.obj.left ⟶ U.obj.left} {b : V'.obj.left ⟶ V.obj.left} {c : W'.obj.left ⟶ W.obj.left}
    {j : U.obj.left ⟶ V.obj.left} {j' : U'.obj.left ⟶ V'.obj.left} {i : V.obj.left ⟶ W.obj.left}
    {i' : V'.obj.left ⟶ W'.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    (q₁ : IsPullback a j' j b) (q₂ : IsPullback b i' i c)
    (q : IsPullback a (j' ≫ i') (j ≫ i) c) (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    openExchangeComponent Λ q.toCommSq K =
      (P Λ c).map ((jComp Λ j i).inv.app K) ≫
      openExchangeComponent Λ q₂.toCommSq ((J Λ j).obj K) ≫
      (J Λ i').map (openExchangeComponent Λ q₁.toCommSq K) ≫
      (jComp Λ j' i').hom.app ((P Λ a).obj K)
  /-- Associativity of the specified open compositors. -/
  j_assoc : ∀ {X₀ X₁ X₂ X₃ : SepFinType F.k}
    (j : X₀.obj.left ⟶ X₁.obj.left) (i : X₁.obj.left ⟶ X₂.obj.left) (k : X₂.obj.left ⟶ X₃.obj.left)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k] (K : D Λ X₀.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ X₀.obj.left) K),
    (J Λ k).map ((jComp Λ j i).hom.app K) ≫
      (jComp Λ (j ≫ i) k).hom.app K ≫ (jCongr Λ (Category.assoc j i k)).hom.app K =
      (jComp Λ i k).hom.app ((J Λ j).obj K) ≫ (jComp Λ j (i ≫ k)).hom.app K
  /-- Both open-compositor unit equations. -/
  j_unit : ∀ {U W : SepFinType F.k} (j : U.obj.left ⟶ W.obj.left)
    [IsOpenImmersion j] (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    ((jComp Λ (𝟙 U.obj.left) j).hom.app K ≫ (jCongr Λ (Category.id_comp j)).hom.app K =
      (J Λ j).map ((jId Λ U.obj.left).hom.app K)) ∧
    ((jComp Λ j (𝟙 W.obj.left)).hom.app K ≫ (jCongr Λ (Category.comp_id j)).hom.app K =
      (jId Λ W.obj.left).hom.app ((J Λ j).obj K))
  /-- Lambda is invertible in precisely the two geometric situations of (b). -/
  restriction_isIso : ∀ {U W Y Z : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left}
    {i : Y.obj.left ⟶ Z.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    (sq : CommSq j p r i), IsAdmissibleSquare j p r i → ∀ (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
      IsIso (supportRestrictionComponent Λ sq K)
  /-- Vertical mixed pasting, with canonical direct-image compositors at both ends. -/
  gamma_vertical : ∀ {U W Y Z V T : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {i : Y.obj.left ⟶ Z.obj.left} {k : V.obj.left ⟶ T.obj.left}
    {p₁ : U.obj.left ⟶ Y.obj.left} {p₂ : Y.obj.left ⟶ V.obj.left} {r₁ : W.obj.left ⟶ Z.obj.left}
    {r₂ : Z.obj.left ⟶ T.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    (_h₁ : IsAdmissibleSquare j p₁ r₁ i) (_h₂ : IsAdmissibleSquare i p₂ r₂ k)
    (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ q K =
      (J Λ k).map ((rComp Λ p₁ p₂).inv.app K) ≫
      properOpenComponent Λ q₂ ((R Λ p₁).obj K) ≫
      (R Λ r₂).map (properOpenComponent Λ q₁ K) ≫
      (rComp Λ r₁ r₂).hom.app ((J Λ j).obj K)
  /-- Horizontal mixed pasting, with canonical open compositors at both ends. -/
  gamma_horizontal : ∀ {U W V Y Z T : SepFinType F.k}
    {j₁ : U.obj.left ⟶ W.obj.left} {j₂ : W.obj.left ⟶ V.obj.left} {i₁ : Y.obj.left ⟶ Z.obj.left}
    {i₂ : Z.obj.left ⟶ T.obj.left}
    {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left} {s : V.obj.left ⟶ T.obj.left}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact j₁] [QuasiCompact j₂] [QuasiCompact i₁] [QuasiCompact i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂))
    (_h₁ : IsAdmissibleSquare j₁ p r i₁) (_h₂ : IsAdmissibleSquare j₂ r s i₂)
    (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ q K =
      (jComp Λ i₁ i₂).inv.app ((R Λ p).obj K) ≫
      (J Λ i₂).map (properOpenComponent Λ q₁ K) ≫
      properOpenComponent Λ q₂ ((J Λ j₁).obj K) ≫
      (R Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  /-- Identity vertical morphisms give identity comparisons. -/
  gamma_vertical_id : ∀ {U W : SepFinType F.k} (j : U.obj.left ⟶ W.obj.left)
    [IsOpenImmersion j] [QuasiCompact j] (sq : CommSq j (𝟙 U.obj.left) (𝟙 W.obj.left) j)
    (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ sq K =
      (J Λ j).map ((rId Λ U.obj.left).hom.app K) ≫ (rId Λ W.obj.left).inv.app ((J Λ j).obj K)
  /-- Identity horizontal opens give identity comparisons. -/
  gamma_horizontal_id : ∀ {U Y : SepFinType F.k} (p : U.obj.left ⟶ Y.obj.left)
    (sq : CommSq (𝟙 U.obj.left) p p (𝟙 Y.obj.left)) (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    properOpenComponent Λ sq K =
      (jId Λ Y.obj.left).hom.app ((R Λ p).obj K) ≫ (R Λ p).map ((jId Λ U.obj.left).inv.app K)
  /-- Base-change cube (c), at bounded constructible inputs and without inverting Ex. -/
  cube : ∀ {U W Y Z U' W' Y' Z' : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left}
    {i : Y.obj.left ⟶ Z.obj.left}
    {j' : U'.obj.left ⟶ W'.obj.left} {p' : U'.obj.left ⟶ Y'.obj.left}
    {r' : W'.obj.left ⟶ Z'.obj.left} {i' : Y'.obj.left ⟶ Z'.obj.left}
    {aU : U'.obj.left ⟶ U.obj.left} {aW : W'.obj.left ⟶ W.obj.left} {aY : Y'.obj.left ⟶ Y.obj.left}
    {b : Z'.obj.left ⟶ Z.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact j'] [QuasiCompact i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (_hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U.obj.left)
    (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K),
    (P Λ b).map (properOpenComponent Λ q K) ≫
      (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K) ≫
      (R Λ r').map (openExchangeComponent Λ qj.toCommSq K) =
    openExchangeComponent Λ qi.toCommSq ((R Λ p).obj K) ≫
      (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
      properOpenComponent Λ q' ((P Λ aU).obj K)
  /-- Naturality of Gamma on the full bounded constructible subcategory. -/
  gamma_natural : ∀ {U W Y Z : SepFinType F.k}
    {j : U.obj.left ⟶ W.obj.left} {p : U.obj.left ⟶ Y.obj.left} {r : W.obj.left ⟶ Z.obj.left}
    {i : Y.obj.left ⟶ Z.obj.left}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    (sq : CommSq j p r i) (_hQ : IsAdmissibleSquare j p r i)
    (K L : D Λ U.obj.left) (_hK : boundedConstructible (condensedRingObj Λ U.obj.left) K)
    (_hL : boundedConstructible (condensedRingObj Λ U.obj.left) L) (f : K ⟶ L),
    (J Λ i).map ((R Λ p).map f) ≫ properOpenComponent Λ sq L =
      properOpenComponent Λ sq K ≫ (R Λ r).map ((J Λ j).map f)


/-- Normalized open exchange, mixed proper/open pasting and the base-change cube, with the
finite-field datum, the single condensed Qbar_l ring, and precisely bounded constructible inputs.
Source: latest blueprint, lem-zl-shriek-composition and the composition proof it invokes
(blueprint: lem-zl-condensed-open-proper-pasting).

Proof (the ten steps of the DAG node):
1. Transport internal modules to modules over the section-ring sheaf, retaining the specified
   pullback, direct image and open-extension adjunctions. Exact diagram descent preserves units,
   counits and composites. Pullback and open extension are exact. Specialize to these finite-type
   geometric schemes and condensed Qbar_l; use ambient adjunctions only for the asserted inputs.
2. Open base change identifies the unit--square--counit map openMap and makes its component
   invertible. The normalized open units are invertible as well. Its unique inverse is B.
3. The direct-image coherence comparison is conjugate to the canonical pullback compositor.
   Transpose the identity, pasting and three-open diagrams. The same restriction comparison and
   units occur on both sides; mate pasting and the triangle identities give all the B and J laws.
4. On a Cartesian open square, the natural Hom chain through J_i, P_r, B, J_j and P_p identifies
   restriction with the specified module-adjunction mate. Apply it to J_j K and cancel the open
   unit to obtain lambda. Its inverse has the open-adjunction transpose properOpenComponent.
5. For a proper commutative square, factor through V = W ×_Z Y. The induced open U → V is
   proper, hence closed. The clopen decomposition V = U ⊔ C identifies extension with zero
   insertion, also right adjoint to restriction. Cartesian restriction and direct-image
   composition give precisely the same lambda on J_j K, without proper base change.
6. On inverse image, compose normalized open exchange with projection to the U coordinate of
   V = U ⊔ C. Its proper-adjunction mate is the open transpose of inverse lambda: the open
   triangle identity cancels the unit and counit, and the clopen coordinates are (1,0).
7. For vertical and horizontal pastes, successive support projections preserve the intersection
   of the supports. They are identity on it and zero elsewhere. Restriction detects equality in
   the open-extension image, or the two clopen coordinates detect it in the proper case.
8. Take mates of these support equations. Mate pasting gives gamma_vertical and gamma_horizontal;
   the K-injective-normalized direct compositor agrees with the conjugate pullback compositor.
   The identity mate gives both identity equations. Evaluate at the stipulated K.
9. Pull back the support decomposition. Pullback preserves restriction and zero insertion; the
   two pullbacks of the support projection have the same coordinates (1,0). Open-exchange
   pasting yields the inverse-image cube. Open immersions and properness survive base change.
10. Apply the mate-cube theorem. The mates of the pullback square comparisons are exactly the
    recorded exchanges; the mates of the support maps are Gamma. This gives cube, without
    inverting proper exchange or Gamma. Arbitrary scheme maps allow the Frobenius case.
-/
theorem condensedGeometricBoundedOpenProperPasting (F : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ F.p) :
    GeometricBoundedPasting (Profinite.padicAlgClRingObj ℓ) F := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
