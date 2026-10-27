/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D9
-/
module

public import Sheaf.Paper.FiniteProductCompactification

/-! # Product compactification on a supplied Cartesian cone

Source: the independence-of-coordinates clause of the compactification reduction in
lem-sf-kunneth-coherence.proof.md, symmetry paragraph.
(blueprint: lem-pur-finite-forward-cartesian-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The usual compactification geometry, using the supplied representative of X times_B Z.
The other two Cartesian cones remain Mathlib's chosen pullbacks. No derived map is chosen.
Source: the Cartesian diagram in the compactification reduction
(blueprint: lem-pur-finite-forward-cartesian-coordinates). -/
abbrev finiteForwardCartesianGeometry {B X Z P : Scheme.{u}}
    {f : X ⟶ B} {g : Z ⟶ B} {p : P ⟶ X} {q : P ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (sq : IsPullback p q f g) :
    FiniteProductGeometry f g where
  cf := cf
  cg := cg
  P := P
  W := pullback f cg.g
  T := pullback cf.g cg.g
  p := p
  q := q
  s := pullback.fst f cg.g
  v := pullback.snd f cg.g
  r := pullback.fst cf.g cg.g
  t := pullback.snd cf.g cg.g
  sqP := sq
  sqW := IsPullback.of_hasPullback f cg.g
  sqT := IsPullback.of_hasPullback cf.g cg.g

/-- Transport the given product-compactification equality to any Cartesian cone.
This asserts no symmetry: it only changes the representative of X times_B Z in the
already supplied comparison theorem.
Source: the compactification reduction of lem-sf-kunneth-coherence.proof.md,
symmetry paragraph, and the independence-of-identifications clause of
lem-pur-finite-product-compactification.
(blueprint: lem-pur-finite-forward-cartesian-coordinates).

Proof: let e:P≅pullback f g be the unique isomorphism of Cartesian cones.
Its two projection equations identify the pulled-back input objects using the canonical
inverse-image compositors. Open base change identifies the two product open immersions,
and the unit-normalized open compositor identifies their extensions by zero.
Naturality of the counit-defined projection maps and horizontal mate pasting for exchange
identify each factor of the specified forward composite. The canonical compactification
comparisons are natural for all ambient morphisms on the origin subcategory and satisfy
the cocycle law, so the final compositor and target comparison are also transported.
Do the same for the ordinary route: naturality of the ordinary direct-image compositor
and the open units identify its open tensor map. Apply the supplied equality hc in the
chosen cone, conjugate by these canonical endpoint isomorphisms, and cancel them.
For the chosen input and output compactifications, the extra self-comparisons are
identities: precompose with the etale-origin equivalence, use etale reflexivity and cancel
the site comparisons. Expand only the definition of the chosen forward map and reassociate
to identify it with finiteForwardProduct. The six-field domain is assembled from d and
hop. No projection or exchange transformation is inverted; no symmetry assertion is used. -/
theorem finiteForwardCartesianCoordinates
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (CommRingCat.of C.field.k))]
    [X.Over (Spec (CommRingCat.of C.field.k))]
    [Z.Over (Spec (CommRingCat.of C.field.k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (CommRingCat.of C.field.k))]
    [g.IsOver (Spec (CommRingCat.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N)
    (hc : FinitePurityProductCompactification C f g M N wM wN)
    {P : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Z}
    (sq : IsPullback p q f g) :
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (CommRingCat.of C.field.k))
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let G := finiteForwardCartesianGeometry cf cg sq
  letI : HasCompactification q := finiteProductGeometry_q_hasCompactification G
  letI : HasCompactification (q ≫ g) := finiteProductGeometry_h_hasCompactification G
  letI : QuasiCompact q := finiteProductGeometry_q_quasiCompact G
  ∀ (d : FiniteForwardProductDomain (ModuleCat.{u + 1} C.Coefficient) sq M.obj N.obj)
    (_hop : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} C.Coefficient) B
      (((derivedTensor (ModuleCat.{u + 1} C.Coefficient) B).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} C.Coefficient) g).obj N.obj)).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} C.Coefficient) f).obj M.obj))),
    finiteForwardProduct C.Coefficient sq M.obj N.obj d.external ≫
      (finiteForwardCompactificationComparison C.Coefficient
        (HasCompactification.compactification (q ≫ g))
        (finiteProductCompactification G)).hom.app ⟨_, d.external⟩ =
      finiteProductOrdinaryInCoordinates G C.Coefficient cf cg M.obj N.obj
        ⟨wM.complex.obj, wM.complex.property, ⟨wM.iso⟩⟩
        ⟨wN.complex.obj, wN.complex.property, ⟨wN.iso⟩⟩ := by sorry

end AlgebraicGeometry.ProEtale
