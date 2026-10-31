/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.SemilinearExchangeReindexing
public import WeilConjectures.AlgebraicGeometry.FiniteFreeSystemRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingComposition

/-! # Integral scalar extension of isomorphism compact-support exchange

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, coefficient transport assembly
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).

The comparisons below are the proper adjunction mate followed by the inverse
of the open-unit transpose. Scalar comparison is the published tensor mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local instance 3000] AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
  AlgebraicGeometry.Scheme.reductionRingModulesHasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.IntegralScalarExchange

/-- Coherence of the coefficient identification, retaining the canonical compositor.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def Coherent (R : Coefficients.{u}) : Prop :=
  ∀ {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W),
    R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)

/-- The inverse-image square is the canonical composition comparison around the square.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def square (R : Coefficients.{u}) (hc : Coherent R)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (g : S ⟶ T) (w : k ≫ p = r ≫ g) :
    pull R g ⋙ pull R r ≅ pull R p ⋙ pull R k :=
  (geometricPullComposition R r g (hc r g)).symm ≪≫
    eqToIso (congrArg (pull R) w.symm) ≪≫
      geometricPullComposition R k p (hc k p)

/-- The open inverse exchange is the transpose of inverse image of the open unit.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def openInverse (R : Coefficients.{u}) (hc : Coherent R)
    {U' U T' T : Scheme.{u}} (x : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : x ≫ j = j' ≫ g) :
    pull R x ⋙ (openExtension R j').mapDerivedCategory ⟶
      (openExtension R j).mapDerivedCategory ⋙ pull R g :=
  ((mateEquiv (openDerivedAdjunction R j) (openDerivedAdjunction R j')).symm
    (TwoSquare.mk _ _ _ _ (square R hc x j' j g w).inv)).natTrans

/-- The unit-normalized open exchange is invertible for the Cartesian open square.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: restrict the transpose to the open, where both units are identity. Off the
open both extensions vanish. The Cartesian identification therefore identifies
its inverse sectionwise; exact localization preserves the two inverse identities. -/
theorem openInverse_isIso (R : Coefficients.{u}) (hc : Coherent R)
    {U' U T' T : Scheme.{u}} (x : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : x ≫ j = j' ≫ g) (_sq : IsPullback x j' j g) :
    IsIso (openInverse R hc x j' j g w) := by
  sorry

/-- The specified compact-support exchange: proper mate, then open comparison.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def exchange (R : Coefficients.{u}) (hc : Coherent R)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b) :
    image R c ⋙ pull R g ⟶ pull R x ⋙ image R c' :=
  Functor.whiskerLeft (openExtension R c.i).mapDerivedCategory
      (mateEquiv
        (proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g))
        (proEtaleRingDerivedAdjunction c'.g (R.ring Y') (R.ring c'.Z) (R.pull c'.g))
        (TwoSquare.mk _ _ _ _ (square R hc b c'.g c.g g sp.w).hom)).natTrans ≫
    Functor.whiskerRight
      (@asIso _ _ _ _ (openInverse R hc x c'.i c.i b sj.w)
        (openInverse_isIso R hc x c'.i c.i b sj.w
          (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd))).inv
      (push R c'.g)

variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

/-- The left path in the integral scalar-exchange rectangle, using the actual maps.
Source: displayed equation of the node
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def scalarLeft (R S : Coefficients.{u}) (hcR : Coherent R) (_hcS : Coherent S)
    (a : Change R S) {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (pbcModules X (R.ring X))) :=
  (pbcDerivedExtend (a.map Y')).map
      ((exchange R hcR c c' x g b sp sj).app M) ≫
    (comparison a c').app ((pull R x).obj M) ≫
    (image S c').map ((scalarPull a x).hom.app M)

/-- The right path in the same integral rectangle.
Source: displayed equation of the node
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def scalarRight (R S : Coefficients.{u}) (_hcR : Coherent R) (hcS : Coherent S)
    (a : Change R S) {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (pbcModules X (R.ring X))) :=
  (scalarPull a g).hom.app ((image R c).obj M) ≫
    (pull S g).map ((comparison a c).app M) ≫
    (exchange S hcS c c' x g b sp sj).app
      ((pbcDerivedExtend (a.map X)).obj M)

attribute [local instance 4000] proEtaleRingModules_hasDerivedCategory in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
/-- The left path in the integral scalar-exchange rectangle, using the actual maps.
Source: displayed equation of the node
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def left {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y')).obj
        ((pull (completed l E) g).obj ((image (completed l E) c).obj M)) ⟶
      (image (completed l F) c').obj ((pull (completed l F) x).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) :=
  (pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
      ((exchange (completed l E) (completedPull_comp l E) c c' x g b sp sj).app M) ≫
    (comparison (completedChange l E F i) c').app ((pull (completed l E) x).obj M) ≫
    (image (completed l F) c').map ((scalarPull (completedChange l E F i) x).hom.app M)

attribute [local instance 4000] proEtaleRingModules_hasDerivedCategory in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
/-- The composite transformation whose components give the right integral path.
The two associators have identity components, so these are exactly the three
specified right-path maps, in their original order.
Source: displayed equation and naturality clause, proof Step 6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def rightTransformation {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b) :
    image (completed l E) c ⋙ pull (completed l E) g ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y') ⟶
      pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
        pull (completed l F) x ⋙ image (completed l F) c' :=
  let a : Change (completed l E) (completed l F) :=
    { map := completedCoefficientMap l E F i
      square := completedChange_square l E F i }
  let I := image (completed l E) c
  let G := pull (completed l E) g
  let P := pbcDerivedExtend (completedCoefficientMap l E F i Y')
  let A := pbcDerivedExtend (completedCoefficientMap l E F i Y)
  let H := pull (completed l F) g
  let B := pbcDerivedExtend (completedCoefficientMap l E F i X)
  let J := image (completed l F) c
  let K := pull (completed l F) x
  let L := image (completed l F) c'
  let α : I ⋙ G ⋙ P ⟶ B ⋙ K ⋙ L :=
    Functor.whiskerLeft I (scalarPull a g).hom ≫
      (Functor.associator I A H).inv ≫
      Functor.whiskerRight (comparison a c) H ≫
      (Functor.associator B J H).hom ≫
      Functor.whiskerLeft B
        (exchange (completed l F) (completedPull_comp l F) c c' x g b sp sj)
  α

attribute [local instance 4000] proEtaleRingModules_hasDerivedCategory in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
/-- The right path in the same integral rectangle.
Source: displayed equation of the node
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def right {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y')).obj
        ((pull (completed l E) g).obj ((image (completed l E) c).obj M)) ⟶
      (image (completed l F) c').obj ((pull (completed l F) x).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) :=
  (rightTransformation l E F i c c' x g b sp sj).app M

/-- The actual finite constant coefficients have the canonical inverse-image compositor.
Source: constant-coefficient convention, proof Steps 1--2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: both maps are the identity on generating constant sections. Constant
sheafification and the inverse-image compositor preserve that identity. -/
theorem finiteCoherent (n : ℕ) (hn : 1 ≤ n) : Coherent (finite l E n hn) := by
  intro U V W h k
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  apply Iso.ext
  exact proEtaleCoefficientInverseImageMap_comp h k (Padic.coefficientExtensionRing l E n)

/-- The specified ramified finite-level rectangle, on actual reductions of M.
This predicate fixes each proper tensor mate, open identification and balanced
association, without choosing a map by its endpoints.
Source: simultaneous finite-system clause, proof Steps 1--4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def FiniteLeft (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  let hn := Nat.le_add_left 1 n
  let R := finite l E (n + 1) hn
  let S := finite l F (h * (n + 1)) (Nat.mul_pos hp hn)
  let a := finiteChange l E F i h hr hp (n + 1) hn
  let N := (pbcDerivedExtend (projection l E (n + 1) hn X)).obj M
  scalarLeft R S (finiteCoherent l E (n + 1) hn)
      (finiteCoherent l F (h * (n + 1)) (Nat.mul_pos hp hn)) a c c' x g b sp sj N

/-- The specified ramified finite-level rectangle, on actual reductions of M.
This predicate fixes each proper tensor mate, open identification and balanced
association, without choosing a map by its endpoints.
Source: simultaneous finite-system clause, proof Steps 1--4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def FiniteRight (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  let hn := Nat.le_add_left 1 n
  let R := finite l E (n + 1) hn
  let S := finite l F (h * (n + 1)) (Nat.mul_pos hp hn)
  let a := finiteChange l E F i h hr hp (n + 1) hn
  let N := (pbcDerivedExtend (projection l E (n + 1) hn X)).obj M
scalarRight R S (finiteCoherent l E (n + 1) hn)
      (finiteCoherent l F (h * (n + 1)) (Nat.mul_pos hp hn)) a c c' x g b sp sj N

/-- The source projection uses the scalar square, balanced pullback and the
proper/open reduction comparison, in their specified order.
Source: total-limit clause, proof Step 5
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def sourceProjection (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (_sp : ChosenCartesianSquare b c'.g c.g g)
    (_sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  let hn := Nat.le_add_left 1 n
  let a := completedChange l E F i
  let d := finiteChange l E F i h hr hp (n + 1) hn
  let r := reduction l E (n + 1) hn
  let t := reduction l F (h * (n + 1)) (Nat.mul_pos hp hn)
  let N := (image (completed l E) c).obj M
  (pbcDerivedScalarAdjunction (t.map Y')).unit.app
      ((pbcDerivedExtend (a.map Y')).obj ((pull (completed l E) g).obj N)) ≫
    (pbcDerivedRestrict (t.map Y')).map
      ((tensorSquare (a.map Y') (d.map Y') (r.map Y') (t.map Y')
          (ramified_reduction_square l E F i h hr hp (n + 1) hn Y')).hom.app
            ((pull (completed l E) g).obj N) ≫
        (pbcDerivedExtend (d.map Y')).map
          ((scalarPull r g).hom.app N ≫
            (pull (finite l E (n + 1) hn) g).map ((comparison r c).app M)))

/-- The target projection uses the proper/open reduction map, inverse pullback
balancing, and the same coefficient square as the source projection.
Source: total-limit clause, proof Step 5
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def targetProjection (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (_sp : ChosenCartesianSquare b c'.g c.g g)
    (_sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  let hn := Nat.le_add_left 1 n
  let a := completedChange l E F i
  let d := finiteChange l E F i h hr hp (n + 1) hn
  let r := reduction l E (n + 1) hn
  let t := reduction l F (h * (n + 1)) (Nat.mul_pos hp hn)
  let N := (pbcDerivedExtend (a.map X)).obj M
  (pbcDerivedScalarAdjunction (t.map Y')).unit.app
      ((image (completed l F) c').obj ((pull (completed l F) x).obj N)) ≫
    (pbcDerivedRestrict (t.map Y')).map
      ((comparison t c').app ((pull (completed l F) x).obj N) ≫
        (image (finite l F (h * (n + 1)) (Nat.mul_pos hp hn)) c').map
          ((scalarPull t x).hom.app N ≫
            (pull (finite l F (h * (n + 1)) (Nat.mul_pos hp hn)) x).map
              ((tensorSquare (a.map X) (d.map X) (r.map X) (t.map X)
                (ramified_reduction_square l E F i h hr hp (n + 1) hn X)).hom.app M)))

/-- The simultaneous strict lift and its total-limit normalization. The two epsilon
families are fixed by the independently constructed source and target projections.
Their finite maps are the displayed proper/open composites. The final equations use
the actual selection/block Roos map, retaining both cone coordinates at ramified indices.
Source: total-limit and quotient-transition clauses, proof Step 5
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def StrictLimitEquation (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  ∃ (P Q : CochainComplex (scalarReductionSource l F Y') ℤ) (v : P ⟶ Q)
    (a₀ : (pbcDerivedExtend (completedCoefficientMap l E F i Y')).obj
        ((pull (completed l E) g).obj ((image (completed l E) c).obj M)) ≅
      DerivedCategory.Q.obj P)
    (a₁ : (image (completed l F) c').obj
        ((pull (completed l F) x).obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≅
      DerivedCategory.Q.obj Q),
    proEtaleFlatRepresentatives Y' ((completed l F).ring Y') P ∧
    proEtaleFlatRepresentatives Y' ((completed l F).ring Y') Q ∧
    IsIso (DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app P)) ∧
    IsIso (DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app Q)) ∧
    (∃ (ε₀ : ∀ n : ℕ,
        DerivedCategory.Q.obj ((identityReductionTower l F P).obj
          (Opposite.op (h * (n + 1) - 1))) ≅
          (pbcDerivedRestrict (projection l F (h * (n + 1))
            (Nat.mul_pos hp (Nat.le_add_left 1 n)) Y')).obj
              (let hn := Nat.le_add_left 1 n;
                (pbcDerivedExtend ((finiteChange l E F i h hr hp (n + 1) hn).map Y')).obj
                  ((pull (finite l E (n + 1) hn) g).obj
                    ((image (finite l E (n + 1) hn) c).obj
                      ((pbcDerivedExtend (projection l E (n + 1) hn X)).obj M)))))
      (ε₁ : ∀ n : ℕ,
        DerivedCategory.Q.obj ((identityReductionTower l F Q).obj
          (Opposite.op (h * (n + 1) - 1))) ≅
          (pbcDerivedRestrict (projection l F (h * (n + 1))
            (Nat.mul_pos hp (Nat.le_add_left 1 n)) Y')).obj
              (let hn := Nat.le_add_left 1 n;
                (image (finite l F (h * (n + 1)) (Nat.mul_pos hp hn)) c').obj
                  ((pull (finite l F (h * (n + 1)) (Nat.mul_pos hp hn)) x).obj
                    ((pbcDerivedExtend ((finiteChange l E F i h hr hp (n + 1) hn).map X)).obj
                      ((pbcDerivedExtend (projection l E (n + 1) hn X)).obj M))))),
      (∀ n : ℕ,
        sourceProjection l E F i h hr hp c c' x g b sp sj M n =
          a₀.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app P) ≫
            DerivedCategory.Q.map (strictLevelProjection (identityReductionTower l F P)
              (h * (n + 1) - 1)) ≫ (ε₀ n).hom) ∧
      (∀ n : ℕ,
        targetProjection l E F i h hr hp c c' x g b sp sj M n =
          a₁.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app Q) ≫
            DerivedCategory.Q.map (strictLevelProjection (identityReductionTower l F Q)
              (h * (n + 1) - 1)) ≫ (ε₁ n).hom) ∧
      (∀ n : ℕ,
        DerivedCategory.Q.map ((identityReductionMap l F v).app
            (Opposite.op (h * (n + 1) - 1))) ≫ (ε₁ n).hom =
          (ε₀ n).hom ≫
            (pbcDerivedRestrict (projection l F (h * (n + 1))
              (Nat.mul_pos hp (Nat.le_add_left 1 n)) Y')).map
                (FiniteLeft l E F i h hr hp c c' x g b sp sj M n)) ∧
      (∀ n : ℕ,
        DerivedCategory.Q.map ((identityReductionMap l F v).app
            (Opposite.op (h * (n + 1) - 1))) ≫ (ε₁ n).hom =
          (ε₀ n).hom ≫
            (pbcDerivedRestrict (projection l F (h * (n + 1))
              (Nat.mul_pos hp (Nat.le_add_left 1 n)) Y')).map
                (FiniteRight l E F i h hr hp c c' x g b sp sj M n))) ∧
    (∃ (ρ₀ : integralOperationsRoos (identityReductionTower l F P) ⟶
          integralOperationsRoos (retainedTower h (identityReductionTower l F P)))
      (ρ₁ : integralOperationsRoos (identityReductionTower l F Q) ⟶
          integralOperationsRoos (retainedTower h (identityReductionTower l F Q))),
      IsCofinalRoosMap h (identityReductionTower l F P) ρ₀ ∧
      IsCofinalRoosMap h (identityReductionTower l F Q) ρ₁ ∧ QuasiIso ρ₀ ∧ QuasiIso ρ₁ ∧
      (∀ z ∈ ({left l E F i c c' x g b sp sj M,
          right l E F i c c' x g b sp sj M} : Set _),
        z ≫ a₁.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app Q) ≫
            DerivedCategory.Q.map ρ₁ =
          a₀.hom ≫ DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app P) ≫
            DerivedCategory.Q.map ρ₀ ≫ DerivedCategory.Q.map
              (integralOperationsRoosMap
                (Functor.whiskerLeft (CategoryTheory.StrictTowerArithmetic.index h)
                  (identityReductionMap l F v)))))

attribute [local irreducible] left right scalarLeft scalarRight FiniteLeft FiniteRight
  sourceProjection targetProjection StrictLimitEquation exchange

/-- The simultaneous finite-level part of the integral scalar-exchange rectangle.
Source: constituent coefficient-transport assembly, proof Steps 1--4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
This is the strict-system equality before the normalized total-limit argument. -/
theorem finiteScalarIsomorphismExchange
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    [IsIso x] [IsIso g] [IsIso b]
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M)
    (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h) :
    ∀ n : ℕ, FiniteLeft l E F i h hr hp c c' x g b sp sj M n =
      FiniteRight l E F i h hr hp c c' x g b sp sj M n := by
  sorry

/-- The normalized total-limit part of the integral scalar-exchange rectangle.
Source: constituent coefficient-transport assembly, proof Steps 5--6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
This is the Roos normalization clause after the strict finite-system equation. -/
theorem strictLimitEquation_of_integralScalarIsomorphismExchange
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    [IsIso x] [IsIso g] [IsIso b]
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M)
    (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h) :
    StrictLimitEquation l E F i h hr hp c c' x g b sp sj M := by
  sorry

-- The DVR argument is the one used in RamifiedPullback.ramification_exists.
private theorem positive_ramification : ∃ h : ℕ, 1 ≤ h ∧ Ramification l E F i h := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l F
  let t := Padic.coefficientExtensionUniformizer l E
  let v := Padic.coefficientExtensionUniformizer l F
  let f := integralScalarIntegerInclusion l E F i
  have hE := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hL := (Padic.extension_integers_dvr l F (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := ℚ_[l]) (L := F))).choose_spec.choose_spec
  have : IsLocalRing R := hE.2.2.2.1
  have : IsLocalRing S := hL.2.2.2.1
  have : IsDiscreteValuationRing R := hE.2.2.2.2.2.2.2.1
  have : IsDiscreteValuationRing S := hL.2.2.2.2.2.2.2.1
  have ht : Ideal.span ({t} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hv : Ideal.span ({v} : Set S) = Padic.coefficientExtensionMaximalIdeal l F :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hti : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr
      ((hE.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal R)).trans ht.symm)
  have hvi : Irreducible v :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer v).mpr
      ((hL.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal S)).trans hv.symm)
  have hft : f t ≠ 0 := by
    intro hz
    have hz' : i (t : E) = 0 := congrArg Subtype.val hz
    exact hti.ne_zero (Subtype.ext (i.injective (by simpa using hz')))
  have hnu : ¬ IsUnit (f t) := by
    intro h
    have ha := (hL.2.2.1 (f t)).mp h
    change Padic.coefficientExtensionAbsoluteValue l F (i (t : E)) = 1 at ha
    rw [integralScalar_absoluteValue l E F i] at ha
    have hb := (hE.2.1 t).mp
      (show t ∈ Padic.coefficientExtensionMaximalIdeal l E from
        ht ▸ Ideal.mem_span_singleton_self t)
    exact (ne_of_lt hb) ha
  obtain ⟨e, w, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hft hvi
  have he : 1 ≤ e := by
    by_contra hn
    have hz : e = 0 := by omega
    apply hnu
    rw [hz, pow_zero, mul_one] at heq
    exact heq.symm ▸ w.isUnit
  have hideal : Ideal.span ({f t} : Set S) = Ideal.span {v ^ e} := by
    rw [heq]
    exact Ideal.span_singleton_mul_left_unit w.isUnit _
  refine ⟨e, he, ?_⟩
  change Ideal.map f (Padic.coefficientExtensionIdeal l E 1) =
    Padic.coefficientExtensionIdeal l F e
  simpa only [Padic.coefficientExtensionIdeal, pow_one, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_pow] using hideal

/-- Finite integral extension preserves the specified isomorphism exchange.
Source: constituent coefficient-transport assembly, Steps 1--6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: choose one integral basis and reduce it at all levels. Restriction preserves
the proper unit-square-counit word and the open-unit transpose. The adjunct of each
ordered scalar comparison is compact support of the scalar unit; balanced pullback
has adjunct pullback of that unit. Hence the two rectangle paths have adjuncts
P' G'(eta) xi and xi G P(eta), equal by naturality of xi. The scalar adjunction
bijection gives equality on entire strict systems. Apply total derived limit;
normalized cofinal reduction and balanced association identify its paths with the
integral paths. Canonical refinement comparisons commute with every factor, so
conjugation gives independence of compactification. No k-linearity is used. -/
theorem integralScalarIsomorphismExchange_integral
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    [IsIso x] [IsIso g] [IsIso b]
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    left l E F i c c' x g b sp sj M = right l E F i c c' x g b sp sj M := by
  obtain ⟨h, hp, hr⟩ := positive_ramification l E F i
  have hlim := strictLimitEquation_of_integralScalarIsomorphismExchange
    l E F i D _hl c c' x g b sp sj M _hM h hr hp
  unfold StrictLimitEquation at hlim
  rcases hlim with ⟨P, Q, v, a₀, a₁, _, _, _, hunit, _,
    ρ₀, ρ₁, _, _, _, hcofinal, hz⟩
  let := hunit
  let := hcofinal
  have heq := (hz _ (Set.mem_insert _ _)).trans
    (hz _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm
  apply (cancel_mono (a₁.hom ≫
    DerivedCategory.Q.map ((completedScalarIdentityUnit l F Y').app Q) ≫
    DerivedCategory.Q.map ρ₁)).1
  simpa only [Category.assoc] using heq

/-- The integral equation together with its simultaneous finite-system and
normalized total-limit clauses, with the actual ramification exponent.
Source: constituent coefficient-transport assembly, proof Steps 1--6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: choose a single integral basis and reduce it at every positive exponent.
The scalar unit inserts one; restriction preserves all proper and open adjunction
words. The two scalar adjuncts are equal by naturality of exchange at this unit,
giving equality before taking total limit. K-flat presentations of its endpoints
and chain-map presentation of this common derived morphism give P,Q,v. Quotient
adjunction determines epsilon from sourceProjection and targetProjection. The
proper tensor, open identification and balanced pullback factors give the stated
finite maps. Both coordinates of the selection/block map commute with this
strict map. Normalized completion units and cofinality identify the resulting
Roos map with both integral paths. These constructions use underlying schemes. -/
theorem integralScalarIsomorphismExchange
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    [IsIso x] [IsIso g] [IsIso b]
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M)
    (h : ℕ) (hr : Ramification l E F i h) (hp : 1 ≤ h) :
    left l E F i c c' x g b sp sj M = right l E F i c c' x g b sp sj M ∧
      (∀ n : ℕ, FiniteLeft l E F i h hr hp c c' x g b sp sj M n =
        FiniteRight l E F i h hr hp c c' x g b sp sj M n) ∧
      StrictLimitEquation l E F i h hr hp c c' x g b sp sj M := by
  refine ⟨integralScalarIsomorphismExchange_integral l E F i D _hl c c' x g b sp sj M _hM, ?_, ?_⟩
  · exact finiteScalarIsomorphismExchange l E F i D _hl c c' x g b sp sj M _hM h hr hp
  · exact strictLimitEquation_of_integralScalarIsomorphismExchange l E F i D _hl c c' x g b sp sj M
      _hM h hr hp

attribute [local irreducible] completedAdicDerivedChange completedAdicChangeData
  reductionDerivedChange pbcDerivedScalarAdjunction completedCoefficientMap
  Functor.mapDerivedCategory

private theorem three_squares
    {C : Type*} [Category C] {A B C₀ D A' B' C' D' : C}
    (p : A ⟶ B) (q : B ⟶ C₀) (r : C₀ ⟶ D)
    (p' : A' ⟶ B') (q' : B' ⟶ C') (r' : C' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : C₀ ⟶ C') (d : D ⟶ D')
    (h₁ : a ≫ p' = p ≫ b) (h₂ : b ≫ q' = q ≫ c) (h₃ : c ≫ r' = r ≫ d) :
    a ≫ p' ≫ q' ≫ r' = (p ≫ q ≫ r) ≫ d := by
  rw [← Category.assoc a, h₁, Category.assoc, ← Category.assoc b,
    h₂, Category.assoc, h₃, Category.assoc, Category.assoc]

attribute [local instance 4000] proEtaleRingModules_hasDerivedCategory in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
/-- Naturality of the two displayed integral paths, including all inputs and morphisms.
Source: naturality clause, proof Step 6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: each factor is a natural transformation: the proper mate, the inverse
open transpose, the scalar mate, and balanced pullback association. Whiskering
and composing their naturality squares gives each displayed equation. -/
theorem rectangle_naturality
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    {M N : DerivedCategory (scalarReductionSource l E X)} (v : M ⟶ N) :
    (∀ z ∈ ({left l E F i c c' x g b sp sj,
        right l E F i c c' x g b sp sj} : Set _),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
          ((pull (completed l E) g).map ((image (completed l E) c).map v)) ≫ z N =
        z M ≫ (image (completed l F) c').map
          ((pull (completed l F) x).map
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).map v))) := by
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · delta left
    have h₁ := congrArg (pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
      ((exchange (completed l E) (completedPull_comp l E) c c' x g b sp sj).naturality v)
    have h₂ := (comparison (completedChange l E F i) c').naturality
      ((pull (completed l E) x).map v)
    have h₃ := congrArg (image (completed l F) c').map
      ((scalarPull (completedChange l E F i) x).hom.naturality v)
    simp only [Functor.comp_map, Functor.map_comp] at h₁ h₂ h₃
    dsimp only [completedChange] at h₁ h₂ h₃ ⊢
    exact three_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
  · delta right
    simpa -implicitDefEqProofs only [Functor.comp_map] using
      (rightTransformation l E F i c c' x g b sp sj).naturality v

/-- The displayed source domain is preserved by finite scalar extension and by
inverse image along an underlying-scheme isomorphism, with uniform reduction bounds.
Source: domains of the rectangle, proof Steps 1 and 5
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: a finite integral basis makes scalar extension a finite exact tensor after
restriction and keeps a common cohomological and Tor interval for every quotient.
The quotient augmentation proves derived completeness. An isomorphism identifies
the small sites, their strata, tensor products and all quotient transitions, so
pullback preserves these same bounds and the reconstruction unit. -/
theorem scalarPull_finiteTor {X' X : Scheme.{u}} (x : X' ⟶ X) [IsIso x]
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X' ((pull (completed l F) x).obj
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) := by
  sorry

/-- Canonical refinement transports both paths to the paths for the refined
compactifications. The prime base structures may be transported along x and g;
no linearity of x or g is a premise. The target finite-Tor
domain is supplied by scalarPull_finiteTor, rather than being a further premise.
Source: independence clause, proof Step 6
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: insert the canonical proper-open refinement maps on the four support
terms. The scalar/refinement square and the proper/open exchange/refinement
square commute, since their open transposes are the same unit and their proper
factors the same pasted counit. Cancel the intermediate inverse comparisons.
This yields each equation, and the canonical refinement cocycle handles common
refinements and independence of their choices. -/
theorem rectangle_refinement
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
    [IsSeparated (X' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
    [IsSeparated (Y' ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
    [f'.IsOver (Spec (.of D.k))] [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (c' d' : Compactification f')
    (r : c.Refinement d) (r' : c'.Refinement d')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z) (a : d'.Z ⟶ d.Z)
    [IsIso x] [IsIso g] [IsIso b] [IsIso a]
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (tp : ChosenCartesianSquare a d'.g d.g g)
    (tj : OpenImmersionSquare x d'.i d.i a)
    (_w : b ≫ r.hom = r'.hom ≫ a)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ((pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
        ((pull (completed l E) g).map
          (refinementComparison l E D hl f r M hM).hom) ≫
      left l E F i d d' x g a tp tj M =
      left l E F i c c' x g b sp sj M ≫
        (refinementComparison l F D hl f' r'
          ((pull (completed l F) x).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
          (scalarPull_finiteTor l E F i x M hM)).hom) ∧
    ((pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
        ((pull (completed l E) g).map
          (refinementComparison l E D hl f r M hM).hom) ≫
      right l E F i d d' x g a tp tj M =
      right l E F i c c' x g b sp sj M ≫
        (refinementComparison l F D hl f' r'
          ((pull (completed l F) x).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
          (scalarPull_finiteTor l E F i x M hM)).hom) := by
  sorry

end WeilConjectures.IntegralScalarExchange

namespace WeilConjectures.IntegralScalarExchange.Systems
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.FiniteFreeSystemRestriction

variable (l : ℕ) [Fact l.Prime]
  (E F : Type (u + 1)) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Strict scalar extension uses the normalized universal K-flat scalar model.
Source: constituent coefficient-transport assembly, Step 1
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
abbrev Scalar (X : Scheme.{u}) :=
  WeilConjectures.SemilinearSections.ScalarData.{u + 1, u, u + 1}
    (systemInclusion l E F i X)

/-- The actual proper mate followed by the unit-normalized open exchange,
on the ordinary derived category of entire semilinear coefficient systems.
Source: constituent coefficient-transport assembly, Step 2
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def exchange (C : ℕ → CommRingCat.{u + 1}) (t : ∀ n, C (n + 1) ⟶ C n)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b) :
    compact C t c.i c.g ⋙ P C t g ⟶ P C t x ⋙ compact C t c'.i c'.g :=
  Functor.whiskerLeft (J C t c.i)
      (mateEquiv (adj C t c.g) (adj C t c'.g)
        (TwoSquare.mk _ _ _ _ (squareP C t b c'.g c.g g sp.w).hom)).natTrans ≫
    Functor.whiskerRight
      (beta C t x c'.i c.i b sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom
      (R C t c'.g)

/-- The scalar compact-support arrow is the mate of the normalized restriction square.
Its proper factor precedes its open factor, as in the specified coefficient comparison.
Source: constituent coefficient-transport assembly, Step 3
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def comparison (D : FiniteFieldDatum.{u}) (G : Geometry l E F i D)
    (S : ∀ W : Spaces D, Scalar l E F i W.val.left)
    (X Z Y : Spaces D) (j : X.val.left ⟶ Z.val.left)
    (p : Z.val.left ⟶ Y.val.left) [IsOpenImmersion j] :
    compact (A l E) (aTransition l E) j p ⋙ (S Y).T ⟶
      (S X).T ⋙ compact (B l E F i) (bTransition l E F i) j p :=
  Functor.whiskerLeft (J (A l E) (aTransition l E) j)
      (((mateEquiv (S Z).adjunction (S Y).adjunction).symm
        (TwoSquare.mk _ _ _ _ (G.pushIso l E F i Z Y p).inv)).natTrans) ≫
    Functor.whiskerRight
      (((mateEquiv (S X).adjunction (S Z).adjunction).symm
        (TwoSquare.mk _ _ _ _ (G.openIso l E F i X Z j).inv)).natTrans)
      (R (B l E F i) (bTransition l E F i) p)

/-- Balanced pullback/scalar association is uniquely conjugate to the
section-normalized restriction/direct-image square.
Source: constituent coefficient-transport assembly, Step 3
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def pullScalar (D : FiniteFieldDatum.{u}) (G : Geometry l E F i D)
    (S : ∀ W : Spaces D, Scalar l E F i W.val.left)
    (X Y : Spaces D) (g : X.val.left ⟶ Y.val.left) :
    P (A l E) (aTransition l E) g ⋙ (S X).T ≅
      (S Y).T ⋙ P (B l E F i) (bTransition l E F i) g :=
  ((((adj (A l E) (aTransition l E) g).comp (S X).adjunction).ofNatIsoRight
    (G.pushIso l E F i X Y g).symm).leftAdjointUniq
      ((S Y).adjunction.comp (adj (B l E F i) (bTransition l E F i) g)))

/-- The left composite on the derived category of the entire ramified system.
Source: displayed strict-system equation, proof Step 4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def left (D : FiniteFieldDatum.{u}) (G : Geometry l E F i D)
    (S : ∀ W : Spaces D, Scalar l E F i W.val.left)
    (X' X Y' Y Z' Z : Spaces D)
    (j : X.val.left ⟶ Z.val.left) (p : Z.val.left ⟶ Y.val.left)
    (j' : X'.val.left ⟶ Z'.val.left) (p' : Z'.val.left ⟶ Y'.val.left)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (x : X'.val.left ⟶ X.val.left) (g : Y'.val.left ⟶ Y.val.left)
    (b : Z'.val.left ⟶ Z.val.left)
    (sp : ChosenCartesianSquare b p' p g) (sj : OpenImmersionSquare x j' j b) :=
  Functor.whiskerRight
      (Functor.whiskerLeft (J (A l E) (aTransition l E) j)
          (mateEquiv (adj (A l E) (aTransition l E) p)
            (adj (A l E) (aTransition l E) p')
            (TwoSquare.mk _ _ _ _ (squareP (A l E) (aTransition l E) b p' p g sp.w).hom)
            ).natTrans ≫
        Functor.whiskerRight
          (beta (A l E) (aTransition l E) x j' j b sj.w
            (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom
          (R (A l E) (aTransition l E) p')) (S Y').T ≫
    Functor.whiskerLeft (P (A l E) (aTransition l E) x)
      (comparison l E F i D G S X' Z' Y' j' p') ≫
    Functor.whiskerRight (pullScalar l E F i D G S X' X x).hom
      (compact (B l E F i) (bTransition l E F i) j' p')

/-- The other composite on the same entire strict system, with its quotient transitions.
Source: displayed strict-system equation, proof Step 4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange). -/
def right (D : FiniteFieldDatum.{u}) (G : Geometry l E F i D)
    (S : ∀ W : Spaces D, Scalar l E F i W.val.left)
    (X' X Y' Y Z' Z : Spaces D)
    (j : X.val.left ⟶ Z.val.left) (p : Z.val.left ⟶ Y.val.left)
    (j' : X'.val.left ⟶ Z'.val.left) (p' : Z'.val.left ⟶ Y'.val.left)
    [IsOpenImmersion j] [IsOpenImmersion j']
    (x : X'.val.left ⟶ X.val.left) (g : Y'.val.left ⟶ Y.val.left)
    (b : Z'.val.left ⟶ Z.val.left)
    (sp : ChosenCartesianSquare b p' p g) (sj : OpenImmersionSquare x j' j b) :=
  Functor.whiskerLeft (compact (A l E) (aTransition l E) j p)
      (pullScalar l E F i D G S Y' Y g).hom ≫
    Functor.whiskerRight (comparison l E F i D G S X Z Y j p)
      (P (B l E F i) (bTransition l E F i) g) ≫
    Functor.whiskerLeft (S X).T
      (Functor.whiskerLeft (J (B l E F i) (bTransition l E F i) j)
          (mateEquiv (adj (B l E F i) (bTransition l E F i) p)
            (adj (B l E F i) (bTransition l E F i) p')
            (TwoSquare.mk _ _ _ _
              (squareP (B l E F i) (bTransition l E F i) b p' p g sp.w).hom)).natTrans ≫
        Functor.whiskerRight
          (beta (B l E F i) (bTransition l E F i) x j' j b sj.w
            (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom
          (R (B l E F i) (bTransition l E F i) p'))

attribute [local irreducible] left right comparison pullScalar

/-- Scalar extension preserves the proper/open exchange before evaluation or limit.
The equality is between natural transformations on the ordinary derived category of
entire systems, rather than just its finite evaluated components.
Source: constituent coefficient-transport assembly, proof Steps 1--4
(blueprint: lem-pur-integral-scalar-isomorphism-exchange).
Proof: restriction preserves the proper mate word and the open-unit transpose.
The compact-support scalar mate and the balanced pullback map have adjuncts given
by applying compact support and pullback to the scalar unit. The two displayed
adjuncts agree by naturality of the exchange at that unit. The scalar adjunction
bijection, without any assertion of faithfulness of evaluation, gives the equality. -/
theorem strictScalarIsomorphismExchange
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (G : Geometry l E F i D) (_hG : Compatibility l E F i G)
    (S : ∀ W : Spaces D, Scalar l E F i W.val.left)
    (X' X Y' Y Z' Z : Spaces D)
    (j : X.val.left ⟶ Z.val.left) (p : Z.val.left ⟶ Y.val.left)
    (j' : X'.val.left ⟶ Z'.val.left) (p' : Z'.val.left ⟶ Y'.val.left)
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsProper p] [IsProper p']
    (x : X'.val.left ⟶ X.val.left) (g : Y'.val.left ⟶ Y.val.left)
    (b : Z'.val.left ⟶ Z.val.left) [IsIso x] [IsIso g] [IsIso b]
    (sp : ChosenCartesianSquare b p' p g) (sj : OpenImmersionSquare x j' j b) :
    left l E F i D G S X' X Y' Y Z' Z j p j' p' x g b sp sj =
      right l E F i D G S X' X Y' Y Z' Z j p j' p' x g b sp sj := by
  sorry

end WeilConjectures.IntegralScalarExchange.Systems
