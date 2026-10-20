/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.SixFunctors.CompactCoefficientComposition
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.Compactification.Triangle
public import Sheaf.Paper.SystemCompactificationProjectionSubstitution

/-! # Finite-free compact-support coefficient comparison and composition

Source: blueprint main-20261015, lem-coef-rational-operations, proof paragraph 8;
Stacks Project, Tags 0F7J, 0F7B, 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition).

The system maps below are maps in the ordinary derived category of module sheaves
on the vertical sequence site, before evaluation or inverse limit. Coefficient
comparison is a scalar-adjunction mate. Composition is the proper/open word in a
triangle, transported through the graph common refinements of compactifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.SemilinearSections

namespace WeilConjectures.FiniteFreeCompactComposition

section SystemComposition
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Compact support on the actual semilinear-system category, at a fixed compactification.
Source: blueprint paragraph 8, simultaneous model; Zheng 4.1 and 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  J C τ c.i ⋙ R C τ c.g

/-- The canonical reverse refinement word, with its open-unit and proper-compositor factors.
Source: Stacks 0F7B and 0F7J, proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def refinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) : support C τ d ⟶ support C τ c :=
  haveI := c.quasiCompact_openImmersion inferInstance
  haveI := d.quasiCompact_openImmersion inferInstance
  Functor.whiskerRight
    ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight (sId C τ X).inv (J C τ d.i) ≫
      gamma C τ c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp _).symm)) (R C τ d.g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ c.i)
      ((sComp C τ r.hom d.g).hom ≫
        eqToHom (congrArg (R C τ) r.hom_g))

/-- The graph common-refinement comparison, inverted only on its isomorphism domain.
The zero extension outside that domain is the existing `inverseOnDomain` convention.
Source: Stacks 0F7J; blueprint paragraph 8, fixed compactifications
(blueprint: lem-coef-finite-free-compact-composition). -/
def change {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (M : Derived C τ X) :
    (support C τ c).obj M ⟶ (support C τ d).obj M :=
  (refinement C τ (Compactification.infFst c d)).app M ≫
    FiniteFreeCoefficients.Sites.inverseOnDomain
      ((refinement C τ (Compactification.infSnd c d)).app M)

/-- The canonical proper/open composition word in a compatible triangle.
Source: Stacks 0F7J, the cartesian triangle; blueprint proof paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def triangleWord {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g] (T : Compactification.Triangle f g) :
    support C τ T.cf ⋙ support C τ T.cg ⟶ support C τ T.cfg :=
  haveI := T.cf.quasiCompact_openImmersion inferInstance
  haveI := T.cg.quasiCompact_openImmersion inferInstance
  haveI : QuasiCompact T.q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    T.isPullback inferInstance
  (Functor.associator _ _ _).symm.hom ≫
    Functor.whiskerRight ((Functor.associator _ _ _).hom) _ ≫
    Functor.whiskerRight (Functor.whiskerLeft (J C τ T.cf.i)
      (gamma C τ T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)) _ ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight ((jComp C τ T.cf.i T.q).hom ≫
      (jCongr C τ T.i_q).hom) _) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J C τ T.cfg.i)
      ((sComp C τ T.p T.cg.g).hom ≫ eqToHom (congrArg (R C τ) T.p_g))

/-- The system compositor with the three prescribed compactifications. The auxiliary
triangle is the canonical geometric one; both transports use graph common refinements.
Source: Stacks 0F7J; blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def compositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (M : Derived C τ X) :
    (support C τ cg).obj ((support C τ cf).obj M) ⟶ (support C τ cfg).obj M :=
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  let T := Compactification.Triangle.ofHasCompactification f g
  (support C τ cg).map (change C τ cf T.cf M) ≫
    change C τ cg T.cg ((support C τ T.cf).obj M) ≫
    (triangleWord C τ T).app M ≫ change C τ T.cfg cfg M

end SystemComposition

section Coefficients
variable (l : ℕ) [Fact l.Prime] (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The upper quotient uses the image of the base uniformizer, even when ramified.
Level n denotes positive exponent n+1. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperStage (n : ℕ) : Stage l E where
  field := L
  inclusion := i
  exponent := ⟨n + 1, Nat.succ_pos n⟩

/-- The same positive exponent at the base field. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerStage (n : ℕ) : Stage l E := baseStage ⟨n + 1, Nat.succ_pos n⟩

/-- Canonical inclusion on the quotient rings, induced by the integer-ring inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def inclusion (n : ℕ) : (lowerStage l E n).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap { embedding := i, over_base := AlgHom.comp_id i, level := le_rfl })

/-- Actual adjacent quotient maps at an arbitrary field-extension stage.
Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def upperTransition (n : ℕ) :
    (upperStage l E L i (n + 1)).ring →+* (upperStage l E L i n).ring :=
  (Arrow.ringMap (s := upperStage l E L i (n + 1))
    (t := upperStage l E L i n)
    { embedding := AlgHom.id (Padic l) L
      over_base := AlgHom.id_comp i
      level := Nat.le_succ _ })

/-- Base-field adjacent quotient maps. Source: blueprint paragraph 8, strict transitions
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerTransition (n : ℕ) : (lowerStage l E (n + 1)).ring →+* (lowerStage l E n).ring :=
  upperTransition l E E (AlgHom.id (Padic l) E) n

/-- The constant coefficient ring tower on the original small pro-etale skeleton.
Source: blueprint paragraph 8; Zheng Construction 4.1
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (upperStage l E L i n).ring

/-- The base coefficient tower. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerRings (n : ℕ) : CommRingCat.{u + 1} := CommRingCat.of (lowerStage l E n).ring

/-- Bundled quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev upperMaps (n : ℕ) : upperRings l E L i (n + 1) ⟶ upperRings l E L i n :=
  CommRingCat.ofHom (upperTransition l E L i n)

/-- Bundled base quotient transition. Source: blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev lowerMaps (n : ℕ) : lowerRings l E (n + 1) ⟶ lowerRings l E n :=
  CommRingCat.ofHom (lowerTransition l E n)

/-- The coefficient inclusion is the constant sheaf of the actual quotient inclusion.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientInclusion (W : Scheme.{u}) (n : ℕ) :
    coefficients (lowerRings l E) W n ⟶ coefficients (upperRings l E L i) W n :=
  (constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (inclusion l E L i n))

/-- The canonical inclusions commute with the strict quotient transitions.
Source: blueprint paragraph 8, system clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both quotient composites send the residue of r in O_E to the residue of i(r)
in O_L/(i(pi)^(n+1)). Quotient induction proves equality of ring maps; functoriality
of constant sheafification gives the displayed equality on the whole ring tower. -/
theorem coefficientInclusion_commutes (W : Scheme.{u}) (n : ℕ) :
    coefficientInclusion l E L i W (n + 1) ≫
        transition (upperRings l E L i) (upperMaps l E L i) W n =
      transition (lowerRings l E) (lowerMaps l E) W n ≫
        coefficientInclusion l E L i W n := by
  sorry

/-- Simultaneous normalized K-flat coefficient extension, with evaluation comparisons
specified by the tensor/restriction adjunction. Only universal models are selected.
Source: Zheng 4.1, 4.10 and Stacks 06YY, blueprint paragraph 8
(blueprint: lem-coef-finite-free-compact-composition). -/
def scalarData (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some
      |>.coefficientExtension (coefficients (upperRings l E L i) W)
        (transition (upperRings l E L i) (upperMaps l E L i) W)
        (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W)

/-- Actual ordinary restriction along the map of ring sheaves on the sequence site.
Source: blueprint paragraph 8; Stacks 03CZ
(blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restriction (W : Scheme.{u}) :=
  res (systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (coefficients (upperRings l E L i) W)
    (transition (upperRings l E L i) (upperMaps l E L i) W)
    (coefficientInclusion l E L i W) (coefficientInclusion_commutes l E L i W))


/-- Derived restriction is the exact localization of the actual system restriction.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
abbrev restrictionD (W : Scheme.{u}) := (restriction l E L i W).mapDerivedCategory

/-- The ordinary direct-image restriction comparison is fixed on every section.
Source: blueprint paragraph 8, restriction of scalars
(blueprint: lem-coef-finite-free-compact-composition).
Proof: both functors have sections M_n(U times_Y X); the coefficient actions are
through the same inclusion of quotient rings. The identity gives mutually inverse
linear maps, commuting with every vertical and horizontal restriction. Extensionality
of module sheaves proves uniqueness of the natural isomorphism. -/
theorem pushRestriction_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f ≅
      push (upperRings l E L i) (upperMaps l E L i) f ⋙ restriction l E L i Y,
      ∀ (M : Modules (upperRings l E L i) (upperMaps l E L i) X)
        (n : ℕ) (U : Y.ProEt)
        (x : ((restriction l E L i X ⋙ push (lowerRings l E) (lowerMaps l E) f).obj M).val.obj
          (op (n, U))), HEq ((d.hom.app M).val.app (op (n, U)) x) x := by
  sorry

/-- The ordinary pullback restriction square is the transpose of the section identity.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestrictionInv {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv (ordinaryAdj (upperRings l E L i) (upperMaps l E L i) f)
    (ordinaryAdj (lowerRings l E) (lowerMaps l E) f)).symm
      (pushRestriction_existsUnique l E L i f).choose.inv

/-- The specified pullback comparison is invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: inverse image of constant coefficient rings identifies the two scalar actions.
The ordinary mate is the identity on the pulled-back underlying additive sheaf; its
inverse is that same identity. The section normalization fixes the mate uniquely. -/
theorem pullRestrictionInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pullRestrictionInv l E L i f) := by
  sorry

/-- Exact localization of the specified inverse-image scalar square.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pullRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i X ≅
      restrictionD l E L i Y ⋙ P (lowerRings l E) (lowerMaps l E) f :=
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.1
  letI := (pull_exact (lowerRings l E) (lowerMaps l E) f).2.2
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.1
  letI := (pull_exact (upperRings l E L i) (upperMaps l E L i) f).2.2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@asIso _ _ _ _ (pullRestrictionInv l E L i f)
        (pullRestrictionInv_isIso l E L i f)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Proper direct-image restriction is the actual derived adjunction mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def pushRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R (upperRings l E L i) (upperMaps l E L i) f ⋙ restrictionD l E L i Y ⟶
      restrictionD l E L i X ⋙ R (lowerRings l E) (lowerMaps l E) f :=
  mateEquiv (adj (upperRings l E L i) (upperMaps l E L i) f)
    (adj (lowerRings l E) (lowerMaps l E) f) (pullRestriction l E L i f).inv

/-- Finite freeness makes the canonical direct-image restriction mate invertible.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: a fixed O_E-basis of O_L reduces to a basis of every B_n over A_n, compatible
with quotient transitions. Thus extension on strict systems is exact. Its right
adjoint restriction preserves K-injectives. The section identity computing ordinary
direct image therefore computes its derived mate on K-injective system resolutions.
The inverse section identity yields the inverse, compatibly with units and counits. -/
theorem pushRestriction_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pushRestriction l E L i f) := by
  sorry

/-- The open restriction square is fixed by the open unit and the same pullback mate.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def openRestrictionInv {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (mateEquiv (jAdj (upperRings l E L i) (upperMaps l E L i) j)
    (jAdj (lowerRings l E) (lowerMaps l E) j)).symm (pullRestriction l E L i j).hom

/-- The open-unit restriction mate is an isomorphism on whole systems.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition).
Proof: on the open both maps are the identity on sections, and outside it both
extensions vanish. These maps commute with the quotient transitions and are inverse
already on ordinary systems. Exact localization preserves the inverse identities. -/
theorem openRestrictionInv_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    IsIso (openRestrictionInv l E L i j) := by
  sorry

/-- The whole-system compact-support restriction comparison, in open-then-proper order.
Source: blueprint paragraph 8 (blueprint: lem-coef-finite-free-compact-composition). -/
def supportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    restrictionD l E L i X ⋙ support (lowerRings l E) (lowerMaps l E) c ≅
      support (upperRings l E L i) (upperMaps l E L i) c ⋙ restrictionD l E L i Y :=
  Functor.isoWhiskerRight
    (@asIso _ _ _ _ (openRestrictionInv l E L i c.i)
      (openRestrictionInv_isIso l E L i c.i)) _ ≪≫
    Functor.isoWhiskerLeft _
      (@asIso _ _ _ _ (pushRestriction l E L i c.g) (pushRestriction_isIso l E L i c.g)).symm

/-- The specified B-linear whole-system coefficient map, obtained by scalar adjunction.
Source: blueprint paragraph 8; Stacks 06YY and 07A6
(blueprint: lem-coef-finite-free-compact-composition). -/
def coefficientComparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support (lowerRings l E) (lowerMaps l E) c ⋙ (scalarData l E L i Y).scalar.T ⟶
      (scalarData l E L i X).scalar.T ⋙ support (upperRings l E L i) (upperMaps l E L i) c :=
  ((mateEquiv (scalarData l E L i X).scalar.adjunction
    (scalarData l E L i Y).scalar.adjunction).symm
      (TwoSquare.mk _ (support (upperRings l E L i) (upperMaps l E L i) c)
        (support (lowerRings l E) (lowerMaps l E) c) _
          (supportRestriction l E L i c).hom)).natTrans


/-- The source simultaneous normalized K-flat calculus, retaining every reduction map.
Source: blueprint paragraph 8; Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def lowerCalculus (W : Scheme.{u}) :=
  (semilinearDerivedSections.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)).some.systems

/-- The normalized finite-Tor constructible system domain. The ordered Tor interval is
allowed to depend on the positive level, and every degree-zero module sheaf is tested.
Source: blueprint paragraph 8, normalized systems; Stacks 08FZ and Zheng 4.10
(blueprint: lem-coef-finite-free-compact-composition). -/
def normalizedCtf (W : Scheme.{u})
    (M : Derived (lowerRings l E) (lowerMaps l E) W) : Prop :=
  Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
    (coefficients (lowerRings l E) W) (transition (lowerRings l E) (lowerMaps l E) W)
    (lowerCalculus l E W).scalar M ∧
    ∀ n : ℕ,
      Set.Finite {j : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) j).obj
            ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W)
              (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))} ∧
      (∀ j : ℤ, Scheme.IsConstructibleProEtaleCoefficientModuleSheaf W
        (lowerStage l E n).ring
          ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                  (coefficients (lowerRings l E) W)
                  (transition (lowerRings l E) (lowerMaps l E) W) n).obj M))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
          (coefficients (lowerRings l E) W n)) (j : ℤ),
          (j < a ∨ b < j) → IsZero ((DerivedCategory.homologyFunctor
            (SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
              (coefficients (lowerRings l E) W n)) j).obj
                (((lowerCalculus l E W).levelClosed n).tensor.obj
                  ((e.{u + 1, u, u + 1} (Scheme.ProEt.topology W)
                    (coefficients (lowerRings l E) W)
                    (transition (lowerRings l E) (lowerMaps l E) W) n).obj M,
                    (DerivedCategory.singleFunctor _ 0).obj N)))


/-- Finite-free coefficient extension preserves the bounded etale-origin class on
finite-Tor constructible inputs, for every universal B-linear tensor presentation.
Source: blueprint paragraph 8; lem-sf-proetale-constructible-origin
(blueprint: lem-coef-finite-free-compact-composition).
Proof: represent the bounded constructible input on the etale site. Tensor its
bounded K-flat model with the finite free coefficient algebra. Forgetting coefficients
is a finite direct sum in a fixed reduced integer-ring basis, hence stays bounded.
The normalized tensor/site comparison identifies the pro-etale realization with this
model. Universality identifies every tensor presentation with it, preserving its unit.
Thus the resulting object has the claimed bounded-below etale-origin witness. -/
theorem finiteTensorOrigin (n : ℕ) (X : Scheme.{u})
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K) :
    ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (upperStage l E L i n).ring) X M.obj := by
  sorry

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [qcF : QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [qcG : QuasiCompact g]

include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The specified finite-level B-linear coefficient maps commute with compact-support
composition. The equation uses universal tensor presentations, hence fixes B-linearity
and includes every presentation of the canonical derived tensor functor.
Source: blueprint paragraph 8; Stacks 0F7J
(blueprint: lem-coef-finite-free-compact-composition).
Proof: apply lem-pur-finite-free-compact-composition. Its c_h is exactly the proper
counit-transpose coefficient comparison followed by the open balancing comparison
of lem-coef-etale-open-tensor. The coefficient algebra is O_L/pi^n, finite free
by lem-coef-finite-free-extension, not O_L/v^n. Forgetting the B-action identifies
the comparison with finite-sum distributivity in a reduced O_E-basis of O_L.
The compact-support site comparison and comparison-open-tensor coherence transport
this same map and the canonical compositor to the pro-etale origin class. Substitute
M=K in that lemma's equation; universal tensor map functoriality gives the displayed
identity. Finite freeness makes each comparison invertible by finite-sum
distributivity. This calculation uses no faithfulness of derived scalar restriction. -/
theorem finiteLevelComposition (n : ℕ)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (lowerStage l E n).ring)))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (lowerStage l E n).ring) X K)
    (M : CoefficientTensorModel (inclusion l E L i n) X K)
    (N : CoefficientTensorModel (inclusion l E L i n) Y
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K))
    (P₀ : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) f).obj K)))
    (Q : CoefficientTensorModel (inclusion l E L i n) Z
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} (lowerStage l E n).ring) (f ≫ g)).obj K)) :
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ∧
    IsIso (compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀) ∧
    IsIso (compactSupportCoefficientComparison
      (HasCompactification.compactification (f ≫ g)) M Q) ∧
    compactSupportCoefficientComparison (HasCompactification.compactification g) N P₀ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (upperStage l E L i n).ring) g).map
          (compactSupportCoefficientComparison (HasCompactification.compactification f) M N) ≫
        (originCompositionAmbient (upperStage l E L i n).ring f g).hom.app
          ⟨M.obj, finiteTensorOrigin l E L i n X K hK M⟩ =
      P₀.map Q ((originCompositionAmbient (lowerStage l E n).ring f g).hom.app
        ⟨K, hK.plusEtaleOrigin⟩) ≫
          compactSupportCoefficientComparison (HasCompactification.compactification (f ≫ g)) M Q :=
  by sorry

include D hl overX overY overZ sepX ftX qcX sepY ftY qcY sepZ ftZ qcZ
  overF overG sepF ftF qcF sepG ftG qcG in
/-- The same equality in the ordinary derived category of B-coefficient systems,
with the specified proper/open compositor and coefficient mate, before total limit.
Source: blueprint paragraph 8, simultaneous semilinear-section clause
(blueprint: lem-coef-finite-free-compact-composition).
Proof: (1) Fix one O_E-basis of O_L and reduce it at every positive level. It identifies
B_m tensor^L_A_m A_n with B_n, compatibly with strict quotient transitions. The B-tower
is normalized and constructible of Tor amplitude [0,0]. (2) The simultaneous model of
lem-coef-semilinear-derived-sections provides the actual system scalar adjunction and
geometric operations. Restriction is exact and, as the right adjoint of exact finite
free extension, preserves K-injectives. Hence it commutes with derived direct images,
open extension, their units and counits, and the displayed proper/open compositors.
(3) Under Res T=P tensor B, restriction of coefficientComparison is precisely the
system projection word: transpose the proper counit and then apply open balancing.
This identifies constructed system maps, not just their evaluations.
(4) Apply lem-pur-system-level-projection-formula-coherence to K and the normalized
constant B-tower. It gives equality of restrictions of the two displayed B-system
maps in D(A-systems). Their common source is T(F_g F_f K). The adjunction T ⊣ Res
identifies each map with its restriction composed with the unit; equal restrictions
therefore give equal transposes and equal B-system maps. Derived Res need not be
faithful. (5) Run this construction with the fixed compactifications. The refinement
substitution and cocycle laws of lem-pur-system-compactification-pf-substitution
identify the graph-refinement transports in compositor with the canonical ones.
The proper/open and refinement comparisons are isomorphisms on this domain;
finite-sum distributivity makes the coefficient comparisons isomorphisms. The
equality is established before evaluation and before any inverse limit. -/
theorem systemComposition
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : Derived (lowerRings l E) (lowerMaps l E) X) (hK : normalizedCtf l E X K) :
    IsIso ((coefficientComparison l E L i cf).app K) ∧
    IsIso ((coefficientComparison l E L i cg).app
      ((support (lowerRings l E) (lowerMaps l E) cf).obj K)) ∧
    IsIso ((coefficientComparison l E L i cfg).app K) ∧
    IsIso (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ∧
    IsIso (compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
      ((scalarData l E L i X).scalar.T.obj K)) ∧
    (coefficientComparison l E L i cg).app ((support (lowerRings l E) (lowerMaps l E) cf).obj K) ≫
        (support (upperRings l E L i) (upperMaps l E L i) cg).map
          ((coefficientComparison l E L i cf).app K) ≫
        compositor (upperRings l E L i) (upperMaps l E L i) cf cg cfg
          ((scalarData l E L i X).scalar.T.obj K) =
      (scalarData l E L i Z).scalar.T.map
          (compositor (lowerRings l E) (lowerMaps l E) cf cg cfg K) ≫
        (coefficientComparison l E L i cfg).app K := by
  sorry

end Geometry
end Coefficients
end WeilConjectures.FiniteFreeCompactComposition
