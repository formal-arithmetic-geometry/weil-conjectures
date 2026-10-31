/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FSLogSmoothEtale
public import WeilConjectures.AlgebraicGeometry.LogIdealChartPresentation
public import WeilConjectures.AlgebraicGeometry.LogInfinitesimalLifting
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.PointedEtaleStalk
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.TraceFormula.FgCommutativeMonoidFinitePresentation
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Deformation calculus for a logarithmically smooth chart

Source: ILO X Proposition 1.2, pp.136--138, and XVI Proposition 3.6.3, p.252;
Kato, Logarithmic structures of Fontaine--Illusie, section 3 and Theorem 3.5
(blueprint: lem-sfb-chart-log-smooth-deformation-calculus).

The differential sheaf is the generators-and-relations construction, not an arbitrary
module with postulated properties. Strict fine tests and their lifts use the existing
arbitrary-scheme interfaces. The last clause allows independent compatible strict
etale localizations of both endpoints, including either identity.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The structure ring used for log differentials, obtained from the published
commutative-ring structure presheaf by forgetting commutativity. Its sections and
restrictions are the original regular functions and pullbacks. The sheaf witness
transports `Scheme.isSheaf_etaleStructurePresheaf`: matching ring homomorphisms glue
pointwise in the underlying set sheaf, and separatedness preserves the ring laws.
Source: Stacks Project, Descent, Tag 03DR; ILO VI 1.1
(blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def Scheme.logDifferentialStructureRing (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology RingCat.{u} where
  obj := X.etaleStructurePresheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}
  property := by
    have h : Presieve.IsSheaf X.smallEtaleTopology
        (X.etaleStructurePresheaf ⋙ CategoryTheory.forget CommRingCat.{u}) :=
      (isSheaf_iff_isSheaf_of_type _ _).1
        ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget CommRingCat.{u})).obj
          ⟨X.etaleStructurePresheaf, X.isSheaf_etaleStructurePresheaf⟩).property
    intro E V S hS x hx
    have hQ := h S hS
    let y (e : E) : Presieve.FamilyOfElements
        (X.etaleStructurePresheaf ⋙ CategoryTheory.forget CommRingCat.{u}) S :=
      fun W f hf ↦ (x f hf).hom e
    have hy (e : E) : (y e).Compatible := by
      intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
      exact congrArg (fun φ : E ⟶ RingCat.of Γ(Z.left, ⊤) ↦ φ.hom e)
        (hx g₁ g₂ h₁ h₂ fac)
    let g (e : E) : Γ(V.left, ⊤) := hQ.amalgamate (y e) (hy e)
    have hg (e : E) {W : X.Etale} (f : W ⟶ V) (hf : S f) :
        f.left.appTop (g e) = (x f hf).hom e :=
      hQ.valid_glue (hy e) f hf
    have ext {a b : Γ(V.left, ⊤)}
        (hab : ∀ {W : X.Etale} (f : W ⟶ V), S f →
          f.left.appTop a = f.left.appTop b) : a = b :=
      hQ.isSeparatedFor.ext fun _ f hf ↦ hab f hf
    let φ : E ⟶ RingCat.of Γ(V.left, ⊤) := RingCat.ofHom
      { toFun := g
        map_one' := ext fun f hf ↦ by rw [hg _ f hf, map_one, map_one]
        map_mul' := fun a b ↦ ext fun f hf ↦ by
          rw [map_mul, hg _ f hf, hg _ f hf, hg _ f hf, map_mul]
        map_zero' := ext fun f hf ↦ by rw [hg _ f hf, map_zero, map_zero]
        map_add' := fun a b ↦ ext fun f hf ↦ by
          rw [map_add, hg _ f hf, hg _ f hf, hg _ f hf, map_add] }
    refine ⟨φ, fun W f hf ↦ ?_, fun ψ hψ ↦ ?_⟩
    · change φ ≫ RingCat.ofHom f.left.appTop.hom = x f hf
      ext e
      exact hg e f hf
    · apply RingCat.hom_ext
      apply RingHom.ext
      intro e
      exact ext fun {W} f hf ↦
        (congrArg (fun χ : E ⟶ RingCat.of Γ(W.left, ⊤) ↦ χ.hom e) (hψ f hf)).trans
          (hg e f hf).symm

/-- Ordinary and logarithmic symbols, with their original restriction maps.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogStructure.differentialSymbols {X : Scheme.{u}}
    (M : EtaleLogStructure X) : X.Etaleᵒᵖ ⥤ Type u where
  obj W := Sum Γ(W.unop.left, ⊤) (M.monoidSheaf.obj.obj W)
  map h := ↾(Sum.map (h.unop.left.appTop) (M.monoidSheaf.obj.map h))
  map_id W := by
    ext s
    cases s with
    | inl a =>
      change Sum.inl ((𝟙 W.unop.left : W.unop.left ⟶ W.unop.left).appTop a) = Sum.inl a
      simp
    | inr m => simp
  map_comp h k := by
    ext s
    cases s with
    | inl a =>
      change Sum.inl ((k.unop.left ≫ h.unop.left).appTop a) =
        Sum.inl (k.unop.left.appTop (h.unop.left.appTop a))
      rw [Scheme.Hom.comp_appTop]
      rfl
    | inr m => simp

/-- The free module presheaf on the symbols `da` and `dlog m`.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogStructure.freeDifferentials {X : Scheme.{u}}
    (M : EtaleLogStructure X) : PresheafOfModules.{u} (Scheme.logDifferentialStructureRing X).obj :=
  PresheafOfModules.freeObj M.differentialSymbols

/-- The elementary ordinary symbol in the free module.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogStructure.freeD {X : Scheme.{u}} (M : EtaleLogStructure X)
    (W : X.Etale) (a : Γ(W.left, ⊤)) : M.freeDifferentials.obj (op W) :=
  ModuleCat.freeMk (Sum.inl a)

/-- The elementary logarithmic symbol in the free module.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogStructure.freeDLog {X : Scheme.{u}} (M : EtaleLogStructure X)
    (W : X.Etale) (m : M.monoidSheaf.obj.obj (op W)) :
    M.freeDifferentials.obj (op W) :=
  ModuleCat.freeMk (Sum.inr m)

/-- Exactly the additive, Leibniz, logarithmic, structural and two base relations.
Base functions and log sections range over every relative etale diagram.
Source: Kato section 1; ILO X 1.2 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
def EtaleLogMap.IsDifferentialRelation {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N)
    (W : X.Etale) (s : M.freeDifferentials.obj (op W)) : Prop :=
  (∃ a b, s = M.freeD W (a + b) - M.freeD W a - M.freeD W b) ∨
  (∃ a b, s = M.freeD W (a * b) - a • M.freeD W b - b • M.freeD W a) ∨
  (∃ m n, s = M.freeDLog W (m * n) - M.freeDLog W m - M.freeDLog W n) ∨
  (∃ m, s = M.freeD W (M.alpha.app (op W) m) -
    M.alpha.app (op W) m • M.freeDLog W m) ∨
  (∃ (U : Y.Etale) (k : W.left ⟶ U.left)
    (_hk : k ≫ U.hom = W.hom ≫ f.base) (c : Γ(U.left, ⊤)),
    s = M.freeD W (k.appTop c)) ∨
  (∃ (U : Y.Etale) (k : W.left ⟶ U.left)
    (hk : k ≫ U.hom = W.hom ≫ f.base) (n : N.monoidSheaf.obj.obj (op U)),
    s = M.freeDLog W (f.sectionMap U W k hk n))

/-- The least restriction-stable submodule containing all differential relations.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.differentialRelations {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    M.freeDifferentials.Submodule :=
  sInf {S | ∀ (W : X.Etale) (s : M.freeDifferentials.obj (op W)),
    f.IsDifferentialRelation W s → s ∈ S.obj (op W)}

/-- The presented module presheaf before sheafification, the categorical quotient.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.differentialPresheaf {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    PresheafOfModules.{u} (Scheme.logDifferentialStructureRing X).obj :=
  cokernel f.differentialRelations.ι

/-- The relative logarithmic differential sheaf, obtained by module sheafification.
Source: Kato section 1; ILO X 1.2 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.differentialSheaf {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    SheafOfModules.{u} (Scheme.logDifferentialStructureRing X) :=
  (PresheafOfModules.sheafification (𝟙 (Scheme.logDifferentialStructureRing X).obj)).obj
    f.differentialPresheaf

/-- The canonical generators-to-differentials map: quotient followed by sheafification.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.differentialGeneratorMap {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) :
    M.freeDifferentials ⟶ f.differentialSheaf.val :=
  cokernel.π f.differentialRelations.ι ≫
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Scheme.logDifferentialStructureRing X).obj)).unit.app f.differentialPresheaf

/-- The universal ordinary differential, as an actual section of the constructed sheaf.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.sheafD {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N)
    (W : X.Etale) (a : Γ(W.left, ⊤)) : f.differentialSheaf.val.obj (op W) :=
  f.differentialGeneratorMap.app (op W) (M.freeD W a)

/-- The universal logarithmic differential.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def EtaleLogMap.sheafDLog {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N)
    (W : X.Etale) (m : M.monoidSheaf.obj.obj (op W)) :
    f.differentialSheaf.val.obj (op W) :=
  f.differentialGeneratorMap.app (op W) (M.freeDLog W m)

/-- Etale-local finite freeness, including compatibility of the trivializations on
all objects of the slice site. In particular this is sheaf freeness, not stalkwise
freeness without a neighbourhood. Rank zero and empty sources are allowed.
Source: Kato section 3; ILO XVI 3.6.3 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
def EtaleLogMap.HasFiniteLocallyFreeDifferentials {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) : Prop :=
  ∀ x : X, ∃ (V : X.Etale) (r : ℕ), x ∈ Set.range V.hom ∧
    ∃ e : ∀ (W : X.Etale) (_k : W ⟶ V),
        f.differentialSheaf.val.obj (op W) ≃ₗ[Γ(W.left, ⊤)] (Fin r → Γ(W.left, ⊤)),
      ∀ (W W' : X.Etale) (k : W ⟶ V) (h : W' ⟶ W)
        (s : f.differentialSheaf.val.obj (op W)) (j : Fin r),
        e W' (h ≫ k) (f.differentialSheaf.val.map h.op s) j =
          h.left.appTop (e W k s j)


/-- A relative etale diagram for an inverse-image sheaf, with its prescribed map.
Source: ILO VI 1.1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
structure LogRelativeEtaleTest {T X : Scheme.{u}} (a : T ⟶ X) where
  W : X.Etale
  V : T.Etale
  map : V.left ⟶ W.left
  over : map ≫ W.hom = V.hom ≫ a

/-- A map of relative diagrams, including the square equation.
Source: ILO VI 1.1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
structure LogRelativeEtaleTest.Map {T X : Scheme.{u}} {a : T ⟶ X}
    (q q' : LogRelativeEtaleTest a) where
  source : q.W ⟶ q'.W
  test : q.V ⟶ q'.V
  comm : test.left ≫ q'.map = q.map ≫ source.left

/-- Restriction of functions to the actual base-changed closed subscheme. Its kernel
is the section ideal I on the test object.
Source: Kato section 3 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
noncomputable def logTestReduction {T₀ T : Scheme.{u}} (i : T₀ ⟶ T) (V : T.Etale) :
    Γ(V.left, ⊤) →+* Γ(pullback i V.hom, ⊤) :=
  (pullback.snd i V.hom).appTop.hom

/-- Relative logarithmic derivations into the square-zero ideal, represented on
relative etale diagrams. The monoid homomorphism to `Multiplicative I` is equivalently
an additive homomorphism from the group completion; no integrality assumption is
needed for this universal extension. Naturality supplies a morphism of sheaves.
Source: Kato sections 1 and 3 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
structure EtaleLogMap.LiftDerivation {X Y T₀ T : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {L : EtaleLogStructure T} (f : EtaleLogMap M N)
    (i : T₀ ⟶ T) (a : EtaleLogMap L M) where
  D : ∀ q : LogRelativeEtaleTest a.base, Γ(q.W.left, ⊤) →+ Γ(q.V.left, ⊤)
  delta : ∀ q : LogRelativeEtaleTest a.base,
    M.monoidSheaf.obj.obj (op q.W) →* Multiplicative Γ(q.V.left, ⊤)
  D_ideal : ∀ q c, logTestReduction i q.V (D q c) = 0
  delta_ideal : ∀ q m, logTestReduction i q.V (Multiplicative.toAdd (delta q m)) = 0
  leibniz : ∀ q c d,
    D q (c * d) = q.map.appTop c * D q d + q.map.appTop d * D q c
  compatibility : ∀ q m,
    D q (M.alpha.app (op q.W) m) =
      q.map.appTop (M.alpha.app (op q.W) m) * Multiplicative.toAdd (delta q m)
  D_base : ∀ q (U : Y.Etale) (k : q.W.left ⟶ U.left)
    (_hk : k ≫ U.hom = q.W.hom ≫ f.base) (c : Γ(U.left, ⊤)), D q (k.appTop c) = 0
  delta_base : ∀ q (U : Y.Etale) (k : q.W.left ⟶ U.left)
    (hk : k ≫ U.hom = q.W.hom ≫ f.base) (n : N.monoidSheaf.obj.obj (op U)),
    Multiplicative.toAdd (delta q (f.sectionMap U q.W k hk n)) = 0
  D_naturality : ∀ (q q' : LogRelativeEtaleTest a.base) (h : q.Map q')
    (c : Γ(q'.W.left, ⊤)),
    h.test.left.appTop (D q' c) = D q (h.source.left.appTop c)
  delta_naturality : ∀ (q q' : LogRelativeEtaleTest a.base) (h : q.Map q')
    (m : M.monoidSheaf.obj.obj (op q'.W)),
    h.test.left.appTop (Multiplicative.toAdd (delta q' m)) =
      Multiplicative.toAdd (delta q (M.monoidSheaf.obj.map h.source.op m))

/-- Hom from the pulled-back differential sheaf to the ideal. On each relative diagram
this is a semilinear map to I. Such compatible maps are precisely maps from the tensor
O_T0 tensor_{a0^-1 O_X} a0^-1 omega: annihilation by the reduction kernel makes
semilinearity factor through O_T0. This is an interface for the actual tensor-Hom
universal property, without choosing an unrelated comparison map.
Source: Kato sections 1 and 3 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
structure EtaleLogMap.LiftDifferentialFunctional {X Y T₀ T : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y}
    {L : EtaleLogStructure T} (f : EtaleLogMap M N)
    (i : T₀ ⟶ T) (a : EtaleLogMap L M) where
  app : ∀ q : LogRelativeEtaleTest a.base,
    f.differentialSheaf.val.obj (op q.W) →ₛₗ[q.map.appTop.hom] Γ(q.V.left, ⊤)
  ideal : ∀ q s, logTestReduction i q.V (app q s) = 0
  naturality : ∀ (q q' : LogRelativeEtaleTest a.base) (h : q.Map q')
    (s : f.differentialSheaf.val.obj (op q'.W)),
    h.test.left.appTop (app q' s) = app q (f.differentialSheaf.val.map h.source.op s)

/-- Evaluation at `da` and `dlog m`, specifying the canonical correspondence.
Source: Kato section 1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
def EtaleLogMap.LiftDifferentialFunctional.Represents {X Y T₀ T : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} {L : EtaleLogStructure T}
    {f : EtaleLogMap M N} {i : T₀ ⟶ T} {a : EtaleLogMap L M}
    (H : f.LiftDifferentialFunctional i a) (v : f.LiftDerivation i a) : Prop :=
  (∀ q c, H.app q (f.sheafD q.W c) = v.D q c) ∧
    (∀ q m, H.app q (f.sheafDLog q.W m) = Multiplicative.toAdd (v.delta q m))

/-- The two explicit twisting formulas. Ring maps are compared on relative diagrams
with the same reduction. The log formula uses the actual unit of the log sheaf mapping
to `1 + delta`; its uniqueness is forced by the log-structure unit axiom. This expresses
multiplication by that unit, not multiplication of a log section by a ring element.
Source: Kato section 3; ILO VI 1.1 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
def EtaleLogMap.LiftDerivation.Acts {X Y T₀ T : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} {L : EtaleLogStructure T}
    {f : EtaleLogMap M N} {i : T₀ ⟶ T} {a : EtaleLogMap L M}
    (v : f.LiftDerivation i a) (a' : EtaleLogMap L M) : Prop :=
  ∀ (W : X.Etale) (V : T.Etale) (k k' : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ a.base) (hk' : k' ≫ W.hom = V.hom ≫ a'.base),
    pullback.snd i V.hom ≫ k = pullback.snd i V.hom ≫ k' →
      (∀ c : Γ(W.left, ⊤), k'.appTop c = k.appTop c + v.D ⟨W, V, k, hk⟩ c) ∧
      (∀ m : M.monoidSheaf.obj.obj (op W),
        ∃ e : (L.monoidSheaf.obj.obj (op V))ˣ,
          L.alpha.app (op V) e.val =
            1 + Multiplicative.toAdd (v.delta ⟨W, V, k, hk⟩ m) ∧
          a'.sectionMap W V k' hk' m = a.sectionMap W V k hk m * e.val)

/-- The torsor and tensor-Hom assertions for every strict fine test with a chosen lift.
Quantification over arbitrary test schemes includes restriction to every etale open.
Existence is stated separately by `HasEtaleLocalInfinitesimalLifts`; no global lift is
assumed. Once a lift exists, each derivation gives one lift, and every pair of lifts
has exactly one difference. The two evaluation conditions give the bijection with
linear maps and fix it on the presented generators.
Source: Kato sections 1 and 3 (blueprint: lem-sfb-chart-log-smooth-deformation-calculus). -/
def EtaleLogMap.HasLiftDerivationTorsors {X Y : Scheme.{u}}
    {M : EtaleLogStructure X} {N : EtaleLogStructure Y} (f : EtaleLogMap M N) : Prop :=
  ∀ (T₀ T : Scheme.{u}) (L₀ : EtaleLogStructure T₀) (L : EtaleLogStructure T),
    L₀.IsFine → L.IsFine →
      ∀ (i : EtaleLogMap L₀ L) (a₀ : EtaleLogMap L₀ M) (b : EtaleLogMap L N),
        IsFirstOrderThickening i.base → i.IsStrict → a₀.CompositesEq f i b →
          (∀ (V : T.Etale) (v w : Γ(V.left, ⊤)),
            logTestReduction i.base V v = 0 → logTestReduction i.base V w = 0 →
              v * w = 0 ∧ IsUnit (1 + v) ∧
                (1 + v) * (1 + w) = 1 + (v + w)) ∧
          ∀ a : EtaleLogMap L M, a.CompEq f b → i.CompEq a a₀ →
            (∀ v : f.LiftDerivation i.base a,
              ∃! a' : EtaleLogMap L M,
                a'.CompEq f b ∧ i.CompEq a' a₀ ∧ v.Acts a') ∧
            (∀ a' : EtaleLogMap L M, a'.CompEq f b → i.CompEq a' a₀ →
              ∃! v : f.LiftDerivation i.base a, v.Acts a') ∧
            (∀ v : f.LiftDerivation i.base a,
              ∃! H : f.LiftDifferentialFunctional i.base a, H.Represents v) ∧
            (∀ H : f.LiftDifferentialFunctional i.base a,
              ∃! v : f.LiftDerivation i.base a, H.Represents v)


/-- A chart-log-smooth morphism has locally finite presentation, finite locally free
log differentials, etale-local fine strict square-zero lifts, and the explicitly
normalized derivation torsors. All four assertions persist after compatible etale
localizations on both endpoints with pulled-back log structures.
Source: ILO X 1.2 and XVI 3.6.3; Kato section 3, Theorem 3.5
(blueprint: lem-sfb-chart-log-smooth-deformation-calculus).

Proof (the ten steps of the node):
1. In compatible charts P to Q, finite monoid presentations give a finite presentation
   of Z[Q] over Z[P]. Base change and the affine fibre-product formula make the chart
   target W locally of finite presentation over the base chart. This uses
   lem-trf-fg-commutative-monoid-finite-presentation,
   lem-weil-pbc-finite-presentation-base-change-composition and
   lem-weil-pbc-fibre-product-affine-spectra.
2. Compose with the smooth comparison and the etale base chart, then descend local
   finite presentation through the source chart cover using
   lem-trf-lfp-fppf-source-locality and
   lem-sbc-locally-finite-presentation-composition. The empty source is allowed.
3. Pull the source chart cover back to the test thickening and lift it to T using
   sbc-lem-thickening-etale-site. Formal etale uniqueness, from
   lem-weil-pbc-flat-unramified-formally-etale, extends the base chart map.
   lem-sfb-fine-chart-logification-thickening supplies its associated log map.
4. Strictness identifies log-stalk fibres with free 1+I torsors, by
   lem-sfb-fine-chart-logification-thickening. Group completion gives the exact
   sequence 0 to I to L^gp to L0^gp to 0 and the cartesian description of L.
5. The kernel and torsion cokernel orders of the chart group map are units on the
   square-zero test. Apply lem-sfb-compatible-abelian-group-lifting to lift the
   chart group map compatibly with the base. The cartesian description puts Q in L.
6. Finite monoid presentations and cofiltered pointed etale neighbourhoods spread
   this stalk map. Construct T to W from its monomials, then apply ordinary smooth
   lifting to the comparison. The logification universal property gives the log lift.
   Uses lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered,
   lem-weil-pbc-morphism-into-affine-scheme and def-sbc-smooth-morphisms.
7. For compatible etale localizations of source and target, lift first to X, then
   uniquely to the new source. Formal etale uniqueness over Y identifies the two
   maps to the new target. Logification fixes the log maps, including identity cases.
8. Apply lem-sfb-lifting-log-differential-calculus with the local finite presentation
   and arbitrary fine strict lifting just established. Its presented differential
   sheaf is exactly differentialSheaf, yielding finite local freeness and torsors.
9. Evaluation on da and dlog identifies linear functionals with the displayed
   derivations. Square zero verifies addition on ring maps and multiplication by
   1+delta on log maps. The strict log-stalk fibres give unique differences of lifts.
10. Etale base change and cancellation give local finite presentation after either
    localization; finite-type algebras over Noetherian rings preserve Noetherianness.
    Reapply the lifting differential calculus, with the same restricted formulas.
-/
theorem EtaleLogHom.chart_logSmooth_deformation_calculus
    {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y) (hf : f.IsLogSmooth) :
    (LocallyOfFinitePresentation f.base ∧
      f.toLogMap.HasFiniteLocallyFreeDifferentials ∧
      f.toLogMap.HasEtaleLocalInfinitesimalLifts ∧
      f.toLogMap.HasLiftDerivationTorsors) ∧
    ∀ (X' Y' : FineSaturatedLogScheme.{u})
      (e : EtaleLogHom X' X) (d : EtaleLogHom Y' Y) (f' : EtaleLogHom X' Y'),
      e.toLogMap.IsStrictEtale → d.toLogMap.IsStrictEtale →
      e.toLogMap.CompositesEq f.toLogMap f'.toLogMap d.toLogMap →
        LocallyOfFinitePresentation f'.base ∧
          f'.toLogMap.HasFiniteLocallyFreeDifferentials ∧
          f'.toLogMap.HasEtaleLocalInfinitesimalLifts ∧
          f'.toLogMap.HasLiftDerivationTorsors := by
  sorry

end AlgebraicGeometry
