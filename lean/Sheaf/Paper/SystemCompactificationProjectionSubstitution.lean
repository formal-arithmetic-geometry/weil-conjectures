/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.SystemTensorMateArrows
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import Sheaf.Paper.SystemClopenTensorCompatibility
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Compactification.Over

import Sheaf.Paper.SystemNormalizedTensorClosure
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.RefinementComparisonIsomorphism
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.AmbientProperOpenPasting

/-! # Refinement substitution in strict-system projection maps

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7J, 0B56 and 0ATU;
agent-formulated strict-system refinement compatibility
(blueprint: lem-pur-system-compactification-pf-substitution).

All morphisms below belong to ordinary unbounded derived categories of actual
semilinear systems. Bounds are chosen independently at each positive coefficient level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.SystemTensorMate

section SystemLevels

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- One finite coefficient level, in its original coefficient universe.
Source: Weil blueprint, def-weil-finite-tor-amplitude
(blueprint: lem-pur-system-compactification-pf-substitution). -/
abbrev Level (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.D.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (integralCoefficientCommRingSheaf.{u, u + 1} l E X n)

/-- Bounded cohomology with intrinsically constructible cohomology sheaves.
Source: Weil blueprint, def-weil-finite-tor-amplitude, its D^b_c input
(blueprint: lem-pur-system-compactification-pf-substitution). -/
def levelBoundedConstructible (X : Scheme.{u}) (n : ℕ) (M : Level l E X n) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
    (normalizedDVRModules.{u, u + 1} l E X n) i).obj M)} ∧
    ∀ i : ℤ, Scheme.IsConstructibleProEtaleCoefficientModuleSheaf X
      (ULift.{u + 1, u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
      ((DerivedCategory.homologyFunctor (normalizedDVRModules.{u, u + 1} l E X n) i).obj M)

/-- D^b_ctf at a single finite level: bounded constructibility and an ordered Tor
interval working for every module sheaf in degree zero. The tensor is the level
closed tensor in the canonical simultaneous K-flat section model.
Source: Weil blueprint, def-weil-finite-tor-amplitude; Stacks Tag 08FZ
(blueprint: lem-pur-system-compactification-pf-substitution). -/
def finiteTorConstructibleSystemLevel (o : TensorOperations l E)
    (X : Scheme.{u}) (n : ℕ) (M : Level l E X n) : Prop :=
  levelBoundedConstructible l E X n M ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ (F : normalizedDVRModules.{u, u + 1} l E X n) (i : ℤ),
      (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (normalizedDVRModules.{u, u + 1} l E X n) i).obj
          (((o.systems X).levelClosed n).tensor.obj
            (M, (DerivedCategory.singleFunctor (normalizedDVRModules.{u, u + 1} l E X n) 0).obj F)))

end SystemLevels

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary identity direct image is uniquely fixed by restriction along the
identity fibre-product isomorphism. Source: Stacks 0F7J, identity normalization
(blueprint: lem-pur-system-compactification-pf-substitution).
Proof: on (n,U), restrict along the graph U → U ×_X X. Restriction along the inverse
is its inverse, and the constant-section normalization makes both maps linear.
They commute with vertical and horizontal restrictions. Sections determine uniqueness. -/
theorem refinementDirectId_existsUnique (X : Scheme.{u}) :
    ∃! e : direct l E (𝟙 X) ≅ 𝟭 (S l E X),
      ∀ (M : S l E X) (n : ℕ) (U : X.ProEt)
        (x : ((direct l E (𝟙 X)).obj M).val.obj (op (n, U))),
        (e.hom.app M).val.app (op (n, U)) x =
          M.val.map (Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ X).inv.app U)).op x := by
  sorry

/-- The inverse-image identity, with its ordinary adjunction-unit normalization.
Source: Stacks 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementPullId (o : TensorOperations l E) (X : Scheme.{u}) :
    o.P (𝟙 X) ≅ 𝟭 (D l E X) :=
  Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointIdIso
    (o.adj (𝟙 X)) (refinementDirectId_existsUnique (l := l) (E := E) X).choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The direct-image identity is the adjunction conjugate of the normalized pullback identity.
Source: Stacks 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementPushId (o : TensorOperations l E) (X : Scheme.{u}) :
    pushDerived l E (𝟙 X) ≅ 𝟭 (D l E X) :=
  (conjugateIsoEquiv Adjunction.id (o.derivedAdj (𝟙 X)) (refinementPullId o X)).symm

/-- The canonical direct-image compositor is conjugate to the actual pullback compositor.
Source: Stacks 0D6E, 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementPushComp (o : TensorOperations l E) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushDerived l E (f ≫ g) ≅ pushDerived l E f ⋙ pushDerived l E g :=
  (conjugateIsoEquiv ((o.derivedAdj g).comp (o.derivedAdj f))
    (o.derivedAdj (f ≫ g)) (o.pComp f g).symm).symm

/-- Positive-level evaluation in the ordinary derived system category.
Source: Zheng 4.1, 4.10 (blueprint: lem-pur-system-compactification-pf-substitution). -/
abbrev refinementLevel (X : Scheme.{u}) (n : ℕ) : D l E X ⥤ Level l E X n :=
  SemilinearSections.e.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X) n

/-- The comparison domain has bounded constructible levels, with no common bound.
Source: Stacks 0F7B, 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementDomain (X : Scheme.{u}) (M : D l E X) : Prop :=
  ∀ n : ℕ, levelBoundedConstructible l E X n ((refinementLevel X n).obj M)

/-- Normalization uses the adjoints of actual system transitions; finiteness is levelwise.
Source: the node's normalized D^b_ctf domain, Stacks 08FZ and Zheng 4.10
(blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementNormalizedCtf (o : TensorOperations l E) (X : Scheme.{u})
    (M : D l E X) : Prop :=
  SemilinearSections.Normalized.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X) (o.systems X).scalar M ∧
    ∀ n : ℕ, finiteTorConstructibleSystemLevel l E o X n ((refinementLevel X n).obj M)

variable (o : TensorOperations l E) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]

/-- Compactification opens are quasi-compact because their composite with the proper map is.
Source: Stacks 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
instance refinementOpenQuasiCompact (c : Compactification f) : QuasiCompact c.i :=
  c.quasiCompact_openImmersion inferInstance


/-- The compactification-relative functor on ambient unbounded systems.
Source: Stacks 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
abbrev refinementImage (c : Compactification f) := o.J c.i ⋙ pushDerived l E c.g

/-- The geometric proper/open mate in the refinement square, including the canonical
identity direct-image identification on its left edge.
Source: Stacks 0F7B (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementGamma {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : D l E X) :
    (o.J c₂.i).obj M ⟶ (pushDerived l E r.hom).obj ((o.J c₁.i).obj M) :=
  (o.J c₂.i).map ((refinementPushId o X).inv.app M) ≫
    (o.gamma c₁.i (𝟙 X) r.hom c₂.i (r.i_hom.trans (Category.id_comp _).symm)).app M

/-- The compositor R_p1 → R_p2 R_u at a compactification refinement.
Source: Stacks 0D6E, 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementCompositor {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
    pushDerived l E c₁.g ≅ pushDerived l E r.hom ⋙ pushDerived l E c₂.g :=
  eqToIso (congrArg (fun g ↦ pushDerived l E g) r.hom_g.symm) ≪≫
    refinementPushComp o r.hom c₂.g

/-- The specified compactification projection word: proper projection, open tensor,
then the canonical pullback compositor identifying j^* p^* with f^*.
Source: Stacks 0B56 (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementPF (c : Compactification f) (M : D l E X) (N : D l E Y) :
    (o.T Y).obj ((refinementImage o c).obj M, N) ⟶
      (refinementImage o c).obj ((o.T X).obj (M, (o.P f).obj N)) :=
  o.projection c.g ((o.J c.i).obj M) N ≫
    (pushDerived l E c.g).map
      ((o.delta c.i M ((o.P c.g).obj N)).hom ≫
        (o.J c.i).map ((o.T X).map
          (Prod.mkHom (𝟙 M)
            (((o.pComp c.i c.g) ≪≫
              eqToIso (congrArg (fun g ↦ o.P g) c.comm.symm)).hom.app N))))

section Geometry
variable (K : FiniteFieldDatum.{u}) (hl : l ≠ K.p)
  [overX : X.Over (Spec (.of K.k))] [overY : Y.Over (Spec (.of K.k))]
  [separatedX : IsSeparated (X ↘ Spec (.of K.k))]
  [finiteTypeX : LocallyOfFiniteType (X ↘ Spec (.of K.k))]
  [quasiCompactX : QuasiCompact (X ↘ Spec (.of K.k))]
  [separatedY : IsSeparated (Y ↘ Spec (.of K.k))]
  [finiteTypeY : LocallyOfFiniteType (Y ↘ Spec (.of K.k))]
  [quasiCompactY : QuasiCompact (Y ↘ Spec (.of K.k))]
  [overF : f.IsOver (Spec (.of K.k))] [separatedF : IsSeparated f]
  [finiteTypeF : LocallyOfFiniteType f]

include K hl overX overY separatedX finiteTypeX quasiCompactX
  separatedY finiteTypeY quasiCompactY overF separatedF finiteTypeF in
/-- The actual refinement mate is invertible on systems with bounded constructible levels.
Source: Stacks 0F7B, 0F7J (blueprint: lem-pur-system-compactification-pf-substitution).
Proof: for each positive level choose the bounded etale-origin witness supplied by
lem-sf-proetale-constructible-origin. Apply lem-cbc-strict-tower-proper-open-calculus
only to the constant auxiliary tower over that fixed finite ring. The intrinsic
varying-ring proper/open pasting construction identifies the evaluation of gamma
with that fixed-ring mate. The level mate is invertible. Joint conservativity from
lem-coef-semilinear-derived-sections proves invertibility in the derived system
category. This uses no faithfulness of evaluation and no bound uniform in the level. -/
theorem refinementGamma_isIso {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : D l E X) (hM : refinementDomain X M) : IsIso (refinementGamma o r M) := by
  sorry

/-- The specified refinement comparison, using the inverse of the actual geometric mate.
Source: Stacks 0F7J (blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementTheta {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : D l E X) (hM : refinementDomain X M) :
    (refinementImage o c₁).obj M ≅ (refinementImage o c₂).obj M :=
  (refinementCompositor o r).app ((o.J c₁.i).obj M) ≪≫
    (pushDerived l E c₂.g).mapIso
      (@asIso _ _ _ _ (refinementGamma o r M) (refinementGamma_isIso o K hl r M hM)).symm

/-- The two canonical projection/refinement words agree before evaluation.
Source: Stacks 0F7B, 0F7J and 0B56
(blueprint: lem-pur-system-compactification-pf-substitution).
Proof: (1) Use lem-coef-semilinear-derived-sections for the actual simultaneous
operations and their adjunctions. Naturality of projection follows from its
counit transpose; delta is the open-unit-normalized comparison of
lem-sf-open-tensor-normalization. (2) At each level, lem-sf-pullback-tor-amplitude
preserves the Tor interval of N, and lem-sf-tensor-ctf adds the two level intervals.
The transition formulas of lem-pur-system-normalized-tensor-closure show that
M tensor P_f N is normalized, with bounded constructible finite-Tor levels.
In particular its comparison domain holds; no common interval is used.
(3) The preceding invertibility theorem fixes both inverse refinement mates.
(4) Apply lem-pur-system-clopen-tensor-compatibility to (j1,j2,id_X,u), H=M and
Q=P_p2 N. The identity-edge comparison and projection are their canonical units.
Compactification opens are quasi-compact; the compactification schemes are separated
finite-type over k. The result is gamma_T d2 = R_u(d1) pi_u (gamma_M tensor 1).
(5) Transpose the projection-composition equation under P_u P_p2 adjoint to R_p2 R_u.
On both sides the counit is P_u(epsilon_p2) followed by epsilon_u; tensor-pullback
composition and mate pasting identify the transposes. Thus c_T pi_p1 equals
R_p2(pi_u) pi_p2 (c_M tensor 1), with the canonical pullback identifications.
(6) Invert gamma in (4), apply R_p2 and substitute (5). Naturality of projection
moves gamma_M inverse through pi_p2. The resulting two words are exactly the
maps in the conclusion. All calculations take place in the derived category of
systems, without evaluation detecting equality or inverse limits. -/
theorem system_compactification_pf_substitution
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : D l E X) (N : D l E Y)
    (hM : refinementNormalizedCtf o X M) (hN : refinementNormalizedCtf o Y N) :
    ∃ hT : refinementDomain X ((o.T X).obj (M, (o.P f).obj N)),
      refinementPF o c₁ M N ≫
          (refinementTheta o K hl r ((o.T X).obj (M, (o.P f).obj N)) hT).hom =
        (o.T Y).map (Prod.mkHom
          (refinementTheta o K hl r M (fun n ↦ (hM.2 n).1)).hom (𝟙 N)) ≫
          refinementPF o c₂ M N := by
  sorry

/-- A common-refinement comparison is the specified inverse-forward pair of comparisons.
Source: Stacks 0F7J, 0ATU
(blueprint: lem-pur-system-compactification-pf-substitution). -/
def refinementSpanComparison {c₁ c₂ d : Compactification f}
    (a : d.Refinement c₁) (b : d.Refinement c₂) (M : D l E X)
    (hM : refinementDomain X M) :
    (refinementImage o c₁).obj M ≅ (refinementImage o c₂).obj M :=
  (refinementTheta o K hl a M hM).symm ≪≫ refinementTheta o K hl b M hM

/-- Identity, composition, common-refinement independence and the comparison cocycle
on the full levelwise bounded constructible domain, before evaluation.
Source: Stacks 0F7C, 0F7J and 0ATU
(blueprint: lem-pur-system-compactification-pf-substitution).
Proof: (7) Varying-ring vertical pasting gives c_v,u gamma_vu = R_v(gamma_u) gamma_v.
Invert it on the domain established by refinementGamma_isIso. Associativity of the
canonical direct-image compositors and their naturality with gamma_u inverse rewrite
theta_vu as theta_u followed by theta_v. Identity squares and unital compositors give
theta_id = id. These statements concern actual system transformations.
(8) For parallel refinements a,b, lem-cbc-compactifiable-cofiltered supplies e with
ae=be. Composition gives theta_a theta_e = theta_b theta_e; cancel the invertible
theta_e. Existence of common objects alone would not justify this step.
(9) Two common spans have a common refinement. Apply (8) to the two resulting
arrows to each endpoint, then (7), and cancel the comparison of the common object.
This proves independence of the object and of both arrows. For three endpoint
compactifications take a common refinement and cancel the middle inverse-forward
pair. The resulting equality is the cocycle for any three chosen spans. No
cohomological or Tor bounds uniform in the coefficient index are imposed. -/
theorem system_compactification_refinement_coherence :
    (∀ (c : Compactification f) (M : D l E X) (hM : refinementDomain X M),
      refinementTheta o K hl (Compactification.Refinement.id c) M hM =
        Iso.refl ((refinementImage o c).obj M)) ∧
    (∀ (c₁ c₂ c₃ : Compactification f) (r : c₁.Refinement c₂) (s : c₂.Refinement c₃)
      (M : D l E X) (hM : refinementDomain X M),
      refinementTheta o K hl (r.comp s) M hM =
        refinementTheta o K hl r M hM ≪≫ refinementTheta o K hl s M hM) ∧
    (∀ (c₁ c₂ d d' : Compactification f)
      (a : d.Refinement c₁) (b : d.Refinement c₂)
      (a' : d'.Refinement c₁) (b' : d'.Refinement c₂)
      (M : D l E X) (hM : refinementDomain X M),
      refinementSpanComparison o K hl a b M hM =
        refinementSpanComparison o K hl a' b' M hM) ∧
    (∀ (c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f)
      (a₁₂ : d₁₂.Refinement c₁) (b₁₂ : d₁₂.Refinement c₂)
      (a₂₃ : d₂₃.Refinement c₂) (b₂₃ : d₂₃.Refinement c₃)
      (a₁₃ : d₁₃.Refinement c₁) (b₁₃ : d₁₃.Refinement c₃)
      (M : D l E X) (hM : refinementDomain X M),
      refinementSpanComparison o K hl a₁₂ b₁₂ M hM ≪≫
          refinementSpanComparison o K hl a₂₃ b₂₃ M hM =
        refinementSpanComparison o K hl a₁₃ b₁₃ M hM) := by
  sorry

end Geometry
end WeilConjectures.SystemTensorMate
