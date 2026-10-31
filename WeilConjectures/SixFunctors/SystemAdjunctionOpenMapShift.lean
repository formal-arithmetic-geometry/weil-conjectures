/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SystemPrimitiveComparisonShift
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionUnitShift
import WeilConjectures.AlgebraicGeometry.PurReductionLimitShiftAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Intrinsic shift squares for system adjunctions and normalized open maps

Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
maps-used and coefficient-comparison sentences; extracted obligation, not a shift
assertion quoted from that text (blueprint: lem-pur-system-adjunction-open-map-shift).

The indices below select the listed maps and actual adjunctions. They introduce no
new system, tensor, reconstruction functor, open comparison or shift normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- All intermediate systems in a designated slot, including its fixed tensor operands,
belong to the published normalized bounded domain. Source: fix-prop-coherence, stated
 domains (blueprint: lem-pur-system-adjunction-open-map-shift). -/
def systemShiftContextDomain {B : Scheme.{u}} (o : Operations l E) {A : Over B} :
    {W : Over B} → Expression.SlotContext (systemInterpretation l E o) A W →
      System l E A.left → Prop
  | W, e, M => Good l E W.left (e.evaluate.obj M) ∧
    match e with
    | .input => True
    | .pull _ e => systemShiftContextDomain o e M
    | .push _ _ e => systemShiftContextDomain o e M
    | .shriek _ _ _ e => systemShiftContextDomain o e M
    | .compactSupport _ c e => systemShiftContextDomain o e M ∧
      Good l E c.Z ((Operations.shriek l E o c.i).obj (e.evaluate.obj M))
    | .tensorLeft e N => systemShiftContextDomain o e M ∧ Good l E _ N
    | .tensorRight N e => Good l E _ N ∧ systemShiftContextDomain o e M

/-- Precisely the system generators in G and the two normalized open maps, with
inverses. Tensor constructors distinguish the two signed occurrences.
Source: fix-prop-coherence, maps-used; Stacks 0GL1, 0E8I
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
inductive SystemAdjunctionOpenGenerator (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) :
    {A W : PrimitiveSystemScheme D} →
    (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj) →
    (∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M) → Prop where
  | primitive {A W : PrimitiveSystemScheme D}
      (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj)
      (τ : ∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M)
      (h : PrimitiveSystemComparison l E D o c a e t τ) :
      SystemAdjunctionOpenGenerator D o c a e t τ
  | pushComp {U V W : PrimitiveSystemScheme D} (f : U.obj ⟶ V.obj)
      (g : V.obj ⟶ W.obj) (hf : IsProper f.left) (hg : IsProper g.left)
      (hfg : IsProper (f ≫ g).left) :
      SystemAdjunctionOpenGenerator D o c a (.push g hg (.push f hf .input))
        (.push (f ≫ g) hfg .input) (fun M ↦ (c.pushComp l E f.left g.left).hom.app M)
  | beta {U' U X' X : PrimitiveSystemScheme D}
      (v : U'.obj ⟶ U.obj) (j' : U'.obj ⟶ X'.obj)
      (j : U.obj ⟶ X.obj) (g : X'.obj ⟶ X.obj)
      [hj : IsOpenImmersion j.left] [hj' : IsOpenImmersion j'.left]
      (qj : QuasiCompact j.left) (qj' : QuasiCompact j'.left)
      (_hv : PrimitiveSystemArrow v) (_hg : PrimitiveSystemArrow g)
      (w : v.left ≫ j.left = j'.left ≫ g.left)
      (sq : IsPullback v.left j'.left j.left g.left) :
      SystemAdjunctionOpenGenerator D o c a (.pull g (.shriek j hj qj .input))
        (.shriek j' hj' qj' (.pull v .input))
        (fun M ↦ (a.beta v.left j'.left j.left g.left w sq).hom.app M)
  | tensorLeft {U X : PrimitiveSystemScheme D} (j : U.obj ⟶ X.obj)
      [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (N : System l E X.obj.left) :
      SystemAdjunctionOpenGenerator D o c a (.tensorLeft (.shriek j hj qj .input) N)
        (.shriek j hj qj (.tensorLeft .input ((pull l E j.left).obj N)))
        (fun M ↦ (a.projection j.left).hom.app (M, N))
  | tensorRight {U X : PrimitiveSystemScheme D} (j : U.obj ⟶ X.obj)
      [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (M : System l E U.obj.left) :
      SystemAdjunctionOpenGenerator D o c a
        (.tensorRight ((Operations.shriek l E o j.left).obj M) .input)
        (.shriek j hj qj (.tensorRight M (.pull j .input)))
        (fun N ↦ (a.projection j.left).hom.app (M, N))
  | inverse {A W : PrimitiveSystemScheme D}
      (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj)
      (τ : ∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M)
      [∀ M : System l E A.obj.left, IsIso (τ M)]
      (h : SystemAdjunctionOpenGenerator D o c a e t τ) :
      SystemAdjunctionOpenGenerator D o c a t e (fun M ↦ inv (τ M))

/-- The two kinds of endpoints of the listed actual adjunctions.
Source: fix-prop-coherence, coefficient comparison
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
inductive SystemShiftCorner (D : FiniteFieldDatum.{u}) where
  | system (W : PrimitiveSystemScheme D)
  | integral (W : PrimitiveSystemScheme D)

/-- The endpoint is the published ordinary unbounded derived category.
Source: Stacks 0941 (blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftCorner.category {D : FiniteFieldDatum.{u}} :
    SystemShiftCorner D → Type (u + 2)
  | .system W => System l E W.obj.left
  | .integral W => Integral l E W.obj.left

/-- The existing category structure, with no universe change or category replacement.
Source: Stacks 0941 (blueprint: lem-pur-system-adjunction-open-map-shift). -/
instance SystemShiftCorner.instCategory {D : FiniteFieldDatum.{u}} (A : SystemShiftCorner D) :
    Category.{u + 2} (A.category l E) := by
  cases A <;> dsimp [SystemShiftCorner.category] <;> infer_instance

/-- The existing integer shift on each actual endpoint.
Source: cochain conventions, Stacks 011G
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
instance SystemShiftCorner.instHasShift {D : FiniteFieldDatum.{u}} (A : SystemShiftCorner D) :
    HasShift (A.category l E) ℤ := by
  cases A <;> dsimp [SystemShiftCorner.category] <;> infer_instance

/-- The node's domain: normalized bounded constructible systems with compatible origins
and common finite Tor bounds, or derived-complete constructible integral inputs.
Source: fix-prop-coherence, stated domains
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftCorner.good {D : FiniteFieldDatum.{u}} :
    (A : SystemShiftCorner D) → ObjectProperty (A.category l E)
  | .system W => Good l E W.obj.left
  | .integral W => sfIntegralConstructible l E W.obj.left

/-- A functor between the specified endpoints equipped with its designated shift.
For H and T this is the fixed compatible shift in the node; for an adjoint it is
constructed below from the published operation-shift data.
Source: fix-prop-coherence, adjoint mates
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
structure SystemShiftFunctor {D : FiniteFieldDatum.{u}} (A B : SystemShiftCorner D) where
  functor : A.category l E ⥤ B.category l E
  commShift : functor.CommShift ℤ

/-- The actual commutation isomorphism, without a newly chosen comparison.
Source: Stacks 011G (blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftFunctor.shift {D : FiniteFieldDatum.{u}} {A B : SystemShiftCorner D}
    (F : SystemShiftFunctor l E A B) (r : ℤ) :
    shiftFunctor (A.category l E) r ⋙ F.functor ≅
      F.functor ⋙ shiftFunctor (B.category l E) r :=
  Functor.commShiftIso F.functor (self := F.commShift) r

/-- Identity with its canonical shift.
Source: Stacks 011G (blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftFunctor.id {D : FiniteFieldDatum.{u}} (A : SystemShiftCorner D) :
    SystemShiftFunctor l E A A := ⟨𝟭 _, inferInstance⟩

/-- Composite with the prescribed composite shift.
Source: Mathlib Shift.CommShift, composite convention
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftFunctor.comp {D : FiniteFieldDatum.{u}} {A B C : SystemShiftCorner D}
    (F : SystemShiftFunctor l E A B) (G : SystemShiftFunctor l E B C) :
    SystemShiftFunctor l E A C :=
  letI := F.commShift
  letI := G.commShift
  ⟨F.functor ⋙ G.functor, inferInstance⟩

/-- The component shift square for the actual maps, before finite evaluation.
Source: fix-prop-coherence, extracted shift obligation
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftFunctor.square {D : FiniteFieldDatum.{u}} {A B : SystemShiftCorner D}
    (F G : SystemShiftFunctor l E A B)
    (τ : ∀ M : A.category l E, F.functor.obj M ⟶ G.functor.obj M)
    (M : A.category l E) (r : ℤ) : Prop :=
  τ (M⟦r⟧) ≫ (G.shift l E r).hom.app M =
    (F.shift l E r).hom.app M ≫ (τ M)⟦r⟧'

/-- An actual adjunction together with the fixed shifts on its two functors.
This is only a container; it assumes no compatibility of unit or counit.
Source: fix-prop-coherence, maps-used
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
structure SystemShiftAdjunctionData (D : FiniteFieldDatum.{u}) where
  source : SystemShiftCorner D
  target : SystemShiftCorner D
  left : SystemShiftFunctor l E source target
  right : SystemShiftFunctor l E target source
  adjunction : left.functor ⊣ right.functor

/-- Exactly the three adjunction kinds named by the node, including nonproper
separated finite-type inverse image and proper direct image.
Source: fix-prop-coherence, maps-used
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
inductive SystemShiftAdjunction (D : FiniteFieldDatum.{u}) where
  | direct {U V : PrimitiveSystemScheme D} (f : U.obj ⟶ V.obj)
      (hf : PrimitiveSystemArrow f)
  | open {U V : PrimitiveSystemScheme D} (j : U.obj ⟶ V.obj)
      (hj : IsOpenImmersion j.left) (hq : QuasiCompact j.left)
  | reconstruction (W : PrimitiveSystemScheme D)

/-- The recorded adjunctions and operation shifts, retaining the actual Roos-normalized
limit and its reduction mate. Source: Stacks 0941 and fix-prop-coherence
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunction.data {D : FiniteFieldDatum.{u}} (o : Operations l E) :
    SystemShiftAdjunction D → SystemShiftAdjunctionData l E D
  | .direct (U := U) (V := V) f _ =>
    { source := .system V
      target := .system U
      left := ⟨pull l E f.left, systemPullShift l E f.left⟩
      right := ⟨Operations.push l E o f.left, systemPushShift l E o f.left⟩
      adjunction := (o.direct f.left).adj }
  | .open (U := U) (V := V) j hj _ =>
    letI := hj
    { source := .system U
      target := .system V
      left := ⟨Operations.shriek l E o j.left, systemOpenShift l E o j.left⟩
      right := ⟨pull l E j.left, systemPullShift l E j.left⟩
      adjunction := (o.extension j.left).adj }
  | .reconstruction W =>
    { source := .integral W
      target := .system W
      left := ⟨(calculus l E W.obj.left).reduction, reductionShift l E W.obj.left⟩
      right := ⟨coefficientSequenceLimit l E W.obj.left, limitShift l E W.obj.left⟩
      adjunction := (calculus l E W.obj.left).adjunction }

/-- The unit and counit equations on exactly the stated domains. Every object along
the respective two-operation path is required to be admissible.
Source: fix-prop-coherence, maps-used
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunctionData.unitCounit {D : FiniteFieldDatum.{u}}
    (a : SystemShiftAdjunctionData l E D) : Prop :=
  (∀ (M : a.source.category l E), a.source.good l E M →
    a.target.good l E (a.left.functor.obj M) →
    a.source.good l E (a.right.functor.obj (a.left.functor.obj M)) → ∀ r : ℤ,
    (SystemShiftFunctor.id l E a.source).square l E (a.left.comp l E a.right)
      (fun P ↦ a.adjunction.unit.app P) M r) ∧
  (∀ (M : a.target.category l E), a.target.good l E M →
    a.source.good l E (a.right.functor.obj M) →
    a.target.good l E (a.left.functor.obj (a.right.functor.obj M)) → ∀ r : ℤ,
    (a.right.comp l E a.left).square l E (SystemShiftFunctor.id l E a.target)
      (fun P ↦ a.adjunction.counit.app P) M r)

/-- The precise normalized-domain premise for a shift-compatible alpha:F2 H -> T F1.
Source: fix-prop-coherence, adjoint mates
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunctionData.alphaCompatible {D : FiniteFieldDatum.{u}}
    (a b : SystemShiftAdjunctionData l E D)
    (H : SystemShiftFunctor l E a.source b.source)
    (T : SystemShiftFunctor l E a.target b.target)
    (α : H.functor ⋙ b.left.functor ⟶ a.left.functor ⋙ T.functor) : Prop :=
  ∀ (M : a.source.category l E), a.source.good l E M →
    b.source.good l E (H.functor.obj M) →
    b.target.good l E (b.left.functor.obj (H.functor.obj M)) →
    a.target.good l E (a.left.functor.obj M) →
    b.target.good l E (T.functor.obj (a.left.functor.obj M)) → ∀ r : ℤ,
    (H.comp l E b.left).square l E (a.left.comp l E T) (fun P ↦ α.app P) M r

/-- Every intermediate of the displayed three-factor right mate is in its designated
normalized or integral domain. This imposes no preservation assertion on H or T.
Source: fix-prop-coherence, adjoint mates
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunctionData.mateDomain {D : FiniteFieldDatum.{u}}
    (a b : SystemShiftAdjunctionData l E D)
    (H : SystemShiftFunctor l E a.source b.source)
    (T : SystemShiftFunctor l E a.target b.target) (M : a.target.category l E) : Prop :=
  a.target.good l E M ∧
  a.source.good l E (a.right.functor.obj M) ∧
  b.source.good l E (H.functor.obj (a.right.functor.obj M)) ∧
  b.target.good l E (b.left.functor.obj (H.functor.obj (a.right.functor.obj M))) ∧
  b.source.good l E
    (b.right.functor.obj (b.left.functor.obj (H.functor.obj (a.right.functor.obj M)))) ∧
  a.target.good l E (a.left.functor.obj (a.right.functor.obj M)) ∧
  b.target.good l E (T.functor.obj (a.left.functor.obj (a.right.functor.obj M))) ∧
  b.source.good l E
    (b.right.functor.obj (T.functor.obj (a.left.functor.obj (a.right.functor.obj M)))) ∧
  b.target.good l E (T.functor.obj M) ∧
  b.source.good l E (b.right.functor.obj (T.functor.obj M))

/-- The right mate is the actual unit-alpha-counit composite, with the fixed shifts.
Source: fix-prop-coherence, adjoint mates
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunctionData.mates {D : FiniteFieldDatum.{u}}
    (a b : SystemShiftAdjunctionData l E D) : Prop :=
  ∀ (H : SystemShiftFunctor l E a.source b.source)
    (T : SystemShiftFunctor l E a.target b.target)
    (α : H.functor ⋙ b.left.functor ⟶ a.left.functor ⋙ T.functor),
    a.alphaCompatible l E b H T α → ∀ (M : a.target.category l E),
    a.mateDomain l E b H T M → ∀ r : ℤ,
    (a.right.comp l E H).square l E (T.comp l E b.right)
      (fun P ↦ b.adjunction.unit.app (H.functor.obj (a.right.functor.obj P)) ≫
        b.right.functor.map (α.app (a.right.functor.obj P)) ≫
        b.right.functor.map (T.functor.map (a.adjunction.counit.app P))) M r

/-- Both adjunct forms, on the domains of all the objects occurring in their
unit or counit formulas. H and T can hold any other tensor slot fixed.
Source: fix-prop-coherence, adjoint mates
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
def SystemShiftAdjunctionData.adjuncts {D : FiniteFieldDatum.{u}}
    (a : SystemShiftAdjunctionData l E D) : Prop :=
  (∀ (B : SystemShiftCorner D) (H : SystemShiftFunctor l E B a.source)
    (T : SystemShiftFunctor l E B a.target)
    (h : H.functor ⋙ a.left.functor ⟶ T.functor),
    (∀ (M : B.category l E), B.good l E M →
      a.source.good l E (H.functor.obj M) →
      a.target.good l E (a.left.functor.obj (H.functor.obj M)) →
      a.target.good l E (T.functor.obj M) → ∀ r : ℤ,
      (H.comp l E a.left).square l E T (fun P ↦ h.app P) M r) →
    ∀ (M : B.category l E), B.good l E M →
      a.source.good l E (H.functor.obj M) →
      a.target.good l E (a.left.functor.obj (H.functor.obj M)) →
      a.source.good l E (a.right.functor.obj (a.left.functor.obj (H.functor.obj M))) →
      a.target.good l E (T.functor.obj M) →
      a.source.good l E (a.right.functor.obj (T.functor.obj M)) → ∀ r : ℤ,
      H.square l E (T.comp l E a.right)
        (fun P ↦ a.adjunction.unit.app (H.functor.obj P) ≫
          a.right.functor.map (h.app P)) M r) ∧
  (∀ (B : SystemShiftCorner D) (H : SystemShiftFunctor l E B a.source)
    (T : SystemShiftFunctor l E B a.target)
    (h : H.functor ⟶ T.functor ⋙ a.right.functor),
    (∀ (M : B.category l E), B.good l E M →
      a.source.good l E (H.functor.obj M) →
      a.target.good l E (T.functor.obj M) →
      a.source.good l E (a.right.functor.obj (T.functor.obj M)) → ∀ r : ℤ,
      H.square l E (T.comp l E a.right) (fun P ↦ h.app P) M r) →
    ∀ (M : B.category l E), B.good l E M →
      a.source.good l E (H.functor.obj M) →
      a.target.good l E (a.left.functor.obj (H.functor.obj M)) →
      a.target.good l E (T.functor.obj M) →
      a.source.good l E (a.right.functor.obj (T.functor.obj M)) →
      a.target.good l E (a.left.functor.obj (a.right.functor.obj (T.functor.obj M))) →
      ∀ r : ℤ, (H.comp l E a.left).square l E T
        (fun P ↦ a.left.functor.map (h.app P) ≫
          a.adjunction.counit.app (T.functor.obj P)) M r)

/-- All clauses of the intrinsic system assertion. The generator index has no
proper/open interchange, projection mate, exchange or integral realization constructor.
The normalized open tensor map is included in both of its signed slots.
Source: fix-prop-coherence, maps-used and coefficient-comparison sentences
(blueprint: lem-pur-system-adjunction-open-map-shift). -/
structure SystemAdjunctionOpenShift (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) : Prop where
  generators : ∀ {A W : PrimitiveSystemScheme D}
    (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj)
    (τ : ∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M),
    SystemAdjunctionOpenGenerator l E D o c a e t τ →
    ∀ (M : System l E A.obj.left), systemShiftContextDomain l E o e M →
    systemShiftContextDomain l E o t M → ∀ r : ℤ,
    τ (M⟦r⟧) ≫ (t.shift (systemShifts l E o) r M).hom =
      (e.shift (systemShifts l E o) r M).hom ≫ (τ M)⟦r⟧'
  unitCounit : ∀ b : SystemShiftAdjunction D, (b.data l E o).unitCounit l E
  mates : ∀ b d : SystemShiftAdjunction D, (b.data l E o).mates l E (d.data l E o)
  adjuncts : ∀ b : SystemShiftAdjunction D, (b.data l E o).adjuncts l E
  inverses : ∀ {A B : SystemShiftCorner D} (F G : SystemShiftFunctor l E A B)
    (τ : F.functor ≅ G.functor) (M : A.category l E) (r : ℤ),
    A.good l E M → B.good l E (F.functor.obj M) → B.good l E (G.functor.obj M) →
    F.square l E G (fun P ↦ τ.hom.app P) M r →
    G.square l E F (fun P ↦ τ.inv.app P) M r

/-- The generator shift-square component of the system adjunction/open-map theorem.
This is the generator-by-generator calculation on the simultaneous system site,
including primitive, composition, base-change, tensor and inverse generators.
Source: fix-prop-coherence maps-used and coefficient-comparison sentences.
(blueprint: lem-pur-system-adjunction-open-map-shift) -/
theorem systemAdjunctionOpenMapShift_generators (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c) :
    ∀ {A W : PrimitiveSystemScheme D}
      (e t : Expression.SlotContext (systemInterpretation l E o) A.obj W.obj)
      (τ : ∀ M : System l E A.obj.left, e.evaluate.obj M ⟶ t.evaluate.obj M),
      SystemAdjunctionOpenGenerator l E D o c a e t τ →
      ∀ (M : System l E A.obj.left), systemShiftContextDomain l E o e M →
      systemShiftContextDomain l E o t M → ∀ r : ℤ,
      τ (M⟦r⟧) ≫ (t.shift (systemShifts l E o) r M).hom =
        (e.shift (systemShifts l E o) r M).hom ≫ (τ M)⟦r⟧' := by
  sorry

/-- The adjunction unit/counit, mate, and adjunct shift-square components.
Source: the exact-derived, reduction/limit, mate-transposition, and whiskering
calculations in the coefficient-comparison sentence.
(blueprint: lem-pur-system-adjunction-open-map-shift) -/
theorem systemAdjunctionOpenMapShift_adjunctionClauses
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (o : Operations l E)
    (c : Compositors l E o) (a : OpenComparisons l E o c) :
    ∀ b : SystemShiftAdjunction D,
      (b.data l E o).unitCounit l E ∧
      (∀ d : SystemShiftAdjunction D, (b.data l E o).mates l E (d.data l E o)) ∧
      (b.data l E o).adjuncts l E := by
  sorry

/-- The inverse-isomorphism shift-square component.
Source: cancellation in the shift square for an isomorphism.
(blueprint: lem-pur-system-adjunction-open-map-shift) -/
theorem systemAdjunctionOpenMapShift_inverses (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c) :
    ∀ {A B : SystemShiftCorner D} (F G : SystemShiftFunctor l E A B)
      (τ : F.functor ≅ G.functor) (M : A.category l E) (r : ℤ),
      A.good l E M → B.good l E (F.functor.obj M) →
      B.good l E (G.functor.obj M) →
      F.square l E G (fun P ↦ τ.hom.app P) M r →
      G.square l E F (fun P ↦ τ.inv.app P) M r := by
  sorry

/-- The listed canonical system maps, adjunctions, mates and normalized open maps
commute naturally with every integer shift, before evaluation of systems.
Source: blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
maps-used/coefficient-comparison sentences; agent-extracted obligation
(blueprint: lem-pur-system-adjunction-open-map-shift).

Proof plan, following all nine steps of the node:
1. Use the simultaneous ringed diagram models of
lem-sf-integral-compactification-system-realization and the fixed comparisons of
def-pur-integral-operation-shift-data. Apply
lem-pur-system-primitive-comparison-shift in each designated input occurrence.
2. For P_v adjoint to S_v, apply lem-weil-pbc-derived-adjunction-shift. Exact
inverse image identifies its K-flat comparison with the localized termwise one.
Adjunction shift uniqueness identifies the specified right-adjoint comparison.
For J_j adjoint to P_j, lem-pur-exact-adjunction-unit-shift-descent gives the
unit square of the degreewise adjunction. Its shifted degree-m component is the
same unit at M^(m+r), with differential sign (-1)^r. Adjunction compatibility
then gives the counit square for these same fixed comparisons.
3. Apply lem-pur-reduction-limit-shift-adjunction to the actual reconstruction
calculus. Its limit comparison uses the K-injective strict tower and signed Roos
cone; reductionShift is its left-adjoint mate. This gives both reconstruction
unit and counit equations without using faithfulness of finite evaluation.
4. Apply lem-weil-pbc-commshift-nattrans-comp-whisker for each integer r.
Composites and either whiskering retain their shift squares. Cancelling the
isomorphisms in a square gives the inverse square.
5. The right mate has exactly three factors: eta2 at H G1, G2(alpha at G1),
and G2(T epsilon1). Apply the unit, alpha, and counit squares and cancel the
intermediate comparisons. The two-factor calculation gives G(h) eta and
F(h) epsilon, respectively, using the unit and counit equations.
6. Direct-image compositors are the adjoint conjugates of pullback compositors.
Their composite adjunction unit and counit are composites of the original units
and counits. Apply steps 2, 4 and 5, and invert when necessary.
7. OpenTensorNormalization and OpenComparisons.beta_transpose identify beta^-1
with the open adjunct of P_gU(u_M) followed by the inverse pullback square.
The primitive square, unit square, whiskering and adjunct calculation give its
shift square; invert to obtain beta's square.
8. OpenComparisons.projection_transpose identifies gamma^-1 with the adjunct
of u_M tensor identity through the inverse restriction/tensor comparison.
Shift M and then, separately, N. Use naturality of the first tensor comparison
and of the signed second comparison. The factor (-1)^(ri) occurs on both routes.
Step 5 gives the adjunct square and step 4 gives the inverse square.
9. All comparisons are natural, all integers r were arbitrary, and every
calculation takes place in the original unbounded derived category of systems.
Restrict to the displayed normalized bounded domains; shifts translate the
common finite intervals and preserve their existence. No integral expression
realization, proper/open interchange, projection mate or exchange is used. -/
theorem systemAdjunctionOpenMapShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c) :
    SystemAdjunctionOpenShift l E D o c a := by
  have hA := systemAdjunctionOpenMapShift_adjunctionClauses l E D _hl o c a
  exact ⟨
    systemAdjunctionOpenMapShift_generators l E D _hl o c a,
    fun b ↦ (hA b).1,
    fun b d ↦ (hA b).2.1 d,
    fun b ↦ (hA b).2.2,
    systemAdjunctionOpenMapShift_inverses l E D _hl o c a⟩

end WeilConjectures.IntegralSystemRealization
