/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Compactification.Defs
import WeilConjectures.DeligneLaumon.WeilIndProperOpenHigher
import WeilConjectures.DeligneLaumon.WeilIndOpenRealization
import WeilConjectures.DeligneLaumon.WeilIndProperHigherRealization
import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.DeligneLaumon.WeilIndOpenRepresentability
import WeilConjectures.DeligneLaumon.WeilIndProperHigherRepresentability
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Higher compact-support images in the actual common-stage Weil heart

Source: blueprint main-20261015, sec-deligne-laumon-general,
sk-l-dl-general-composition, lem-zl-composition-weight-bound.proof.md,
first paragraph; SGA 4, XVII, §5--6; Bhatt--Scholze 6.7.6--6.7.7
(blueprint: def-zl-weil-compact-support-cohomology).

Extend by zero first, and then derive the proper direct image in the ambient
category of all equivariant ind-sheaves. Representability returns the result to
the existing common-stage Weil heart. This is an auxiliary resolution construction;
it does not replace the recorded category of Weil complexes.

## Main definitions

- `zlIndWeilHigherShriek`.
- `zlWeilHigherShriek`.
- `zlSourceWeilHeart`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The middle scheme of a compactification, with its inherited k₀-structure.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationMiddle {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ Y₀.hom)

/-- The middle scheme is finite type over k₀ because its proper map has that property.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: a proper map is finite type, and finite type is stable under composition. -/
@[instance]
theorem zlCompactificationMiddle_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    LocallyOfFiniteType (zlCompactificationMiddle D f₀ c).hom := by
  change LocallyOfFiniteType (c.g ≫ Y₀.hom)
  infer_instance

/-- The middle scheme is quasi-compact over k₀ by properness and composition.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: proper morphisms are quasi-compact, as are their composites. -/
@[instance]
theorem zlCompactificationMiddle_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    QuasiCompact (zlCompactificationMiddle D f₀ c).hom := by
  change QuasiCompact (c.g ≫ Y₀.hom)
  infer_instance

/-- The open part, over k₀, of the given compactification.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: the equality f₀.left = c.i ≫ c.g and f₀.w show the structure-map equality. -/
theorem zlCompactificationOpen_w {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    c.i ≫ (zlCompactificationMiddle D f₀ c).hom = X₀.hom := by
  change c.i ≫ (c.g ≫ Y₀.hom) = X₀.hom
  rw [← Category.assoc, ← c.comm]
  exact f₀.w

/-- The open part as an arrow of k₀-schemes.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationOpen {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    X₀ ⟶ zlCompactificationMiddle D f₀ c :=
  Over.homMk c.i (zlCompactificationOpen_w D f₀ c)

/-- The open part has its specified open-immersion property.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: its underlying map is c.i, an open immersion by the compactification data. -/
@[instance]
theorem zlCompactificationOpen_isOpenImmersion {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    IsOpenImmersion (zlCompactificationOpen D f₀ c).left := by
  change IsOpenImmersion c.i
  infer_instance

/-- The proper part as an arrow of k₀-schemes.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationProper {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    zlCompactificationMiddle D f₀ c ⟶ Y₀ :=
  Over.homMk c.g

/-- The actual ind-object Rⁿp_*j!F. Only the proper direct image is derived;
Rf! is not defined as the right derived functor of ordinary f!.
Source: SGA 4, XVII, §5--6; blueprint composition proof, first paragraph
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlIndWeilHigherShriek {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) (n : ℕ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) : zlIndWeilHeart D l hl Ω Y₀ :=
  ((zlIndWeilPush D l hl Ω (zlCompactificationProper D f₀ c)).rightDerived n).obj
    ((zlIndWeilOpenShriek D l hl Ω (zlCompactificationOpen D f₀ c)).obj
      ((zlWeilIndEmbedding D l hl Ω X₀).obj F))

/-- Proper direct-image finiteness makes Rⁿp_*j!F representable by a constructible
Weil sheaf, inside the original common-stage heart.
Source: SGA 4, XVII, §5--6; blueprint composition proof, first paragraph
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: apply open-extension representability to the open leg, obtaining G and an
isomorphism from its embedding to j!F. Apply proper higher-image representability
to G and the proper leg, obtaining H. Map the first isomorphism by the n-th right
derived proper-image functor and compose it with the representation of H.
The two constituent results are isolated in their own statement modules; this is
a decomposition of the original argument, rather than a proof of its finiteness
and realization inputs. -/
theorem zlWeilHigherShriek_representable {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) (n : ℕ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ H : sfCommonStageWeilSheaf D l hl Y₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj H ≅
        zlIndWeilHigherShriek D l hl Ω f₀ c n F) := by
  obtain ⟨G, ⟨e⟩⟩ := zlIndWeilOpenShriek_representable D l hl Ω
    (zlCompactificationOpen D f₀ c) F
  let p₀ := zlCompactificationProper D f₀ c
  have : IsProper p₀.left := inferInstanceAs (IsProper c.g)
  obtain ⟨H, ⟨h⟩⟩ := zlIndWeilProperHigher_representable D l hl Ω p₀ n G
  exact ⟨H, ⟨h ≪≫ ((zlIndWeilPush D l hl Ω p₀).rightDerived n).mapIso e⟩⟩

/-- Higher compact-support image in the actual common-stage Weil heart. Selection
is along a fully faithful embedding, so it selects the unique representing object
up to the isomorphism used downstream, including the prescribed Weil action.
Source: SGA 4, XVII, §5--6; blueprint composition proof, first paragraph
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlWeilHigherShriek {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) (n : ℕ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) : sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  (zlWeilHigherShriek_representable D l hl Ω f₀ c n F).choose

/-- Compactification choices yield isomorphic higher images in the actual Weil heart.
Source: SGA 4, XVII, §5--6; blueprint compact-support construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: two compactifications admit a common proper refinement. Proper base change
identifies the two proper direct images after open extension, by the counit mates.
The comparison is natural and Frobenius-equivariant by normalization of the
pullback squares and mate pasting. Injective-resolution comparison carries it to
each higher image. Full faithfulness of zlWeilIndEmbedding lifts the resulting
isomorphism to the original heart. No compactification is selected arbitrarily. -/
theorem zlWeilHigherShriek_compactification_independent
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c c' : Compactification f₀.left) (n : ℕ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    Nonempty (zlWeilHigherShriek D l hl Ω f₀ c n F ≅
      zlWeilHigherShriek D l hl Ω f₀ c' n F) := by
  have : IsLocallyNoetherian X₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  have : CompactSpace X₀.left :=
    QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : IsNoetherian X₀.left := ⟨⟩
  have : QuasiCompact f₀.left := inferInstance
  obtain ⟨d, ⟨r⟩, ⟨r'⟩⟩ := Compactification.exists_common_refinement c c'
  have compare (a b : Compactification f₀.left) (s : a.Refinement b) :
      Nonempty (zlIndWeilHigherShriek D l hl Ω f₀ a n F ≅
        zlIndWeilHigherShriek D l hl Ω f₀ b n F) := by
    let q : zlCompactificationMiddle D f₀ a ⟶ zlCompactificationMiddle D f₀ b :=
      Over.homMk s.hom (by
        change s.hom ≫ (b.g ≫ Y₀.hom) = a.g ≫ Y₀.hom
        rw [← Category.assoc, s.hom_g])
    have : IsProper q.left := inferInstanceAs (IsProper s.hom)
    have : IsProper (zlCompactificationProper D f₀ a).left :=
      inferInstanceAs (IsProper a.g)
    have : IsProper (zlCompactificationProper D f₀ b).left :=
      inferInstanceAs (IsProper b.g)
    apply zlIndWeilProperOpenHigher D l hl Ω
      (zlCompactificationOpen D f₀ a) (zlCompactificationOpen D f₀ b)
      (zlCompactificationProper D f₀ a) (zlCompactificationProper D f₀ b) q
      ?_ ?_ n F
    · ext
      exact s.i_hom
    · ext
      exact s.hom_g
  obtain ⟨e⟩ := compare d c r
  obtain ⟨e'⟩ := compare d c' r'
  let E := zlWeilIndEmbedding D l hl Ω Y₀
  obtain ⟨h⟩ := (zlWeilHigherShriek_representable D l hl Ω f₀ c n F).choose_spec
  obtain ⟨h'⟩ := (zlWeilHigherShriek_representable D l hl Ω f₀ c' n F).choose_spec
  obtain ⟨hfull, hfaith⟩ := zlWeilIndEmbedding_full_faithful D l hl Ω Y₀
  let : E.Full := hfull
  let : E.Faithful := hfaith
  exact ⟨E.preimageIso (h ≪≫ e.symm ≪≫ e' ≪≫ h'.symm)⟩

/-- The geometric fibre has its specified structure over the chosen algebraic closure.
Source: blueprint finite-field geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology). -/
instance zlGeometricFiberOver (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
  ⟨(D.geometricFiber X₀).hom⟩

/-- Finite type survives the defining geometric base change.
Source: Stacks 01T6; blueprint geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: the structure map is pullback.snd of X₀.hom, and locally finite type is
stable under base change. -/
@[instance]
theorem zlGeometricFiber_finiteType (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
  change LocallyOfFiniteType (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

/-- Quasi-compactness survives geometric base change.
Source: Stacks 01K0; blueprint geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: quasi-compactness is stable under base change, applied to X₀.hom. -/
@[instance]
theorem zlGeometricFiber_quasiCompact (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
  change QuasiCompact (pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

/-- The base-changed map respects the specified geometric structure maps.
Source: blueprint geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: this is the Over.w equation of the image of f₀ under Over.pullback. -/
@[instance]
theorem zlFiberMap_isOver {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlFiberMap D f₀).IsOver (Spec (.of D.k)) := by
  exact ⟨((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).w⟩

/-- Separatedness survives geometric base change.
Source: Stacks 01L4; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: the square of f₀ with its geometric-fibre map is Cartesian. Base change
preserves closed diagonals, which characterize separatedness. -/
@[instance]
theorem zlFiberMap_separated {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] : IsSeparated (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsSeparated)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Local finite type survives geometric base change.
Source: Stacks 01T6; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: f₀.left and zlFiberMap D f₀ form the base-change square of the two
structure-map pullbacks. Apply locally finite type stability under base change. -/
@[instance]
theorem zlFiberMap_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Quasi-compactness survives geometric base change.
Source: Stacks 01K0; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: use the same Cartesian square and quasi-compact base-change stability. -/
@[instance]
theorem zlFiberMap_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] : QuasiCompact (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @QuasiCompact)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

include hl in
/-- The coefficient prime is a unit in the closure field itself.
Source: blueprint finite-field coefficient convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: D.card_base and D.cardinality_eq give characteristic D.p in D.k₀ and
hence D.k. The prime l differs from D.p, so its image in that field is nonzero,
and therefore invertible. -/
theorem zlClosurePrimeUnit : IsUnit (l : D.k) := by
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
    (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)

/-- Equality transport of a recorded value keeps its chosen tower unchanged. -/
private theorem zlCompactSupportValue_copy
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [f'.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (c : Compactification f) (w : f' = f)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X) :
    sfQbarCompactSupportValue l D.k (zlClosurePrimeUnit D l hl) Ω (c.copy w) L K =
      sfQbarCompactSupportValue l D.k (zlClosurePrimeUnit D l hl) Ω c L K := by
  cases w
  rfl

/-- Comparison with the prescribed integral/rational/common-stage compact-support
value, on every integral representative and every geometric compactification.
Source: Bhatt--Scholze 6.7.6--6.7.7; SGA 4, XVII, §5--6; blueprint composition proof
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: represent the arithmetic open ind-extension by G and its n-th proper
ind-image by H. Open-only realization identifies the carrier of G with the
normalized coefficient action for (j,id); proper-only realization identifies
H.carrier with the n-th standard cohomology of the action for (id,p) on G.carrier.
The two representations and full faithfulness identify the originally chosen
higher shriek object with H as a Weil sheaf. Forget this isomorphism to carriers.
The geometric fibre maps compose by functoriality of Over.pullback. The existing
normalized coefficient compositor therefore identifies the successive open and
proper actions with the action for the specified geometric compactification.
Map the given integral-model isomorphism, then apply the coefficient action's
literal value equation. Standard cohomology maps this composite isomorphism to
the requested target. The two realization inputs are separate source results;
their existence is not asserted by the bare representability conclusions. -/
theorem zlWeilHigherShriek_compactSupportComparison
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c : Compactification f₀.left) (cg : Compactification (zlFiberMap D f₀))
    (n : ℕ) (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left)
    (_e : F.obj.carrier ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
      ((sfRationalConstructibleLocalization l _ (D.geometricFiber X₀).left).obj K)) :
    Nonempty ((zlWeilHigherShriek D l hl Ω f₀ c n F).obj.carrier ≅
      (constructibleTruncationCohomology
        (sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl) (n : ℤ)).obj
          (sfQbarCompactSupportValue l
            (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
            (f := zlFiberMap D f₀) D.k (zlClosurePrimeUnit D l hl) Ω cg L K)) := by
  have : IsLocallyNoetherian X₀.left :=
    LocallyOfFiniteType.isLocallyNoetherian X₀.hom
  have : CompactSpace X₀.left :=
    QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : IsNoetherian X₀.left := ⟨⟩
  let j₀ := zlCompactificationOpen D f₀ c
  have : QuasiCompact j₀.left := inferInstance
  let p₀ := zlCompactificationProper D f₀ c
  have : IsProper p₀.left := inferInstanceAs (IsProper c.g)
  have w : zlFiberMap D j₀ ≫ zlFiberMap D p₀ = zlFiberMap D f₀ := by
    let B := Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    have h : j₀ ≫ p₀ = f₀ := by
      apply Over.OverMorphism.ext
      exact c.comm.symm
    exact (congrArg (fun h ↦ h.left) (B.map_comp j₀ p₀)).symm.trans
      (congrArg (fun h ↦ (B.map h).left) h)
  let cj := Compactification.ofIsOpenImmersion (zlFiberMap D j₀)
  let cp := Compactification.ofIsProper (zlFiberMap D p₀)
  let cfg := cg.copy w
  obtain ⟨Sj, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (zlClosurePrimeUnit D l hl) Ω cj
  obtain ⟨Sp, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (zlClosurePrimeUnit D l hl) Ω cp
  obtain ⟨Sfg, _⟩ := sfCompactSupportFiniteFieldIndependence l D.k
    (zlClosurePrimeUnit D l hl) Ω cfg
  obtain ⟨G, ⟨eG⟩⟩ := zlIndWeilOpenShriek_representable D l hl Ω j₀ F
  obtain ⟨g⟩ := zlIndWeilOpenShriek_realization D l hl Ω j₀ Sj F G eG
  obtain ⟨H, ⟨eH⟩⟩ := zlIndWeilProperHigher_representable D l hl Ω p₀ n G
  obtain ⟨h⟩ := zlIndWeilProperHigher_realization D l hl Ω p₀ Sp n G H eH
  let E := zlWeilIndEmbedding D l hl Ω Y₀
  obtain ⟨hfull, hfaith⟩ := zlWeilIndEmbedding_full_faithful D l hl Ω Y₀
  let : E.Full := hfull
  let : E.Faithful := hfaith
  obtain ⟨eR⟩ := (zlWeilHigherShriek_representable D l hl Ω f₀ c n F).choose_spec
  let hH : zlWeilHigherShriek D l hl Ω f₀ c n F ≅ H :=
    E.preimageIso (eR ≪≫
      (((zlIndWeilPush D l hl Ω p₀).rightDerived n).mapIso eG).symm ≪≫ eH.symm)
  let U := ((sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω).inverseImage
    (sfCommonStageWeilForget D l hl Y₀ Ω)).ι
  let q := (sfCommonStageWeilForget D l hl Y₀ Ω).mapIso (U.mapIso hH)
  obtain ⟨γ, _⟩ := (sfFieldShriekCompositionQbar_existsUnique D l hl cj cp cfg Ω
    Sj Sp Sfg).exists
  let C := constructibleTruncationCohomology
    (sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl) (n : ℤ)
  let output := Sp.system.functor.mapIso g ≪≫ γ.app F.obj.carrier ≪≫
    Sfg.system.functor.mapIso _e ≪≫ eqToIso (Sfg.value_eq _) ≪≫
      eqToIso (zlCompactSupportValue_copy D l hl Ω cg w L K)
  exact ⟨q ≪≫ h ≪≫ C.mapIso output⟩

/-- A finite-type map to a finite-type k₀-scheme has finite-type source.
Source: blueprint Leray proof, source-domain check
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: f₀.w identifies the source structure map with f₀.left followed by the
target structure map. Apply stability of locally finite type under composition. -/
theorem zlSource_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType X₀.hom := by
  rw [← f₀.w]
  infer_instance

/-- The finite-type source also has quasi-compact structure map.
Source: blueprint Leray proof, source-domain check
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: use f₀.w and composition of the two quasi-compact maps. -/
theorem zlSource_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] :
    QuasiCompact X₀.hom := by
  rw [← f₀.w]
  infer_instance

/-- The source Weil heart with its induced finite-type instances. This packages
consequences of the hypotheses and adds no source hypothesis to the Leray statement.
Source: blueprint Leray proof, source-domain check
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlSourceWeilHeart {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :=
  letI := zlSource_finiteType D f₀
  letI := zlSource_quasiCompact D f₀
  sfCommonStageWeilSheaf D l hl X₀ Ω

/-- Source presentation of the same canonical higher image.
Source: blueprint Leray proof, first paragraph
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlSourceHigherShriek {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c : Compactification f₀.left) (n : ℕ) (F : zlSourceWeilHeart D l hl Ω f₀) :
    sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  letI := zlSource_finiteType D f₀
  letI := zlSource_quasiCompact D f₀
  zlWeilHigherShriek D l hl Ω f₀ c n F

/-- The composite higher image, with source instances inherited from the first map.
Source: blueprint Leray proof, first paragraph
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompositeHigherShriek {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    (g₀ : Z₀ ⟶ Y₀) (c : Compactification (h₀ ≫ g₀).left) (n : ℕ)
    (F : zlSourceWeilHeart D l hl Ω h₀) : sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  letI := zlSource_finiteType D h₀
  letI := zlSource_quasiCompact D h₀
  zlWeilHigherShriek D l hl Ω (h₀ ≫ g₀) c n F

end WeilConjectures
