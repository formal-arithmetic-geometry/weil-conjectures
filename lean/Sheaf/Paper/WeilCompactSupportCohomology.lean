/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Compactification.Defs
import Mathlib.Algebra.CharP.CharAndCard

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
Proof:
1. Open extension is exact and preserves constructibility, so j!F is the image of a
   constructible Weil sheaf G = j!F on the middle scheme under the ind embedding.
2. The forgetful functor from Weil pairs to ind-objects is exact and preserves
   injectives: its left adjoint is the sum of the Frobenius iterates, which is exact
   because coproducts are exact in the Grothendieck ind-category. Direct image
   commutes with forgetting, so the underlying object of Rⁿp_*(G) is Rⁿ of the
   ind-extended heart direct image applied to G.
3. Identify the latter. The heart direct image of a constructible sheaf is H⁰(Rp_*),
   constructible because p is proper. The functor D^b(heart) → D^b_c realizing the
   standard t-structure is an equivalence on the finite-type geometric fibres
   (Beilinson, On the derived category of perverse sheaves, with the standard
   t-structure in place of the perverse one; Nori, Constructible sheaves), and
   D^b(heart) → D^b(Ind heart) is fully faithful (Kashiwara--Schapira, Categories
   and Sheaves, 15.3). Constructible sheaves have finite length, so the ind-category
   is locally noetherian and its derived direct image commutes with filtered
   colimits. Hence the right derived ind direct image, right adjoint to the exact
   ind inverse image, restricts on D^b(heart) to Rp_*, and its n-th cohomology of G
   is the ind embedding of Hⁿ(Rp_* j!F), a constructible heart object.
4. Proper pushforward commutes with finite coefficient extension, so this holds at
   every finite stage and descends to the common-stage heart.
5. The canonical mates defining the two adjunctions give its usual Weil action, and
   the step-2 comparison is equivariant. The fully faithful ind embedding determines
   the representing object, with its Frobenius structure, up to unique isomorphism
   compatible with its representation. -/
theorem zlWeilHigherShriek_representable {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) (n : ℕ)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ H : sfCommonStageWeilSheaf D l hl Y₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj H ≅
        zlIndWeilHigherShriek D l hl Ω f₀ c n F) := by
  sorry

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
  sorry

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

/-- Comparison with the prescribed integral/rational/common-stage compact-support
value, on every integral representative and every geometric compactification.
Source: Bhatt--Scholze 6.7.6--6.7.7; SGA 4, XVII, §5--6; blueprint composition proof
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: extend by zero before resolving for the proper direct image. By steps 2--3
of the proof of zlWeilHigherShriek_representable, the carrier is Hⁿ of Rp_* j!
applied to the underlying heart object, computed in the constructible derived
category. At each positive exponent the construction is the finite compactification
operation.
The coefficient action and its quotient maps are the canonical tensor-unit mates,
so the strict tower is sfCompactSupportTerm with sfCompactSupportTransition.
Exact products and derived completeness identify its inverse limit with the
integral compact-support value. Localize at the coefficient uniformizer and
include the finite stage; these are exactly sfQbarCompactSupportValue. Standard
t-exact coefficient change identifies the n-th heart object with the displayed
truncation cohomology. The free equivariant object is the sum of all Frobenius
iterates and is exact, so forgetting preserves injectives. Its mate equations
show that the induced action is precisely the natural Weil action of Rf!.
Common proper refinements identify the chosen geometric and arithmetic
compactifications. The normalized coefficient comparisons commute with all these
maps, so this argument applies to every integral model and every finite stage. -/
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
  sorry

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
