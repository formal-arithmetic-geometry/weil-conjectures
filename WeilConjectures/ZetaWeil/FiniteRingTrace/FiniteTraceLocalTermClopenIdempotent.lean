/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceLocalTerm
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceIntegrationComponentSum

/-! # The clopen idempotent and the cut integral, arbitrary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/sk-d-local-term/_section.md
(blueprint unit sk-d-local-term: the displayed clopen composite, "cuts out an idempotent" and
"which is `∫_B α|_B`"); DAG node lem-trf-local-term-clopen-idempotent.

The coefficient ring `A` is an arbitrary finite commutative ring killed by a positive power of
`ell`, exactly as in def-trf-local-term (`Sheaf.Paper.FiniteTraceLocalTerm`) below this module,
whose clopen piece `B = clopenPiece E U`, inclusion `j_B = clopenInclusion E U`, derived
pullback `Lj_B^* = clopenPullback`, extension-by-zero adjunction `Dj_{B!} ⊣ Lj_B^*`
(`clopenOpenAdjunction`), restricted section `α|_B = restrictSection` and integral
`∫ = sectionIntegral` are reused verbatim.

The ambient category `Ambient A E = D(Mod_{A_E})` is the derived category of module objects
over the pulled-back condensed coefficient ring (`ProEtale.CondensedRing`). The existing
`AlgebraicGeometry.ProEtale.clopenIdempotent`
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent`) is the same
composite on `D(Sheaf (X_proét) 𝒜)` for an abelian value category `𝒜`; that category is not
`Ambient A E`, so the composite is rebuilt here on module objects with the same three arrows
and the same shape (`clopenIdempotentNat` mirrors `clopenIdempotent`, the sheaf comparison
`clopenLowerShriekToLowerStar` mirrors `ProEtale.openImmersionLowerShriekToLowerStar`, and the
derived comparison `clopenDerivedComparison` mirrors `rightDerivedLowerStarIsoOfIsClosedRange`):
* `η`: the unit of the ordinary derived adjunction `Lj_B^* ⊣ Rj_{B*}`
  (`CondensedRing.derivedUpperStarLowerStarAdjunction`, def-weil-pbc-proetale-operations);
* the inverse of the comparison `Dj_{B!} ≅ Rj_{B*}` induced termwise by the sheaf comparison
  `j_{B!} → j_{B*}` of def-sfb-finite-lower-shriek-to-lower-star (the inverted counit of
  `j_B^* ⊣ j_{B*}` contracted with the counit of `j_{B!} ⊣ j_B^*`), followed by the identification
  of the exact `j_{B*}` with its total right derived functor;
* `ε`: the counit of `Dj_{B!} ⊣ Lj_B^*` (`clopenOpenAdjunction` of def-trf-local-term, the
  termwise sheaf counit of def-weil-open-closed-recollement transported along `Lj^* ≅ D(j^*)`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

attribute [local instance] vdDiscreteTopology tmDiscrete tmTopologicalRing tmCharPrime

section Geometry

variable {D : FiniteFieldDatum.{u}} (E : Over (Spec (.of D.k)))
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
  (U : E.left.Opens) [Fact (IsClopen (U : Set E.left))]

/-- The complementary open subset `E ∖ j_B(B)` of an open-and-closed `U`; its open subscheme
`V = clopenPiece E (clopenComplement E U)` has inclusion `j_V = clopenInclusion E _`.
Source: "let `j_V : V ↪ E` be the open immersion of the complementary open subscheme on
`E ∖ j_B(B)`" (blueprint: lem-trf-local-term-clopen-idempotent). -/
def clopenComplement : E.left.Opens :=
  ⟨(U : Set E.left)ᶜ, (Fact.out : IsClopen (U : Set E.left)).isClosed.isOpen_compl⟩

/-- The complement of an open-and-closed subset is open and closed.
Source: "the complementary open subscheme on `E ∖ j_B(B)`"
(blueprint: lem-trf-local-term-clopen-idempotent). -/
instance clopenComplement_clopen : Fact (IsClopen (clopenComplement E U : Set E.left)) :=
  ⟨(Fact.out : IsClopen (U : Set E.left)).compl⟩

/-- The empty open subset is open and closed (the case `B = ∅`).
Source: "In particular the integral is `0` when `B = ∅`"
(blueprint: lem-trf-local-term-clopen-idempotent). -/
instance bot_clopen : Fact (IsClopen ((⊥ : E.left.Opens) : Set E.left)) :=
  ⟨by rw [TopologicalSpace.Opens.coe_bot]; exact isClopen_empty⟩

/-- The whole space is open and closed (the case `B = E`).
Source: "and is `∫_E α` when `B = E`" (blueprint: lem-trf-local-term-clopen-idempotent). -/
instance top_clopen : Fact (IsClopen ((⊤ : E.left.Opens) : Set E.left)) :=
  ⟨by rw [TopologicalSpace.Opens.coe_top]; exact isClopen_univ⟩

/-- The open immersion `j_B` of an open-and-closed subset is also a closed immersion.
Source: "for the open immersion `j_B`, which is also a closed immersion
[def-weil-closed-immersion]" (blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 1): the underlying map of `j_B` is a homeomorphism onto the closed subset `U`;
on the open cover `U, Uᶜ` of `E` its structure-sheaf map is the identity, resp. the map to the
zero sheaf, hence surjective. This is def-weil-closed-immersion. -/
theorem clopenInclusion_isClosedImmersion : IsClosedImmersion (clopenInclusion E U).left := by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range (Subtype.val : U → E.left))
  rw [Subtype.range_val]
  exact (Fact.out : IsClopen (U : Set E.left)).isClosed

attribute [local instance] clopenInclusion_isClosedImmersion

/-- If `E` is proper over `s`, so is the open-and-closed piece `B`.
Source: "`B` and `V` are proper over `s` [lem-weil-pbc-closed-immersion-proper]"
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 1): `j_B` is a closed immersion (`clopenInclusion_isClosedImmersion`), hence
proper (lem-weil-pbc-closed-immersion-proper (a)); the composite `B → E → s` of proper
morphisms is proper (lem-weil-pbc-closed-immersion-proper (b)). -/
theorem clopenPiece_isProper [IsProper E.hom] : IsProper (clopenPiece E U).hom := by
  have : IsClosedImmersion U.ι := clopenInclusion_isClosedImmersion E U
  change IsProper (U.ι ≫ E.hom)
  infer_instance

/-- If `E` is proper over `s`, so is the complementary piece `V`.
Source: "`B` and `V` are proper over `s` [lem-weil-pbc-closed-immersion-proper]"
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 1): the identical check with `B, V` interchanged: `Uᶜ` is open and closed
(`clopenComplement_clopen`), so `clopenPiece_isProper` applies to it. -/
theorem clopenComplementPiece_isProper [IsProper E.hom] :
    IsProper (clopenPiece E (clopenComplement E U)).hom :=
  clopenPiece_isProper E (clopenComplement E U)

end Geometry

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

section Idempotent

variable {D} (E : Over (Spec (.of D.k)))
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
  (U : E.left.Opens) [Fact (IsClopen (U : Set E.left))]

attribute [local instance] clopenInclusion_isClosedImmersion

/-- The sheaf comparison `j_{B!} → j_{B*}` on module objects: `j_{B!}` of the inverted counit
of `j_B^* ⊣ j_{B*}` (invertible since `j_B` is a closed immersion,
`CondensedRing.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion`), followed by the
counit of `j_{B!} ⊣ j_B^*` at `j_{B*}`; this is the formula `v_M = ε_{GM} ∘ F(c_M^{-1})` of the
compactification `(j_B, id_E)`, the module-object form of
`ProEtale.openImmersionLowerShriekToLowerStar`.
Source: "the canonical comparison `j_{B!} ≃ Rj_{B*}` induced termwise by the sheaf comparison
`j_{B!} → j_{B*}` of [def-sfb-finite-lower-shriek-to-lower-star]"
(blueprint: lem-trf-local-term-clopen-idempotent). -/
def clopenLowerShriekToLowerStar :
    ((clopenInclusion E U).left)_!open⟦coefficient A⟧ ⟶
      ((clopenInclusion E U).left)_*⟦coefficient A⟧ :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (inv (CondensedRing.upperStarLowerStarAdjunction (coefficient A)
        (clopenInclusion E U).left).counit)
      ((clopenInclusion E U).left)_!open⟦coefficient A⟧ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((clopenInclusion E U).left)_*⟦coefficient A⟧
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficient A)
        (clopenInclusion E U).left).counit ≫
    (Functor.rightUnitor _).hom

omit [Finite A] in
private theorem clopenOpenCounit_isIso
    (N : Mod (Sheaf (Scheme.ProEt.topology (clopenPiece E U).left) Ab.{u + 1})
      (condensedRingObj (coefficient A) (clopenPiece E U).left)) :
    IsIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction (coefficient A)
      (clopenInclusion E U).left).counit.app
        (((clopenInclusion E U).left)_*⟦coefficient A⟧.obj N)) := by
  let j := (clopenInclusion E U).left
  have hc : IsClosed (Set.range j.base) := j.isClosedEmbedding.isClosed_range
  have := ProEtale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    Ab.{u + 1} j hc
  apply (Adjunction.isIso_counit_app_iff_mem_essImage _).2
  apply mem_essImage_openImmersionLowerShriek_of_mem_essImage
  exact ⟨N.X, ⟨asIso ((ProEtale.openImmersionLowerShriekToLowerStar Ab.{u + 1} j).app N.X)⟩⟩

set_option maxHeartbeats 1600000 in
-- Converting the module adjunction and its functor unitors needs a larger kernel budget.
/-- The sheaf comparison `j_{B!} → j_{B*}` is an isomorphism, since the image of `j_B` is closed.
Source: "(an isomorphism by [sk-def-sfb-finite-lower-shriek])"
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 2): the abelian-sheaf comparison is invertible for the clopen inclusion,
so the underlying sheaf of each direct-image module lies in the essential image of extension
by zero. The module essential-image theorem lifts this property to module objects. The open
adjunction counit at that module is therefore invertible. The other factor of the specified
comparison is extension by zero applied to the inverse of the ordinary counit, hence is
invertible as well. -/
theorem isIso_clopenLowerShriekToLowerStar : IsIso (clopenLowerShriekToLowerStar A E U) := by
  have : ∀ N, IsIso ((clopenLowerShriekToLowerStar A E U).app N) := by
    intro N
    have : IsIso (CondensedRing.upperStarLowerStarAdjunction (coefficient A)
        (clopenInclusion E U).left).counit :=
      CondensedRing.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion _ _
    dsimp only [clopenLowerShriekToLowerStar]
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' (clopenOpenCounit_isIso A E U N) ?_)
    · exact CategoryTheory.Functor.map_isIso _ _
    · exact IsIso.id _
  exact NatIso.isIso_of_isIso_app _

attribute [local instance] isIso_clopenLowerShriekToLowerStar

/-- `j_{B*}` on module objects is right exact, being isomorphic to the left adjoint `j_{B!}`.
Source: "and `G` since its sheaf functor is isomorphic to `F`"
(blueprint: lem-trf-local-term-clopen-idempotent, Step 2).
Proof: `preservesFiniteColimits_of_natIso (asIso (clopenLowerShriekToLowerStar A E U))` from
`CondensedRing.preservesFiniteColimits_openImmersionLowerShriek`. -/
theorem clopenLowerStar_preservesFiniteColimits :
    PreservesFiniteColimits ((clopenInclusion E U).left)_*⟦coefficient A⟧ := by
  exact preservesFiniteColimits_of_natIso (asIso (clopenLowerShriekToLowerStar A E U))

attribute [local instance] clopenLowerStar_preservesFiniteColimits

/-- The canonical derived comparison `Dj_{B!} ≅ Rj_{B*}`: the sheaf comparison
`clopenLowerShriekToLowerStar` applied termwise, followed by the inverse of the identification
of the exact `j_{B*}` with its total right derived functor
(`Functor.rightDerivedFunctorIsoMapDerivedCategory`). Module-object form of
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarIsoOfIsClosedRange` (inverted).
Source: "the inverse of the canonical comparison `j_{B!} ≃ Rj_{B*}` induced termwise by the
sheaf comparison `j_{B!} → j_{B*}`" (blueprint: lem-trf-local-term-clopen-idempotent). -/
def clopenDerivedComparison :
    D(((clopenInclusion E U).left)_!open⟦coefficient A⟧) ≅
      ((clopenInclusion E U).left)_*⟦coefficient A⟧.rightDerivedFunctor :=
  Functor.mapDerivedCategoryNatIso (asIso (clopenLowerShriekToLowerStar A E U)) ≪≫
    ((clopenInclusion E U).left)_*⟦coefficient A⟧.rightDerivedFunctorIsoMapDerivedCategory.symm

/-- The clopen projector `e_B : 𝟭 ⟶ 𝟭` of `D(E, A)`: the unit of `Lj_B^* ⊣ Rj_{B*}`, the inverse
of the comparison `Dj_{B!} ≅ Rj_{B*}` (whiskered by `Lj_B^*`) and the counit of
`Dj_{B!} ⊣ Lj_B^*`. Module-object form of `AlgebraicGeometry.ProEtale.clopenIdempotent`.
Source: "`e_B : A_E → Rj_{B*}j_B^*A_E ≃ j_{B!}j_B^*A_E → A_E` be the composite of the unit of
the ordinary adjunction `j_B^* ⊣ Rj_{B*}` ..., the inverse of the canonical comparison
`j_{B!} ≃ Rj_{B*}` ..., and the counit of the extension-by-zero adjunction `j_{B!} ⊣ j_B^*`"
(blueprint: lem-trf-local-term-clopen-idempotent). -/
def clopenIdempotentNat : 𝟭 (Ambient A E.left) ⟶ 𝟭 (Ambient A E.left) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A)
      (clopenInclusion E U).left).unit ≫
    Functor.whiskerLeft (clopenPullback A E U) (clopenDerivedComparison A E U).inv ≫
    (clopenOpenAdjunction A E U).counit

/-- The clopen idempotent `e_B : A_E → A_E` in `End_{D(E,A)}(A_E)`: the component of
`clopenIdempotentNat` at the constant coefficient object `A_E = 𝟙_`.
Source: "`e_B : A_E →^{η_{j_B}} Rj_{B*}j_B^*A_E →^{∼} j_{B!}j_B^*A_E →^{ε_{j_B}} A_E`"
(blueprint: lem-trf-local-term-clopen-idempotent). -/
def clopenIdempotent : 𝟙_ (Ambient A E.left) ⟶ 𝟙_ (Ambient A E.left) :=
  (clopenIdempotentNat A E U).app (𝟙_ (Ambient A E.left))

/-- Clause 2, first half: under `Lj_B^* A_E ≅ A_B`, `j_B^* e_B = id_{A_B}`.
Source: "2. Under the constant-coefficient identifications `j_B^*A_E ≃ A_B` and
`j_V^*A_E ≃ A_V`, one has `j_B^*e_B = id_{A_B}`" (blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 4): by the normalization `L(v_{LK}⁻¹) = u_{LK} ∘ c_{LK}` and the triangle
identity `c_{LK} ∘ L(η_K) = 1`, `L(q_K) = u_{LK}`; the open triangle identity gives
`L(ε_K) = u_{LK}⁻¹`, so `L(e_B) = 1`; conjugating by the constant identification gives `𝟙`. -/
theorem clopenIdempotent_restrict_self :
    (CondensedRing.leftDerivedUpperStarUnitIso (coefficient A) (clopenInclusion E U).left).inv ≫
        (clopenPullback A E U).map (clopenIdempotent A E U) ≫
        (CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
          (clopenInclusion E U).left).hom =
      𝟙 _ := by
  sorry

/-- Clause 1: `e_B ∘ e_B = e_B` in `End_{D(E,A)}(A_E)`.
Source: "1. `e_B ∘ e_B = e_B` in `End_{D(E,A)}(A_E)`."
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 3): cancel the constant-coefficient isomorphism in
`clopenIdempotent_restrict_self` to obtain `L(e_B) = 1`. Naturality of the open adjunction
counit gives `F(L(e_B)) ≫ ε = ε ≫ e_B`, hence `ε ≫ e_B = ε`. Since the displayed projector
factors as `q ≫ ε`, associativity gives `e_B ≫ e_B = q ≫ ε ≫ e_B = q ≫ ε = e_B`. -/
theorem clopenIdempotent_comp_self :
    clopenIdempotent A E U ≫ clopenIdempotent A E U = clopenIdempotent A E U := by
  let L := clopenPullback A E U
  let e := clopenIdempotent A E U
  let ε := (clopenOpenAdjunction A E U).counit.app (𝟙_ (Ambient A E.left))
  let i := CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
    (clopenInclusion E U).left
  have hL : L.map e = 𝟙 _ := by
    apply (cancel_epi i.inv).mp
    apply (cancel_mono i.hom).mp
    simpa only [L, e, i, Category.assoc, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id] using clopenIdempotent_restrict_self A E U
  have hε : ε ≫ e = ε := by
    have h := (clopenOpenAdjunction A E U).counit.naturality e
    change (D(((clopenInclusion E U).left)_!open⟦coefficient A⟧)).map (L.map e) ≫ ε =
      ε ≫ e at h
    rw [hL, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.symm
  let q := (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient A)
      (clopenInclusion E U).left).unit.app (𝟙_ (Ambient A E.left)) ≫
    (clopenDerivedComparison A E U).inv.app (L.obj (𝟙_ (Ambient A E.left)))
  have he : e = q ≫ ε := by
    simp only [L, e, q, ε, clopenIdempotent, clopenIdempotentNat, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc]
  change e ≫ e = e
  calc
    e ≫ e = (q ≫ ε) ≫ e := congrArg (fun f ↦ f ≫ e) he
    _ = q ≫ ε := by rw [Category.assoc, hε]
    _ = e := he.symm

/-- Clause 2, second half: under `Lj_V^* A_E ≅ A_V`, `j_V^* e_B = 0`.
Source: "one has ... and `j_V^*e_B = 0`" (blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 4): `j_V^* j_{B!} = 0` on sheaves (the defining presheaf of the extension by
zero of def-weil-extension-by-zero vanishes on every object over `V`, and on the empty object by
the sheaf axiom), hence termwise on complexes; `e_B` factors through `F L A_E = j_{B!} j_B^* A_E`,
so `Lj_V^* e_B = 0`, and conjugation by the constant identification keeps it `0`. -/
theorem clopenIdempotent_restrict_complement :
    (CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
          (clopenInclusion E (clopenComplement E U)).left).inv ≫
        (clopenPullback A E (clopenComplement E U)).map (clopenIdempotent A E U) ≫
        (CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
          (clopenInclusion E (clopenComplement E U)).left).hom =
      0 := by
  let L := clopenPullback A E (clopenComplement E U)
  have hz := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
    (coefficient A) (clopenInclusion E U).left
    (clopenInclusion E (clopenComplement E U)).left
    (by
      change Disjoint (Set.range (Subtype.val : U → E.left))
        (Set.range (Subtype.val : clopenComplement E U → E.left))
      rw [Subtype.range_val, Subtype.range_val]
      exact disjoint_compl_right)
    ((clopenPullback A E U).obj (𝟙_ (Ambient A E.left)))
  have hε : L.map ((clopenOpenAdjunction A E U).counit.app
      (𝟙_ (Ambient A E.left))) = 0 := hz.eq_of_src _ _
  simp only [clopenIdempotent, clopenIdempotentNat, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp]
  rw [hε]
  simp

end Idempotent

private theorem preimage_zero {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] (F : C₁ ⥤ C₂) [F.Full] [F.Faithful]
    {X Y : C₁} : F.preimage (0 : F.obj X ⟶ F.obj Y) = 0 := by
  apply F.map_injective
  simp

section Integral

variable {A D ell hell hA} (E : Over (Spec (.of D.k)))
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom] [IsProper E.hom]

attribute [local instance] clopenPiece_isProper

omit [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom] in
private theorem sectionIntegral_zero : sectionIntegral A ell hell hA E 0 = 0 := by
  have : (integrationExceptionalData A D ell hell hA E).lower.IsLeftAdjoint :=
    (integrationExceptionalData A D ell hell hA E).adjunction.isLeftAdjoint
  have hmap (X Y : Ctf A E.left) :
      ((integrationExceptionalData A D ell hell hA E).lower.map
        (0 : X ⟶ Y)).hom = 0 := by
    rw [CategoryTheory.Functor.map_zero]
    rfl
  have hzero : traceFormulaIntegrationEndomorphism A D ell hell hA E 0 = 0 := by
    simp only [traceFormulaIntegrationEndomorphism, zero_comp]
    erw [hmap]
    simp
  change traceFormulaIntegrationScalar A D _ = 0
  rw [hzero]
  simp [traceFormulaIntegrationScalar, preimage_zero, Sheaf.unitHomEval]

/-- Clause 3: for every `α : A_E → ω_{E,A}`, `∫_E (α ∘ e_B) = ∫_B α|_B ∈ A` (the properness of
`B` is the instance `clopenPiece_isProper`, that of `V` is `clopenComplementPiece_isProper`).
Source: "3. `B` and `V` are proper over `s` [lem-weil-pbc-closed-immersion-proper], and for
every morphism `α : A_E → ω_{E,A}` in `D(E,A)` ..., `∫_E(α∘e_B) = ∫_B α|_B ∈ A`"
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Steps 5-6): apply lem-trf-integration-component-sum to the two-piece clopen
partition `E = B ⊔ V` (both proper by Step 1) and the section `τ = α ∘ e_B`; its restrictions
are those of def-trf-local-term (`restrictSection`). Pullback respects composition, so clause 2
gives `τ|_B = α|_B` and `τ|_V = 0`; hence `∫_E τ = ∫_B α|_B + ∫_V 0`. The integral
of zero is zero: the exceptional left adjoint preserves zero morphisms, as do the fully
faithful preimages and evaluation used to read the resulting coefficient scalar. -/
theorem sectionIntegral_comp_clopenIdempotent (U : E.left.Opens)
    [Fact (IsClopen (U : Set E.left))]
    (α : 𝟙_ (Ambient A E.left) ⟶ dualizingComplex A D ell hell hA E) :
    sectionIntegral A ell hell hA E (clopenIdempotent A E U ≫ α) =
      sectionIntegral A ell hell hA (clopenPiece E U) (restrictSection A ell hell hA E U α) := by
  classical
  let W : ULift.{u} Bool → E.left.Opens := fun b ↦
    cond b.down U (clopenComplement E U)
  let (b : ULift.{u} Bool) : Fact (IsClopen (W b : Set E.left)) := by
    rcases b with ⟨b⟩
    cases b <;> dsimp [W] <;> infer_instance
  let (b : ULift.{u} Bool) : IsProper (clopenPiece E (W b)).hom :=
    clopenPiece_isProper E (W b)
  have hd : Pairwise fun b c ↦ Disjoint (W b) (W c) := by
    rintro ⟨b⟩ ⟨c⟩ h
    cases b <;> cases c
    · exact False.elim (h rfl)
    · exact TopologicalSpace.Opens.coe_disjoint.mp disjoint_compl_left
    · exact TopologicalSpace.Opens.coe_disjoint.mp disjoint_compl_right
    · exact False.elim (h rfl)
  have hc : ⨆ b, W b = ⊤ := by
    ext x
    simpa [W, clopenComplement, or_comm] using (Classical.em (x ∈ U))
  have hB : restrictSection A ell hell hA E U (clopenIdempotent A E U ≫ α) =
      restrictSection A ell hell hA E U α := by
    let i := CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
      (clopenInclusion E U).left
    have he := clopenIdempotent_restrict_self A E U
    have he' : i.inv ≫ (clopenPullback A E U).map (clopenIdempotent A E U) = i.inv := by
      apply (cancel_mono i.hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id] using he
    simp only [restrictSection, Functor.map_comp, ← Category.assoc]
    rw [he']
  have hV : restrictSection A ell hell hA E (clopenComplement E U)
      (clopenIdempotent A E U ≫ α) = 0 := by
    let i := CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
      (clopenInclusion E (clopenComplement E U)).left
    have he := clopenIdempotent_restrict_complement A E U
    have he' : i.inv ≫ (clopenPullback A E (clopenComplement E U)).map
        (clopenIdempotent A E U) = 0 := by
      apply (cancel_mono i.hom).mp
      simpa only [Category.assoc, zero_comp] using he
    simp only [restrictSection, Functor.map_comp, ← Category.assoc]
    rw [he']
    simp
  have h := sectionIntegral_eq_sum_restrictSection A ell hell hA E W hd hc
    (clopenIdempotent A E U ≫ α)
  rw [← Equiv.ulift.symm.sum_comp] at h
  simp only [Fintype.sum_bool] at h
  dsimp only [W, Equiv.ulift, Equiv.symm, ULift.down] at h
  change sectionIntegral A ell hell hA E (clopenIdempotent A E U ≫ α) =
    sectionIntegral A ell hell hA (clopenPiece E U)
      (restrictSection A ell hell hA E U (clopenIdempotent A E U ≫ α)) +
    sectionIntegral A ell hell hA (clopenPiece E (clopenComplement E U))
      (restrictSection A ell hell hA E (clopenComplement E U)
        (clopenIdempotent A E U ≫ α)) at h
  simpa only [hB, hV, sectionIntegral_zero, add_zero] using h

/-- Clause 3, the case `B = ∅`: the cut integral vanishes.
Source: "In particular the integral is `0` when `B = ∅`"
(blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 7): apply the cut-integral equality, then apply the existing component-sum
theorem to the empty family of opens of the empty scheme `B`. Its covering condition is
vacuous and its component sum is zero. -/
theorem sectionIntegral_comp_clopenIdempotent_bot
    (α : 𝟙_ (Ambient A E.left) ⟶ dualizingComplex A D ell hell hA E) :
    sectionIntegral A ell hell hA E (clopenIdempotent A E ⊥ ≫ α) = 0 := by
  rw [sectionIntegral_comp_clopenIdempotent]
  let T := clopenPiece E (⊥ : E.left.Opens)
  let W : PEmpty.{u + 1} → T.left.Opens := PEmpty.elim
  let (b : PEmpty.{u + 1}) : Fact (IsClopen (W b : Set T.left)) := b.elim
  let (b : PEmpty.{u + 1}) : IsProper (clopenPiece T (W b)).hom := b.elim
  have : IsEmpty T.left := ⟨fun x ↦ by
    have hx : x.val ∈ (⊥ : E.left.Opens) := x.property
    exact TopologicalSpace.Opens.mem_bot.mp hx⟩
  have hd : Pairwise fun b c ↦ Disjoint (W b) (W c) := fun b ↦ b.elim
  have hc : ⨆ b, W b = ⊤ := by
    ext x
    exact isEmptyElim x
  have h := sectionIntegral_eq_sum_restrictSection A ell hell hA T W hd hc
    (restrictSection A ell hell hA E ⊥ α)
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using h

/-- Clause 3, the case `B = E`: the cut integral is `∫_E α`.
Source: "and is `∫_E α` when `B = E`" (blueprint: lem-trf-local-term-clopen-idempotent).
Proof (node Step 7): the whole-space open inclusion is an isomorphism. Its derived pullback
is therefore faithful. Cancel the constant isomorphisms in the self-restriction assertion to
get `L(e_E) = 1`, and use faithfulness to deduce `e_E = 1`. Precomposition by the identity
does not change the section or its integral. -/
theorem sectionIntegral_comp_clopenIdempotent_top
    (α : 𝟙_ (Ambient A E.left) ⟶ dualizingComplex A D ell hell hA E) :
    sectionIntegral A ell hell hA E (clopenIdempotent A E ⊤ ≫ α) =
      sectionIntegral A ell hell hA E α := by
  have : IsIso (clopenInclusion E ⊤).left :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      simp only [clopenInclusion, Over.homMk_left, Scheme.Opens.opensRange_ι])
  let L := clopenPullback A E ⊤
  let i := CondensedRing.leftDerivedUpperStarUnitIso (coefficient A)
    (clopenInclusion E ⊤).left
  have he : clopenIdempotent A E ⊤ = 𝟙 _ := by
    apply L.map_injective
    rw [CategoryTheory.Functor.map_id]
    apply (cancel_epi i.inv).mp
    apply (cancel_mono i.hom).mp
    simpa only [L, i, Category.assoc, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id] using clopenIdempotent_restrict_self A E ⊤
  rw [he, Category.id_comp]

end Integral

end WeilConjectures.FiniteRingTrace
