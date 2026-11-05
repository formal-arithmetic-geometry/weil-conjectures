/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Regular sections and transverse direct sums

Source: Stacks Project, Tags 067M, 01WY, 01M2, 01LW and 01LX; purity blueprint,
localized top Chern class, statement and (L3) (blueprint: def-pur-regular-section).

The module starts with an actual global section of F. Its evaluation on the ordinary sheaf
dual defines the map to Spec Sym(F dual). The affine characterization determines this map
uniquely, so choosing it does not choose arbitrary geometric data. Regularity uses the actual
components in a frame, and transversality uses the concatenation of two such component lists.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry

/-- Evaluation at a global section, using the ordinary sheaf-Hom bidual map.
Source: Stacks Tag 01M2; purity section convention (blueprint: def-pur-regular-section). -/
def regularSectionEvaluation {T : Scheme.{u}} (F : T.Modules) (s : F.sections) :
    Scheme.Modules.dual F ⟶ SheafOfModules.unit T.ringCatSheaf :=
  SheafOfModules.homObjSectionsEquiv (Scheme.Modules.dual F)
    (SheafOfModules.unit T.ringCatSheaf)
    (SheafOfModules.sectionsMap (SheafOfModules.bidual (R := T.sheaf) F) s)

/-- The ordinary dual has the same constant rank, including rank zero.
Source: Stacks Tag 01C6 and the dual-frame convention (blueprint: def-pur-regular-section).
Proof: restrict a frame to each trivializing open. Coordinate projections are the dual basis,
so Hom(O^r,O) is O^r on that open. These opens cover the scheme. -/
theorem regularSectionDual_rank {T : Scheme.{u}} (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] :
    (Scheme.Modules.dual F).IsFiniteLocallyFreeOfRank r := by
  sorry

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  (T : Scheme.{u}) (hT : T ⟶ Spec (CommRingCat.of P.field.k))
  [IsSeparated hT] [LocallyOfFiniteType hT] [QuasiCompact hT]

/-- E(F) is the canonical relative spectrum of Sym(F dual), with its canonical zero section.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section). -/
def regularSectionBundle (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r] :
    PurityVectorBundle P T hT r where
  E := @VectorBundleZeroSection.scheme T (isNoetherian_of_locallyOfFiniteType hT) r
    (Scheme.Modules.dual F) (regularSectionDual_rank F r)
  p := @VectorBundleZeroSection.π T (isNoetherian_of_locallyOfFiniteType hT) r
    (Scheme.Modules.dual F) (regularSectionDual_rank F r)
  𝓔 := Scheme.Modules.dual F
  locallyFree := regularSectionDual_rank F r
  phi := Iso.refl _
  over_commutes := Category.id_comp _

/-- The canonical map into E(F) exists uniquely and has the evaluation ring map on every
relative-Spec affine chart. Source: Stacks Tags 01LW and 01LX
(blueprint: def-pur-regular-section).
Proof: extend evaluation by the symmetric-algebra universal property. The relative-Spec
anti-equivalence sends this algebra morphism to a morphism over T. Its affine-chart clause
identifies the restriction with Spec of SymmetricAlgebra.lift of evaluation, using the affine
symmetric-algebra comparison. Conversely these affine maps determine the morphism on a cover,
so uniqueness follows. -/
theorem regularSectionGeometric_existsUnique (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) :
    ∃! f : {f : T ⟶ (regularSectionBundle P T hT F r).E //
        f ≫ (regularSectionBundle P T hT F r).p = 𝟙 T},
      ∀ U : T.affineOpens,
        ∃ fU : U.1.toScheme ⟶
            (((regularSectionBundle P T hT F r).p) ⁻¹ᵁ U.1).toScheme,
          fU ≫ (((regularSectionBundle P T hT F r).p) ⁻¹ᵁ U.1).ι = U.1.ι ≫ f.val ∧
          fU ≫ @VectorBundleZeroSection.affineChart T
            (isNoetherian_of_locallyOfFiniteType hT) r (Scheme.Modules.dual F)
              (regularSectionDual_rank F r) U =
            U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
              ((SymmetricAlgebra.lift
                (((regularSectionEvaluation F s).val.app (op U.1)).hom)).toRingHom)) := by
  sorry

/-- The geometric section determined by dual evaluation, chosen from its unique affine
characterization, not from an unconstrained existence statement.
Source: Stacks Tags 01M2 and 01LX (blueprint: def-pur-regular-section). -/
def regularSectionGeometric (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : {f : T ⟶ (regularSectionBundle P T hT F r).E //
      f ≫ (regularSectionBundle P T hT F r).p = 𝟙 T} :=
  (regularSectionGeometric_existsUnique P T hT F r s).exists.choose

/-- The zero scheme is the fibre product of the evaluation section with the zero section.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section). -/
def regularSectionZeroScheme (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : Scheme.{u} :=
  pullback (regularSectionGeometric P T hT F r s).val
    (regularSectionBundle P T hT F r).zeroSection

/-- The zero-scheme projection to the base.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section). -/
def regularSectionZeroProjection (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : regularSectionZeroScheme P T hT F r s ⟶ T :=
  pullback.fst _ _

/-- Regularity is regularity of the component germs in an actual local frame of F.
Source: Stacks Tags 067M and 01WY (blueprint: def-pur-regular-section). -/
def IsRegularSection (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : Prop :=
  ∀ x : regularSectionZeroScheme P T hT F r s,
    ∃ (U : T.affineOpens)
      (hx : regularSectionZeroProjection P T hT F r s x ∈ U.1)
      (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1))),
      RingTheory.Sequence.IsRegular
        (T.presheaf.stalk (regularSectionZeroProjection P T hT F r s x))
        (List.ofFn (fun i : Fin r ↦
          T.presheaf.germ U.1 (regularSectionZeroProjection P T hT F r s x) hx
            (b.repr (s.val (op U.1)) i)))

/-- The scheme-theoretic intersection is the pullback of the zero-scheme inclusions.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionIntersectionScheme (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Scheme.{u} :=
  pullback (regularSectionZeroProjection P T hT F r s)
    (regularSectionZeroProjection P T hT G e t)

/-- The intersection projection.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionIntersectionProjection (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    regularSectionIntersectionScheme P T hT F G r e s t ⟶ T :=
  pullback.fst _ _ ≫ regularSectionZeroProjection P T hT F r s

/-- Transversality requires both sections regular and the concatenated actual components
regular in simultaneous frames at every intersection point.
Source: Stacks Tag 067M; purity (L3) (blueprint: def-pur-regular-section). -/
def IsTransverseDirectSum (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Prop :=
  IsRegularSection P T hT F r s ∧ IsRegularSection P T hT G e t ∧
  ∀ x : regularSectionIntersectionScheme P T hT F G r e s t,
    ∃ (U : T.affineOpens)
      (hx : regularSectionIntersectionProjection P T hT F G r e s t x ∈ U.1)
      (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1)))
      (c : Module.Basis (Fin e) (T.presheaf.obj (op U.1)) (G.val.obj (op U.1))),
      RingTheory.Sequence.IsRegular
        (T.presheaf.stalk (regularSectionIntersectionProjection P T hT F G r e s t x))
        ((List.ofFn (fun i : Fin r ↦
          T.presheaf.germ U.1 (regularSectionIntersectionProjection P T hT F G r e s t x)
            hx (b.repr (s.val (op U.1)) i))) ++
          List.ofFn (fun j : Fin e ↦
            T.presheaf.germ U.1 (regularSectionIntersectionProjection P T hT F G r e s t x)
              hx (c.repr (t.val (op U.1)) j)))

/-- The finite direct sum is the product module sheaf, whose section is the pair (s,t).
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSum {X : Scheme.{u}} (F G : X.Modules)
    (s : F.sections) (t : G.sections) : (F ⨯ G).sections :=
  (F ⨯ G).unitHomEquiv (prod.lift (F.unitHomEquiv.symm s) (G.unitHomEquiv.symm t))

/-- The direct sum of ranks r and e has rank r+e.
Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: take simultaneous local frames and concatenate their bases. Their inverses are the
two coordinate projections. These simultaneous frame opens cover the base. -/
theorem regularSectionSum_rank {X : Scheme.{u}} (F G : X.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e] :
    (F ⨯ G).IsFiniteLocallyFreeOfRank (r + e) := by
  sorry

/-- The zero scheme of the actual paired section of the direct sum module.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroScheme (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : Scheme.{u} :=
  @regularSectionZeroScheme P T hT _ _ _ (F ⨯ G) (r + e)
    (regularSectionSum_rank F G r e) (regularSectionSum F G s t)

/-- The paired zero-scheme projection.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroProjection (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) : regularSectionSumZeroScheme P T hT F G r e s t ⟶ T :=
  @regularSectionZeroProjection P T hT _ _ _ (F ⨯ G) (r + e)
    (regularSectionSum_rank F G r e) (regularSectionSum F G s t)

/-- The paired zero scheme is canonically the scheme-theoretic intersection, over the base.
Source: purity (L3), affine fibre products (blueprint: def-pur-regular-section).
Proof: in simultaneous frames both closed subschemes have quotient ring A/(a_i,b_j).
The intersection tensor product A/(a_i) tensor_A A/(b_j) maps to this quotient by
multiplication; a-bar maps inversely to a-bar tensor 1. These maps commute with projections.
Consequently the affine comparisons agree on overlaps and glue. As closed subschemes of T,
the comparison over T is unique. -/
theorem regularSectionSumZeroComparison_existsUnique (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    ∃! i : regularSectionSumZeroScheme P T hT F G r e s t ≅
        regularSectionIntersectionScheme P T hT F G r e s t,
      i.hom ≫ regularSectionIntersectionProjection P T hT F G r e s t =
        regularSectionSumZeroProjection P T hT F G r e s t := by
  sorry

/-- The canonical comparison, determined by its commutation with the zero-scheme projections.
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSumZeroComparison (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    regularSectionSumZeroScheme P T hT F G r e s t ≅
      regularSectionIntersectionScheme P T hT F G r e s t :=
  (regularSectionSumZeroComparison_existsUnique P T hT F G r e s t).exists.choose

end AlgebraicGeometry
