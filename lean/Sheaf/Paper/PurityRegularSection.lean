/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityVectorBundleZeroSection
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

/-- Evaluation on U sends lambda to lambda(s restricted to U).
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section).
Proof: expand biduality and the global-sections/Hom equivalence. Its component at the identity
object of the localized site is precisely application of lambda to the restricted section. -/
theorem regularSectionEvaluation_apply {T : Scheme.{u}} (F : T.Modules) (s : F.sections)
    (U : T.Opens) (l : (Scheme.Modules.dual F).val.obj (op U)) :
    (regularSectionEvaluation F s).val.app (op U) l =
      l.app (op (Over.mk (𝟙 U))) (s.val (op U)) := by
  sorry

/-- The canonical dual frame on any open: restrict ordinary sheaf Hom, transpose the frame,
and use the coordinate-projection duality of the finite free module.
Source: Stacks Tag 01C6; purity dual-frame convention (blueprint: def-pur-regular-section). -/
def regularSectionDualFrame {T : Scheme.{u}} (F : T.Modules) (r : ℕ) (U : T.Opens)
    (e : F.over U ≅ SheafOfModules.free
      (R := T.ringCatSheaf.over U) (ULift.{u} (Fin r))) :
    (Scheme.Modules.dual F).over U ≅ SheafOfModules.free
      (R := T.ringCatSheaf.over U) (ULift.{u} (Fin r)) :=
  SheafOfModules.overHomObjIso F (SheafOfModules.unit T.ringCatSheaf) U ≪≫
    ((SheafOfModules.homFunctor (T.sheaf.over U)).flip.obj
      (SheafOfModules.unit _)).mapIso e.symm.op ≪≫
        SheafOfModules.homObjFreeUnitIso.{u} (ULift.{u} (Fin r))

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

/-- The evaluation algebra map is the unique symmetric-algebra extension of evaluation.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section). -/
def regularSectionAlgebraMap (F : T.Modules) (s : F.sections) :
    SymmetricAlgebraSheaf.algebra (Scheme.Modules.dual F) ⟶ Under.mk (𝟙 T.sheaf) :=
  (exists_quasiCoherentSymmetricAlgebra_core T (Scheme.Modules.dual F)
    (Under.mk (𝟙 T.sheaf)) (regularSectionEvaluation F s)).exists.choose

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

/-- Global module sections correspond bijectively to geometric sections of p.
Source: Stacks Tags 01M2 and 01LX (blueprint: def-pur-regular-section).
Proof: a geometric section gives a linear map out of F dual by the relative-Spec and symmetric
algebra universal properties. In a frame its values on the dual basis give the coefficients
of a section of F. Evaluation characterizes that section uniquely, so the local expressions
agree on overlaps and glue. These constructions are inverse, also for the empty frame. -/
theorem regularSectionGeometric_bijective (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] :
    Function.Bijective (regularSectionGeometric P T hT F r) := by
  sorry

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

/-- The ideal sheaf of the scheme-theoretic zero locus, as Mathlib ideal-sheaf data.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section). -/
def regularSectionZeroIdeal (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) : T.IdealSheafData :=
  (regularSectionZeroProjection P T hT F r s).ker

/-- The zero locus is closed, and its ideal on every affine open is the image of evaluation.
Source: Stacks Tags 067M and 01QO (blueprint: def-pur-regular-section).
Proof: choose a frame on an affine cover. The two maps from the polynomial algebra send each
variable to the component of s and to zero. Their tensor product is the quotient by the
components. The image of dual evaluation is that same ideal. The affine closed-immersion
criterion gives closedness; equality of the quasi-coherent ideals follows on affine opens. -/
theorem regularSectionZeroIdeal_spec (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) :
    IsClosedImmersion (regularSectionZeroProjection P T hT F r s) ∧
    ∀ (U : T.affineOpens) (a : T.presheaf.obj (op U.1)),
      a ∈ (regularSectionZeroIdeal P T hT F r s).ideal U ↔
        ∃ l : (Scheme.Modules.dual F).val.obj (op U.1),
          (regularSectionEvaluation F s).val.app (op U.1) l = a := by
  sorry

/-- In an affine frame the zero scheme is the quotient by the actual components of s, over U.
Source: Stacks Tags 067M and 01M2 (blueprint: def-pur-regular-section).
Proof: in the dual frame Sym(F dual)(U) is A[x_i]. Evaluation sends x_i to a_i and augmentation
sends it to zero. The affine fibre-product formula identifies the pullback ring with
A tensor over A[x_i] with A. Multiplication modulo (a_i) and a-bar mapped to a tensor 1
are well-defined inverse maps. Their spectra give the stated chart over U. -/
theorem regularSectionZero_affine (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) (U : T.affineOpens)
    (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1))) :
    ∃ i : (((regularSectionZeroProjection P T hT F r s) ⁻¹ᵁ U.1).toScheme) ≅
        Spec (CommRingCat.of (T.presheaf.obj (op U.1) ⧸
          Ideal.span (Set.range (b.repr (s.val (op U.1)))))),
      i.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span (Set.range (b.repr (s.val (op U.1))))))) ≫ U.2.isoSpec.inv =
        (regularSectionZeroProjection P T hT F r s) ∣_ U.1 := by
  sorry

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

/-- In a frame the dual basis consists of coordinate projections, and evaluation and
augmentation send its degree-one generators to the components and to zero, respectively.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section).
Proof: a basis of sections on an affine open induces a sheaf frame by quasi-coherence.
Its coordinate maps are the dual frame. The symmetric-algebra basis isomorphism sends the
dual generators to polynomial variables. The extension property of regularSectionAlgebraMap
and the augmentation property give their displayed values. -/
theorem regularSectionPolynomial_coordinates (F : T.Modules) (r : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] (s : F.sections) (U : T.affineOpens)
    (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1))) :
    ∃ d : Module.Basis (Fin r) (T.presheaf.obj (op U.1))
        ((Scheme.Modules.dual F).val.obj (op U.1)),
      (∀ i j : Fin r,
        (d i).app (op (Over.mk (𝟙 U.1))) (b j) =
          if i = j then (1 : T.presheaf.obj (op U.1)) else 0) ∧
      (∀ i : Fin r,
        SymmetricAlgebra.equivMvPolynomial d
          (SymmetricAlgebra.ι (T.presheaf.obj (op U.1)) _ (d i)) = MvPolynomial.X i) ∧
      (∀ i : Fin r,
        (regularSectionAlgebraMap T F s).right.hom.app (op U.1)
          ((SymmetricAlgebraSheaf.inclusion (Scheme.Modules.dual F)).val.app (op U.1)
            (d i)) = b.repr (s.val (op U.1)) i) ∧
      (∀ i : Fin r,
        (VectorBundleZeroSection.augmentation T (Scheme.Modules.dual F)).right.hom.app
          (op U.1)
          ((SymmetricAlgebraSheaf.inclusion (Scheme.Modules.dual F)).val.app (op U.1)
            (d i)) = 0) := by
  sorry

/-- The symmetric-algebra extension is uniquely characterized by evaluation on generators.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section).
Proof: apply the unique extension property of the symmetric-algebra sheaf to evaluation.
Its uniqueness also identifies the sectionwise map before sheafification with the usual lift. -/
theorem regularSectionAlgebraMap_spec (F : T.Modules) (s : F.sections) :
    (∀ (U : T.Opens) (l : (Scheme.Modules.dual F).val.obj (op U)),
      (regularSectionAlgebraMap T F s).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion (Scheme.Modules.dual F)).val.app (op U) l) =
          (regularSectionEvaluation F s).val.app (op U) l) ∧
    (∀ a : SymmetricAlgebraSheaf.algebra (Scheme.Modules.dual F) ⟶ Under.mk (𝟙 T.sheaf),
      (∀ (U : T.Opens) (l : (Scheme.Modules.dual F).val.obj (op U)),
        a.right.hom.app (op U)
          ((SymmetricAlgebraSheaf.inclusion (Scheme.Modules.dual F)).val.app (op U) l) =
            (regularSectionEvaluation F s).val.app (op U) l) →
      a = regularSectionAlgebraMap T F s) := by
  sorry

/-- The finite direct sum is the product module sheaf, whose section is the pair (s,t).
Source: purity (L3) (blueprint: def-pur-regular-section). -/
def regularSectionSum {X : Scheme.{u}} (F G : X.Modules)
    (s : F.sections) (t : G.sections) : (F ⨯ G).sections :=
  (F ⨯ G).unitHomEquiv (prod.lift (F.unitHomEquiv.symm s) (G.unitHomEquiv.symm t))

/-- The finite direct sum is the sectionwise direct sum and its section has projections s,t.
Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: limits of module sheaves are computed sectionwise. Thus the two product projections
identify sections with pairs, with inverse the product lift. The definition of the paired
global section and the product identities give its projections. -/
theorem regularSectionSum_sections {X : Scheme.{u}} (F G : X.Modules)
    (s : F.sections) (t : G.sections) :
    (∀ U : X.Opens, Function.Bijective (fun a : (F ⨯ G).val.obj (op U) ↦
      ((prod.fst : F ⨯ G ⟶ F).val.app (op U) a,
        (prod.snd : F ⨯ G ⟶ G).val.app (op U) a))) ∧
    SheafOfModules.sectionsMap prod.fst (regularSectionSum F G s t) = s ∧
    SheafOfModules.sectionsMap prod.snd (regularSectionSum F G s t) = t := by
  sorry

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

/-- The common quotient chart of the intersection in simultaneous frames.
Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: the affine fibre-product formula gives A/(a_i) tensor_A A/(b_j). Multiplication
modulo the sum ideal and a-bar mapped to a-bar tensor 1 are inverse maps. The projection
formula gives the chart over U and ensures agreement on overlaps. -/
theorem regularSectionIntersection_affine (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) (U : T.affineOpens)
    (b : Module.Basis (Fin r) (T.presheaf.obj (op U.1)) (F.val.obj (op U.1)))
    (c : Module.Basis (Fin e) (T.presheaf.obj (op U.1)) (G.val.obj (op U.1))) :
    ∃ i : (((regularSectionIntersectionProjection P T hT F G r e s t) ⁻¹ᵁ U.1).toScheme) ≅
        Spec (CommRingCat.of (T.presheaf.obj (op U.1) ⧸
          (Ideal.span (Set.range (b.repr (s.val (op U.1)))) ⊔
            Ideal.span (Set.range (c.repr (t.val (op U.1))))))),
      i.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span (Set.range (b.repr (s.val (op U.1)))) ⊔
          Ideal.span (Set.range (c.repr (t.val (op U.1))))))) ≫ U.2.isoSpec.inv =
        (regularSectionIntersectionProjection P T hT F G r e s t) ∣_ U.1 := by
  sorry

/-- The canonical direct-sum comparison commutes with the projection to T.
Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: take the property of the unique over-T comparison used in its definition. -/
theorem regularSectionSumZeroComparison_spec (F G : T.Modules) (r e : ℕ)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank e]
    (s : F.sections) (t : G.sections) :
    (regularSectionSumZeroComparison P T hT F G r e s t).hom ≫
      regularSectionIntersectionProjection P T hT F G r e s t =
        regularSectionSumZeroProjection P T hT F G r e s t := by
  sorry

/-- In rank zero the only section is zero, the bundle and its zero scheme are T over T,
and the section is regular. Source: Stacks Tag 067M (blueprint: def-pur-regular-section).
Proof: the empty frame identifies F with zero and its symmetric algebra with O_T. Relative
Spec of O_T is T, both section maps are the identity under this identification, and their
pullback is T. The empty list is regular in every scheme stalk because that local ring is
nonzero. This also covers an empty base, where the stalk condition has no instances. -/
theorem regularSection_rankZero (F : T.Modules) [F.IsFiniteLocallyFreeOfRank 0]
    (s : F.sections) :
    s = F.unitHomEquiv 0 ∧ IsIso (regularSectionBundle P T hT F 0).p ∧
      IsIso (regularSectionZeroProjection P T hT F 0 s) ∧
      IsRegularSection P T hT F 0 s := by
  sorry

/-- The polynomial map associated to a component tuple; the zero tuple gives augmentation.
Source: Stacks Tag 01M2 (blueprint: def-pur-regular-section). -/
def regularSectionPolynomialMap {A : Type u} [CommRing A] {r : ℕ} (a : Fin r → A) :
    CommRingCat.of (MvPolynomial (Fin r) A) ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (MvPolynomial.aeval a).toRingHom

/-- The affine tensor-product ring of section and zero maps is the component quotient.
Here the pushout in commutative rings is exactly the tensor product with the two specified
polynomial-algebra actions. The two projection maps become the quotient map, and its inverse
sends a residue class to a tensor 1.
Source: Stacks Tag 01M2, affine fibre products (blueprint: def-pur-regular-section).
Proof: multiplication modulo the component ideal is balanced: a polynomial evaluated at a
and at zero agrees modulo that ideal. It induces the map from the pushout. Conversely the
tensor relations kill each a_i tensor 1 and hence factor the left inclusion through the
quotient. The right inclusion equals the left on scalars, so these maps are mutually inverse.
Their formulas are precisely ab modulo the ideal and a-bar mapped to a tensor 1. -/
theorem regularSectionAffineRing {A : Type u} [CommRing A] (r : ℕ) (a : Fin r → A) :
    ∃ i : pushout (regularSectionPolynomialMap a)
        (regularSectionPolynomialMap (fun _ : Fin r ↦ (0 : A))) ≅
          CommRingCat.of (A ⧸ Ideal.span (Set.range a)),
      pushout.inl (regularSectionPolynomialMap a)
          (regularSectionPolynomialMap (fun _ : Fin r ↦ (0 : A))) ≫ i.hom =
        CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range a))) ∧
      pushout.inr (regularSectionPolynomialMap a)
          (regularSectionPolynomialMap (fun _ : Fin r ↦ (0 : A))) ≫ i.hom =
        CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range a))) ∧
      ∀ c : A, i.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range a)) c) =
        (pushout.inl (regularSectionPolynomialMap a)
          (regularSectionPolynomialMap (fun _ : Fin r ↦ (0 : A)))).hom c := by
  sorry

/-- The intersection tensor product has the concatenated component ideal, with the specified
multiplication map and inverse. Source: purity (L3) (blueprint: def-pur-regular-section).
Proof: the two quotient maps into A/(I+J) induce the multiplication map on the tensor product.
Both I and J vanish in the tensor product, so a-bar mapped to a-bar tensor 1 is well defined.
The tensor balancing relation makes it inverse on both factors, hence on pure tensors. -/
theorem regularSectionIntersectionRing {A : Type u} [CommRing A] (I J : Ideal A) :
    ∃ i : ((A ⧸ I) ⊗[A] (A ⧸ J)) ≃ₐ[A] A ⧸ (I ⊔ J),
      (∀ a b : A,
        i ((Ideal.Quotient.mk I a) ⊗ₜ[A] (Ideal.Quotient.mk J b)) =
          Ideal.Quotient.mk (I ⊔ J) (a * b)) ∧
      (∀ a : A, i.symm (Ideal.Quotient.mk (I ⊔ J) a) =
        (Ideal.Quotient.mk I a) ⊗ₜ[A] (1 : A ⧸ J)) := by
  sorry

/-- An empty zero locus makes regularity vacuous.
Source: Stacks Tag 067M (blueprint: def-pur-regular-section).
Proof: there is no point at which the local-frame regularity predicate has to be checked. -/
theorem regularSection_emptyZero (F : T.Modules) (r : ℕ) [F.IsFiniteLocallyFreeOfRank r]
    (s : F.sections) [IsEmpty (regularSectionZeroScheme P T hT F r s)] :
    IsRegularSection P T hT F r s := by
  sorry

end AlgebraicGeometry
