/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module
public import Sheaf.Paper.ExceptionalRingTransportCoreData
/-! Proper/open normalization laws for exceptional integral transport.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
structure TransportCoreNormalizationLaws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  integralLeft_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((d.integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  inputGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      ((d.reconstruction E true).equivalence.functor.obj K).obj
  openGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
        ((d.reconstruction E true).equivalence.functor.obj K).obj)
  integral_system_normalized (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((d.realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K ≍
      (IntegralSystemRealization.RealizationModel.push l E.carrier
          (d.realizations E).realizationModel c.g).hom.app
        ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
          ((d.reconstruction E true).equivalence.functor.obj K).obj) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((d.realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              ((d.reconstruction E true).equivalence.functor.obj K).obj
              (inputGood E K) (openGood E K)).hom ≫
            (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory.map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((d.reconstruction E true).equivalence.functor.obj K))
                  (d.reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((d.reconstruction E true).equivalence.unitIso.inv.app K)))
section IntegralLeftNormalization
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (E : FieldStage.{u} l)
  (A : Operation.{u} l Ω X Y (.integral E))
  (r : LeftRealization.{u} l Ω c (.integral E) A)

/-- The integral comparison is the fully faithful lift of the given ambient left
realization followed by the proper/open compact-support realization.
Source: Zheng, Construction 5.25 and Proposition 5.26; the full-subcategory lift of
this specified natural isomorphism.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
def normalizedIntegralLeft :
    A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier :=
  ((sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
    (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
      (r ≪≫ Functor.isoWhiskerLeft
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c))

/-- The fully faithful lift has exactly the prescribed ambient component.
Proof: the image of a preimage under a fully faithful functor is the original map;
apply this equality to each component of the ambient composite.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
theorem normalizedIntegralLeft_hom (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map
        ((normalizedIntegralLeft l Ω D hl c E A r).hom.app K) =
      r.hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K) := by
  let eambient :
      (A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y) ⋙
        (sfIntegralConstructible l E.carrier Y).ι ≅
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) ⋙
        (sfIntegralConstructible l E.carrier Y).ι :=
    r ≪≫ Functor.isoWhiskerLeft
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
      (sfQcqsCompactSupportRealization l E.carrier D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c)
  exact congr_app
    (((sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
      (finiteTorConstructibleIntegralCategory l E.carrier X)).map_preimage eambient.hom) K

/-- The normalization equation characterizes the integral comparison uniquely.
Proof: both comparisons have the same image component by component. Faithfulness of
inclusion gives equality of the components, then of the natural transformations and
finally of the isomorphisms.
Source: Zheng, Construction 5.25 and Proposition 5.26; uniqueness of a fully faithful lift.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
theorem integralLeft_eq_normalized
    (e : A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier)
    (he : ∀ K : C.{u} l Ω X (.integral E),
      (sfIntegralConstructible l E.carrier Y).ι.map (e.hom.app K) =
        r.hom.app K ≫
          (sfQcqsCompactSupportRealization l E.carrier D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
            ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)) :
    e = normalizedIntegralLeft l Ω D hl c E A r := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (sfIntegralConstructible l E.carrier Y).fullyFaithfulι.map_injective
  exact (he K).trans (normalizedIntegralLeft_hom l Ω D hl c E A r K).symm

end IntegralLeftNormalization

section IntegralLeftObstruction
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)

/-- Replace the freely chosen integral comparison by its specified fully faithful lift.
This changes no other field of the transport data.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
def TransportCoreData.normalizeIntegralLeft : TransportCoreData l Ω D hl c operation left :=
  { d with
    integralLeft := fun E ↦
      normalizedIntegralLeft l Ω D hl c E (operation (.integral E)) (left (.integral E)) }

/-- The explicitly normalized data satisfy the integral-left equation.
Proof: its integral-left field is the fully faithful lift, so the equation is
`normalizedIntegralLeft_hom`. No compatibility assertion about the other fields is used.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
theorem TransportCoreData.normalizeIntegralLeft_hom
    (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map
        (((d.normalizeIntegralLeft l Ω D hl c operation left).integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K) := by
  exact normalizedIntegralLeft_hom l Ω D hl c E
    (operation (.integral E)) (left (.integral E)) K

/-- A normalization package forces every chosen integral comparison to be canonical.
Proof: apply uniqueness of the fully faithful lift to the first field of the package.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-obstruction) -/
theorem TransportCoreNormalizationLaws.integralLeft_eq
    (h : TransportCoreNormalizationLaws l Ω D hl c operation left d)
    (E : FieldStage.{u} l) :
    d.integralLeft E = normalizedIntegralLeft l Ω D hl c E
      (operation (.integral E)) (left (.integral E)) := by
  exact integralLeft_eq_normalized l Ω D hl c E
    (operation (.integral E)) (left (.integral E))
    (d.integralLeft E) (h.integralLeft_normalized E)

/-- A noncanonical freely chosen integral comparison obstructs the whole package.
Proof: its first normalization equation would force equality with the canonical lift,
contrary to the hypothesis. This uses no existence theorem for transport laws.
Source: the fully faithful lift in Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-obstruction) -/
theorem not_normalization_of_integralLeft_ne (E : FieldStage.{u} l)
    (he : d.integralLeft E ≠ normalizedIntegralLeft l Ω D hl c E
      (operation (.integral E)) (left (.integral E))) :
    ¬ Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left d) := by
  rintro ⟨h⟩
  exact he (h.integralLeft_eq l Ω D hl c operation left d E)

/-- Twisting just one integral comparison by a nonidentity natural automorphism
produces transport data admitting no normalization package.
Proof: normalization would identify the twisted comparison with the canonical one.
Cancel the canonical isomorphism; the twist would be the identity, a contradiction.
Source: the fully faithful lift in Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-obstruction) -/
theorem not_normalization_of_integralLeft_twist (E : FieldStage.{u} l)
    (α : (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) ≅
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier))
    (hα : α ≠ Iso.refl _) :
    letI := Classical.decEq (FieldStage.{u} l)
    ¬ Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left
      { d with
        integralLeft := Function.update d.integralLeft E
          (normalizedIntegralLeft l Ω D hl c E
            (operation (.integral E)) (left (.integral E)) ≪≫ α) }) := by
  classical
  rintro ⟨h⟩
  have he := h.integralLeft_eq l Ω D hl c operation left _ E
  change Function.update d.integralLeft E
    (normalizedIntegralLeft l Ω D hl c E
      (operation (.integral E)) (left (.integral E)) ≪≫ α) E = _ at he
  rw [Function.update_self] at he
  apply hα
  apply Iso.ext
  apply (cancel_epi (normalizedIntegralLeft l Ω D hl c E
    (operation (.integral E)) (left (.integral E))).hom).mp
  simpa only [Iso.trans_hom, Iso.refl_hom, Category.comp_id] using congrArg Iso.hom he

/-- A nonidentity twist refutes the assertion that every transport datum has laws.
Proof: apply a hypothetical universal existence statement to the datum obtained by
changing just its integral-left comparison, then use the twist obstruction.
Source: the fully faithful lift in Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-obstruction) -/
theorem not_forall_normalization_of_integralLeft_twist
    (d₀ : TransportCoreData l Ω D hl c operation left) (E : FieldStage.{u} l)
    (α : (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) ≅
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier))
    (hα : α ≠ Iso.refl _) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left d') := by
  classical
  intro h
  exact not_normalization_of_integralLeft_twist l Ω D hl c operation left d₀ E α hα (h _)

end IntegralLeftObstruction

/- STATEMENT-DISPUTED: `d.integralLeft` is arbitrary in TransportCoreData, whereas
`integralLeft_eq_normalized` proves that the first normalization equation forces its
value to be the one specified lift. The data and their laws must be constructed
jointly; existence of unnormalized data does not establish laws for every such datum. -/
/-- The proper/open normalization equations are supplied by integral realization.
Proof: transport the prescribed integral realization and retain its Good domains.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
theorem exists_exceptional_transport_core_normalization_laws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left d) := by
  sorry
end WeilConjectures.ExceptionalIntegralScalar
