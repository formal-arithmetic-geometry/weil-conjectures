# Integral coefficient comparison factorization

## Reason

The remaining integralStratifiedPerfectDetailed hole needs the existing completeness
comparison. Its original module also contains a bounded-constructibility comparison
proved from integralStratifiedPerfectDetailed. Importing that whole module would cycle.
Factor the genuinely independent coefficient constructions and completeness comparison
into modules that the original modules publicly reexport. This is an interface
factorization, not a change of rings, functors, predicates or hypotheses. The two
adapted modules other than the Q3 item were unclaimed at the audit.

The Roos theorem has precisely one current direct importer,
CompletedCoefficientPresentationTransport, which keeps its explicit public import of
the original item. Thus reducing the Roos theorem's public import loses no declaration
in that consumer. The public import closures of the item and presentation transport
continue to contain all their original declarations. No WeilConjectures source file
is changed. The target statements and mathematical meanings remain identical.

## Old

The following entire coefficient construction block was in
Sheaf.Paper.IntegralStratifiedPerfectCharacterization:

```lean
/-- The quotient coefficient identification induced by the canonical valuation-ring lift.
The normalization on representatives determines the equivalence uniquely. The source
uses the recorded valuation ring lifted to the small site's coefficient universe.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: ULift.down is a ring equivalence from the recorded lifted valuation ring to the
original valuation ring. It sends the recorded lifted uniformizer to the original
uniformizer, and hence identifies their principal ideals and every positive power.
Descend this equivalence to the quotients and lift its target. Surjectivity of the
quotient map proves uniqueness from the displayed representative formula. -/
theorem integralCoefficientULift_exists
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    ∃! e : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1) ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ x : PbcIntegralRing l E,
        e (Ideal.Quotient.mk _ x) = ULift.up (Ideal.Quotient.mk _ x.down) := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E :=
    ULift.ringEquiv
  have hI : Padic.coefficientExtensionIdeal l E (n + 1) =
      Ideal.map e.toRingHom ((pbcIntegralDatum l E).ideal ^ (n + 1)) := by
    simp [pbcIntegralDatum, Padic.coefficientExtensionIdeal, Ideal.map_pow,
      Ideal.map_span, Set.image_singleton, e, pbcUniformizer]
    rfl
  let q := Ideal.quotientEquiv _ _ e hI
  refine ⟨q.trans ULift.ringEquiv.symm, ?_, ?_⟩
  · intro x
    change ULift.up (q (Ideal.Quotient.mk _ x)) = _
    rw [Ideal.quotientEquiv_mk]
    rfl
  · intro e' he'
    apply RingEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (he' x).trans (by
      change ULift.up (Ideal.Quotient.mk _ x.down) =
        ULift.up (q (Ideal.Quotient.mk _ x))
      rw [Ideal.quotientEquiv_mk]
      rfl)

/-- The uniquely normalized quotient equivalence, not an arbitrary field identification.
Source: blueprint coefficient conventions, order 411; Bhatt--Scholze, Section 6.5
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralCoefficientULift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  (integralCoefficientULift_exists l E n).exists.choose

/-- The finite-level coefficient isomorphism: undo the normalized functions-sheaf
presentation, apply the quotient lift and forget commutativity.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedLevelComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (adicLisseForget T).obj
        ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)) ≅
      WeilConjectures.integralCoefficientSheaf l E T n :=
  (adicLisseForget T).mapIso
    ((pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
        (integralCoefficientULift l E n).toCommRingCatIso)

/-- The unique completed coefficient comparison compatible with every finite projection.
This keeps the detailed definition's actual ring and positive reduction functors.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: the normalized finite-level comparisons commute with transitions, as can be
checked on residue representatives. Apply the limit universal property. Forgetting
commutativity preserves limits, so both rings are limits of the same quotient system.
The projection identities determine a unique isomorphism. -/
theorem integralDetailedCoefficientComparison_exists
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃! e : (adicLisseForget T).obj
        (pbcAdicCompletion T (pbcIntegralDatum l E)) ≅
          WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T,
      ∀ n : ℕ,
        e.hom ≫ limit.π (WeilConjectures.integralCoefficientSheafSystem l E T) (op n) =
          (adicLisseForget T).map
              (pbcAdicProjection T (pbcIntegralDatum l E) n) ≫
            (integralDetailedLevelComparison T l E n).hom := by
  let d := pbcIntegralDatum l E
  let F := adicLisseForget T
  let C := constantSheaf (ProEt.topology T) CommRingCat.{u + 1}
  have hq (n : ℕ) (x : PbcIntegralRing l E) :
      integralCoefficientULift l E n (Ideal.Quotient.mk _ x) =
        ULift.up (Ideal.Quotient.mk _ x.down) :=
    (integralCoefficientULift_exists l E n).exists.choose_spec x
  have htrans (n : ℕ) :
      CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)) ≫
        (integralCoefficientULift l E n).toCommRingCatIso.hom =
      (integralCoefficientULift l E (n + 1)).toCommRingCatIso.hom ≫
        CommRingCat.ofHom
          ((ULift.ringEquiv.symm.toRingHom).comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change integralCoefficientULift l E n
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1) (Ideal.Quotient.mk _ x)) = _
    change integralCoefficientULift l E n (Ideal.Quotient.mk _ x) = _
    rw [hq]
    change ULift.up (Ideal.Quotient.mk _ x.down) =
      ULift.up ((Padic.coefficientExtensionTransition l E (n + 1))
        ((integralCoefficientULift l E (n + 1) (Ideal.Quotient.mk _ x)).down))
    rw [hq]
    rfl
  let c : adicLisseRingSystem T d.ideal ⋙ F ⟶
      WeilConjectures.integralCoefficientSheafSystem l E T :=
    NatTrans.ofOpSequence
      (fun n ↦ F.map (C.map (integralCoefficientULift l E n).toCommRingCatIso.hom))
      (by
        intro n
        dsimp only [Functor.comp_map]
        simp only [adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ,
          WeilConjectures.integralCoefficientSheafSystem,
          WeilConjectures.integralCoefficientSheafTransition]
        change F.map (C.map _) ≫ F.map (C.map _) =
          F.map (C.map _) ≫ F.map (C.map _)
        simp only [← F.map_comp, ← C.map_comp, htrans])
  have (n : ℕᵒᵖ) : IsIso (c.app n) := by
    change IsIso (F.map (C.map (integralCoefficientULift l E n.unop).toCommRingCatIso.hom))
    infer_instance
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have : PreservesLimit (pbcAdicRings T d) F := by
    have : PreservesLimit (pbcAdicRings T d)
        (F ⋙ sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}) :=
      inferInstanceAs (PreservesLimit (pbcAdicRings T d)
        (sheafToPresheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
          (Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat.{u + 1} RingCat.{u + 1}).obj
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    exact preservesLimit_of_reflects_of_preserves F
      (sheafToPresheaf (ProEt.topology T) RingCat.{u + 1})
  let w := Functor.isoWhiskerRight (pbcConstantSystemComparison T d).symm F ≪≫ asIso c
  let e := preservesLimitIso F (pbcAdicRings T d) ≪≫ HasLimit.isoOfNatIso w
  refine ⟨e, ?_, ?_⟩
  · intro n
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl
  · intro e' he'
    apply Iso.ext
    apply limit.hom_ext
    intro n
    change e'.hom ≫ limit.π _ n = e.hom ≫ limit.π _ n
    rw [he' n.unop]
    dsimp only [e, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
      preservesLimitIso_hom_π]
    rfl

/-- Canonical ring comparison, chosen from its unique projection normalization.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedCoefficientComparison
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (integralDetailedCoefficientComparison_exists T l E).exists.choose

/-- Scalar restriction along this canonical ring isomorphism is exact.
Source: Bhatt--Scholze, Section 6.5; Stacks Tag 03DA
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization).
Proof: restriction changes only the scalar action. Restriction along the inverse
is its inverse equivalence. Finite limits and colimits are unchanged on underlying
additive sheaves, and therefore preserved. -/
theorem integralDetailedCoefficientRestriction_exact
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u + 1}
        (integralDetailedCoefficientComparison T l E).hom) := by
  let F := SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom
  let R := (adicLisseForget T).obj (pbcAdicCompletion T (pbcIntegralDatum l E))
  let B := WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u + 1} B))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} B))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R)⟩

/-- Transport the detailed category along the canonical coefficient isomorphism.
The valuation ring is lifted to the small site's coefficient universe u+1. The
finite extension E itself retains the recorded coefficient convention E : Type u.
Source: Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-weil-pbc-integral-stratified-perfect-characterization). -/
def integralDetailedTransport
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      DerivedCategory (pbcModules T
        (pbcAdicCompletion T (pbcIntegralDatum l E))) :=
  letI := HasDerivedCategory.standard
    (WeilConjectures.scalarReductionSource.{u, u} l E T)
  letI := (integralDetailedCoefficientRestriction_exact T l E).1
  letI := (integralDetailedCoefficientRestriction_exact T l E).2
  (SheafOfModules.restrictScalars.{u + 1}
    (integralDetailedCoefficientComparison T l E).hom).mapDerivedCategory
```

The following independent prefix was in
Sheaf.Paper.CompletedCoefficientPresentationTransport:

```lean
section CoefficientPresentation
variable (W : Scheme.{u})

/-- Lift the landed Ring-level coefficient comparison to commutative ring sheaves.
Its image under forgetting commutativity is the existing normalized comparison.
Source: Stacks 099N and Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: a morphism between commutative rings is exactly a ring morphism. Thus the
forgetful functor on ring sheaves is fully faithful. Lift the existing comparison
and its inverse. Faithfulness gives their inverse identities and uniqueness. The
finite projection normalization is inherited from the landed comparison. -/
theorem purCoefficientIso_existsUnique :
    ∃! e : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E W,
      (adicLisseForget W).mapIso e = integralDetailedCoefficientComparison W l E := by
  let F := adicLisseForget W
  let hF := fullyFaithfulSheafCompose (ProEt.topology W)
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  refine ⟨hF.preimageIso (integralDetailedCoefficientComparison W l E), ?_, ?_⟩
  · apply Iso.ext
    exact hF.map_preimage _
  · intro e he
    apply F.mapIso_injective
    apply Iso.ext
    exact (congrArg Iso.hom he).trans (hF.map_preimage _).symm

/-- The CommRing lift of integralDetailedCoefficientComparison, with no new choice
of normalization. Source: Stacks 099N
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCoefficientIso := (purCoefficientIso_existsUnique l E W).exists.choose

end CoefficientPresentation

/-- The actual coefficient transport on ordinary module sheaves.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
abbrev purOrdinaryCoefficientModel (W : Scheme.{u}) :
    pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)) ⥤
      integralTowerModules.{u, u} l E W :=
  pbcRestrict (purCoefficientIso l E W).inv

/-- Additivity of the specified exact coefficient restriction.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_additive (W : Scheme.{u}) :
    (purOrdinaryCoefficientModel l E W).Additive := pbcRestrict_additive _

/-- Exactness of the specified coefficient restriction on finite limits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_limits (W : Scheme.{u}) :
    PreservesFiniteLimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_limits _

/-- Exactness of the specified coefficient restriction on finite colimits.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
instance purOrdinaryCoefficientModel_colimits (W : Scheme.{u}) :
    PreservesFiniteColimits (purOrdinaryCoefficientModel l E W) := pbcRestrict_colimits _

/-- The ordinary restriction round trip is the identity on every section.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: the CommRing lift forgets to the landed ring isomorphism. Restricting along
its inverse and then its forward map restores the same scalar action. Identity
section functions are linear and natural, with identity inverses. Sections detect
module morphisms, so this normalization determines the isomorphism uniquely. -/
theorem purOrdinaryCoefficientRoundTrip_existsUnique (W : Scheme.{u}) :
    ∃! e : purOrdinaryCoefficientModel l E W ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (integralDetailedCoefficientComparison W l E).hom ≅
      𝟭 (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))),
      ∀ (M : pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E)))
        (U : W.ProEtᵒᵖ) (x : M.val.obj U), (e.hom.app M).val.app U x = x := by
  let e := purCoefficientIso l E W
  have he : (adicLisseForget W).mapIso e =
      integralDetailedCoefficientComparison W l E :=
    (purCoefficientIso_existsUnique l E W).exists.choose_spec
  rw [← he]
  obtain ⟨c, hc, _⟩ := pbcRestrictComp_exists e.hom e.inv (𝟙 _) e.hom_inv_id
  obtain ⟨d, hd, _⟩ := pbcScalarRestrictId_exists l E W
  refine ⟨c ≪≫ d, ?_, ?_⟩
  · intro M U x
    change (d.hom.app M).val.app U ((c.hom.app M).val.app U x) = x
    rw [hc, hd]
  · intro e' he'
    apply Iso.ext
    ext M U x
    change (e'.hom.app M).val.app U x =
      (d.hom.app M).val.app U ((c.hom.app M).val.app U x)
    rw [he', hc, hd]

/-- The uniquely section-normalized ordinary restriction round trip.
Source: Stacks 03DA (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purOrdinaryCoefficientRoundTrip (W : Scheme.{u}) :=
  (purOrdinaryCoefficientRoundTrip_existsUnique l E W).exists.choose

section RestrictionEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

private def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle (c : R ≅ S) (M : SheafOfModules.{u + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

private theorem restriction_isEquivalence (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} c.hom).IsEquivalence :=
  (restrictionEquivalence c).isEquivalence_functor

private theorem restrictionEquivalence_unit (c : R ≅ S)
    (M : SheafOfModules.{u + 1} S) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictionEquivalence c).unit.app M).val.app U x = x := by
  rfl

end RestrictionEquivalence

/-- The landed integralDetailedTransport is an equivalence.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: restriction along the inverse coefficient ring isomorphism is an exact
inverse to the landed restriction functor. Both ordinary round trips are identity
on sections. Termwise round trips descend through derived localization, proving
full faithfulness and essential surjectivity of the existing functor. -/
@[instance] theorem purDetailedTransport_isEquivalence (W : Scheme.{u}) :
    (integralDetailedTransport W l E).IsEquivalence := by
  have := restriction_isEquivalence (integralDetailedCoefficientComparison W l E)
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  exact Functor.isEquivalence_mapDerivedCategory _

/-- The exact restriction round trip, descended by the published localization API.
Source: Stacks 03DA, 099N
(blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purDerivedCoefficientRoundTrip (W : Scheme.{u}) :
    pbcDerivedRestrict (purCoefficientIso l E W).inv ⋙
      integralDetailedTransport W l E ≅
        𝟭 (PbcCompletedDerived W (pbcIntegralDatum l E)) :=
  have := (integralDetailedCoefficientRestriction_exact W l E).1
  have := (integralDetailedCoefficientRestriction_exact W l E).2
  (Functor.mapDerivedCategoryCompIso (purOrdinaryCoefficientModel l E W)
    (SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison W l E).hom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (purOrdinaryCoefficientRoundTrip l E W) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- Reuse the inverse of the landed transport. changeFunctor gives its explicit
CommRing restriction model via the identity-on-sections round trip; the inverse
functor remains exactly integralDetailedTransport.
Source: Stacks 099N (blueprint: def-pur-completed-coefficient-presentation-transport). -/
def purCoefficientModel (W : Scheme.{u}) :
    PbcCompletedDerived W (pbcIntegralDatum l E) ≌
      DerivedCategory (integralTowerModules.{u, u} l E W) :=
  (integralDetailedTransport W l E).asEquivalence.symm.changeFunctor
    ((Iso.isoCompInverse
      (H := (integralDetailedTransport W l E).asEquivalence)
      (purDerivedCoefficientRoundTrip l E W) ≪≫ Functor.leftUnitor _).symm)

/-- Completeness alone is invariant under the existing coefficient transport.
Source: Stacks 099N, Bhatt--Scholze 6.5
(blueprint: def-pur-completed-coefficient-presentation-transport).
Proof: normalized coefficient projections identify the finite reductions and
quotient units. Exact restriction preserves the product and Roos descriptions of
the completion unit, so its being invertible is unchanged. The recorded intrinsic
and slice completeness predicates test this same unit, without geometric bounds. -/
theorem purCoefficientModel_predicates (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IntegralOnSlice.IsComplete l E W none ((purCoefficientModel l E W).functor.obj K)) ∧
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E) K ↔
      IsSfDerivedComplete l E W ((purCoefficientModel l E W).functor.obj K)) := by
  let d := pbcIntegralDatum l E
  let Φ := purCoefficientModel l E W
  let C := pbcActualCompletion d W
  let η := pbcActualCompletionUnit d W
  let P : ObjectProperty (PbcCompletedDerived W d) := PbcIsIntrinsicallyComplete W d
  have hP : P.IsClosedUnderIsomorphisms := by
    constructor
    intro A B e hA
    obtain ⟨r, f, hf, A', eA, hA'⟩ := hA
    refine ⟨r, f, hf, A', eA ≪≫
      (pbcDerivedExtend (pbcCompletedComparison W d).inv).mapIso e, ?_⟩
    change IsIso (eA.inv ≫ _) at hA'
    have hu := (isIso_comp_left_iff eA.inv _).mp hA'
    change IsIso ((_ ≫ eA.inv) ≫ _)
    infer_instance
  have := hP
  obtain ⟨hp, p, δ, ht, hu⟩ := completedCoefficientCompletionRoosTransport l E W
    (purCoefficientIso l E W) (purCoefficientIso_existsUnique l E W).exists.choose_spec K
  have := hp
  have hsf : P K ↔ IsSfDerivedComplete l E W (Φ.functor.obj K) := by
    constructor
    · intro hK
      let adj := Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)
      have : IsIso (η.app K) :=
        adj.isIso_unit_app_of_iso (X := ⟨K, hK⟩) (Iso.refl K)
      let i := asIso (Φ.functor.map (η.app K))
      let δ' := δ ≫ (shiftFunctor _ (1 : ℤ)).map i.inv
      refine ⟨hp, δ', ?_⟩
      let T := Pretriangulated.Triangle.mk
        (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app (Φ.functor.obj K)))
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ'
      let T' := Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ
      let e : T ≅ T' := Pretriangulated.Triangle.isoMk T T' i (Iso.refl _) (Iso.refl _)
        (by
          change (Pi.lift _) ≫ 𝟙 _ = i.hom ≫ p
          exact (Category.comp_id _).trans hu.symm)
        (by
          change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by
          change (δ ≫ (shiftFunctor _ (1 : ℤ)).map i.inv) ≫
            (shiftFunctor _ (1 : ℤ)).map i.hom = 𝟙 _ ≫ δ
          rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
      exact (Pretriangulated.distinguished_iff_of_iso e).mpr ht
    · rintro ⟨hp', δ', ht'⟩
      have := hp'
      let T := Pretriangulated.Triangle.mk
        (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app (Φ.functor.obj K)))
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ'
      let T' := Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism
          (fun n ↦ (sfDerivedReductionTransition l E W n).app (Φ.functor.obj K))) δ
      let e := Pretriangulated.isoTriangleOfIso₁₂ T.rotate T'.rotate
        (Pretriangulated.rot_of_distTriang T ht')
        (Pretriangulated.rot_of_distTriang T' ht) (Iso.refl _) (Iso.refl _)
        (by
          change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
          exact (Category.comp_id _).trans (Category.id_comp _).symm)
      let i : Φ.functor.obj K ≅ Φ.functor.obj (C.obj K) :=
        (shiftFunctor _ (1 : ℤ)).preimageIso (Pretriangulated.Triangle.π₃.mapIso e)
      let j : K ≅ C.obj K := Φ.functor.preimageIso i
      exact ObjectProperty.prop_of_iso P j.symm
        (((ObjectProperty.ι P).leftAdjoint.obj K).property)
  have hlegacy : IsSfDerivedComplete l E W (Φ.functor.obj K) ↔
      IntegralOnSlice.IsComplete l E W none (Φ.functor.obj K) := by
    change IsSfDerivedComplete l E W (Φ.functor.obj K) ↔
      ∃ (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p),
        IsDerivedComplete l E W D hl (Φ.functor.obj K)
    constructor
    · intro hK
      obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
      have : Fact p.Prime := ⟨hprime⟩
      let D : FiniteFieldDatum.{0} :=
        { p := p
          a := 1
          q := p
          prime := hprime
          exponent_pos := by decide
          cardinality_eq := by simp
          k₀ := ZMod p
          card_base := by simp [Nat.card_eq_fintype_card]
          k := AlgebraicClosure (ZMod p) }
      have hl : l ≠ D.p := by change l ≠ p; omega
      exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E W D hl _).mp hK⟩
    · rintro ⟨D, hl, hK⟩
      exact (sfDerivedComplete_iff_legacy l E W D hl _).mpr hK
  exact ⟨hsf.trans hlegacy, hsf⟩
```

The Roos module publicly imported:

```lean
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
```

## New

The first block is unchanged, including all public signatures and definition bodies,
in Sheaf.Paper.IntegralCompletedCoefficientTransport. The item publicly imports it.
The second block is in Sheaf.Paper.IntegralCoefficientCompletenessTransport, publicly
imported by CompletedCoefficientPresentationTransport. Every signature and every
non-theorem construction remains unchanged. The ordinary round-trip existence proof
constructs the identity restriction comparison explicitly, replacing its previous
call to a private helper unavailable in the independent import context. All moved
proofs compile. Two new proved comparison theorems are documented by their new nodes.
The presentation module imports the new module's private restriction-equivalence
helpers for its remaining proofs; their constructions are preserved.

The Roos theorem's Lean signature and sorry body are unchanged. Its public import is:

```lean
public import Sheaf.Paper.IntegralCompletedCoefficientTransport
```

Its node now cites def-sfb-integral-completed-coefficient-transport for the identical
normalized coefficient constructor, instead of citing the parent characterization.
The statement_change records this reference-only correction and all DAG citers.
This removes a false dependency of a constructor on a theorem about membership.

## Users

The prescribed downstream.py audit was run for all three existing modules and all
sixteen moved constructor/comparison base names. All users preserve the same public
signatures, instances and constructions through the original public import paths.
Private proof dependencies introduce no new public assumptions. The following table
contains the full transitive union, including the adapted modules; textual direct
uses are a subset. The mathematical contracts of every unchanged consumer are
therefore identical. The independent reader/global build check the reexports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorTruncationWindow | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | S8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | R1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | P9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos | J4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | R4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionScalarTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldActionTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | T2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusContractionScalarPasting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.IdentityOpenModuleSections | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | W6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | X7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | V1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.PersistentNodeNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComplementSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | W3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion | V4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | B6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeNodalPointPinching | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeSingleTensorCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.TraitEtaleBranchPinching | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Abelian.ModuleSupportedHomTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.BilinearCoefficientDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedActionModule | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedActionTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedBarTotalAugmentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedBarTotalNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedCentralActionDerivedVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedCup | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInflationArrows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInvariantBar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedInvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedEquivariantBarData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedInjectiveBarRows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedInternalBarResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedNormalInvariantData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedProductActionInflation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedProductBarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedRestrictionMateNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedScalarTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedSplitCosetInduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedTensorInductionAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CondensedUnipotentClass | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.ContinuousScalarRing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.CyclicTotalTriangulated | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.DiscreteLatticeCupExterior | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.EquivariantResolutionBarNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalBarFiniteIndexTransfer | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalBarOrderedCup | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalBarRoofAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalFunctionVertexPrism | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.InternalInflationGradedCup | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.LatticeAlgebraDerivedCup | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.LatticeRestrictionCupComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.NormAlgclBarAugmentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.OpenNormalActionInjectiveModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.PointedFreeDeletionContraction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.PolynomialDerivedBarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.PolynomialTranslationAcyclic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.ProfiniteActionParameters | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeBarData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeCyclicRestrictionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeCyclicTotal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeDerivedInvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeInvariantForgetting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeLatticeBridge | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.RelativeTrivialCyclicMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicFiniteExchangeEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AllStageCtfPullbackUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | B8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmbientQcqsExchangeCanonicalShifts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AmplificationProper | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AugmentedIntegralDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BalancedFiniteTowerGeneratorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedFiniteModelGeneration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedFlatCoefficientSiteSquare | M1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BoundedFlatTensorContinuity | B2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CanonicalOpenRestrictionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CanonicalPointScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | B9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CleanOpenUnitParametrizedExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClopenCommonCompactSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion | T9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedTestDerivedExchangeModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedTestKInjectiveSectionModels | M8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedTestLocalizedModelCoherence | E2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ClosedTestUnitEvaluation | Z6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientDualModelTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeart | C6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartCurveComplement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartCurveLisseDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | D2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartLocallyClosedExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | P3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | C5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientRingedSquareNormalization | C9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoefficientScalarTensorRealization | D7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageCalculus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageFiniteHomLifting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageFiniteObjectLifting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageInclusionTensorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonTensorComparisonConstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonTensorComparisonDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CommonTensorComparisonRepresentatives | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactAdicContinuousIdentification | M2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportScalarCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompleteGroupTorsorMonodromy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompleteIntegralResidueFunctor | T2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompleteResidueLineInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientCompletionRoosTransport | unclaimed | Unclaimed adaptation: independent coefficient import; theorem signature and existing hole unchanged. |
| Sheaf.Paper.CompletedCoefficientFamilyTransportModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | unclaimed | Unclaimed adaptation: publicly reexports the independent prefix; remaining signatures and bodies unchanged. |
| Sheaf.Paper.CompletedCoefficientPullbackLinearity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientSystemTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientTensorTransportModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedCoefficientTransportExpressions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedFrameGenericComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedInverseImageScalarCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedLineTensorCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedOpenFiniteTransposeCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedOpenTensorSystemRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedPerfectScalarPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedPullbackUniverseTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedScalarExtensionTExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedSourceAugmentationNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletedUnitPullbackTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ComponentDerivedPullbackSquare | C1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ComponentLiftLisseSectionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CompositeModuleOplaxMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | U8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedERealization | D3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedLocalizationHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | U9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedPointModuleComparison | V1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedScalarFinitePresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CondensedZlReduction | Q4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantModelStratificationTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantSquareZeroTorExample | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleNormedGeometricFibres | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousAlgclScalarConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousCoefficientFreeRank | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralConstructibleComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousQbarLisseHeartClosure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousRepresentationCondensation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ContinuousScalarDerivedEncoding | V8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoordinateBoundaryGeometricPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | W5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DenseLatticeDerivedInvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | D4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | C6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | E5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | E6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | E1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DivisorNormalizedRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DualizingClosedSite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DualizingCompositionCoefficientMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EmbeddedLatticeCoefficientComparison | V9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleIsoDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleSystemCoefficientProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalCommonStageDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExplicitScalarConeWordCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdHomLinearEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdIntegralIdentityRationalEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdNormalizedIntegralCompletionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdPullbackAugmentationCounitMatching | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdPullbackComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FdShiftTriangleReflection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldActionToposCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldLisseStratifiedHeartSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldSeparableCechCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification | D8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteComparisonPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteConstantModelStrataGeneration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteConstantModelsCommonStratification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteConstantStratifiedZariskiLocality | V2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | U3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteScalarConstantModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteFieldClosedSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteFieldHomEtaleWitness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteFreeDualChainComparison | E5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteImageOpenKernelInflation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteMateDomain | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | X7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteOpenProductSwap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePointReconstructedHomModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePrincipalSupportUnitAssembly | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | E8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePullbackStrictTowerData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FinitePullbackTensorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteReductionTowerResolvingModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteRegularCoefficientComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | F2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteScalarLocalModelComplete | X9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | G1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStagePairCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteStrataCompletionDetection | Y6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | E7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FlatCondensedScalarRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FourierAdicCharacterOf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedEtaleHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedForgetSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedProPredicate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedProRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedRealizationAdditive | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedRealizationEnlarge | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedRealizationIso | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedRealizationProperty | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FramedRealizationPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterDegreeZeroData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterEvaluationCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterEvaluationData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterMatrixCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterRelativeMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FreeParameterScalarMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | E9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GenericLisseScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | E8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | F5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ImmersionResidueTorIntervals | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndUnipotentProcyclicDifference | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IndUnipotentSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAdicHomCompleteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralAugmentedQuotientTowers | Y7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCoefficientModelRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | Y8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | E9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompletedTowerPullbackUniverses | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHomSums | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | G7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | J7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpSequentialContinuity | G4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralImmersionPullbackNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralLocalizationHomColimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralModels | J8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralModelsExtensionClosed | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | V1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralObjectPullbackLine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackShiftCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | F6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | J9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | K5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | K9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | H1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientResolutionNormalization | H2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | H3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | K7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | A3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralScalarConstructibleImage | E2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | Q3 | Q3 item: reexports the coefficient block and proves the remaining detailed comparison. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTStructure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTensorComparisonSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalDerivedClosedLocalization | F7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalDirectImageLaxRealization | E4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalScalarMateTransitivity | J4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalScalarProjectionMate | K1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalScalarPullbackNormalization | K2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | K3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonNatural | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismFieldTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.IteratedReturnTransportScalarCalculus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerBarResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerNormalizedComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerProductShearHomotopy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerProductUnitPermutation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerResolutionColumns | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerScalarRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.KummerTermMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseLatticeReducedOpen | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseOpenUnitTestDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalModelTorBoundDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.LocallyFiniteCoefficientRingRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModuleDerivedFunctorCompositorShifts | P2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModuleDerivedFunctorShifts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | M2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbySpecializationSlice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | M3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NoetherianStratifiedModelProductEmbedding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | F8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormAlgclCohomologyTopologyComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalGenericLisseCocycle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.NormedCoefficientRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenCompletedRestrictionIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenExtensionConstructibleFiniteTor | W4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenInternalKFlatMateNormalization | F9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenRestrictionCompleteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenSquareClosedUnitTriangle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrdinaryDerivedProductLegTransposes | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrdinaryImmersionChartComparison | P1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | C7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ParameterRootBoundaryData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcAutomorphismTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcConeIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDescentInterfaces | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDirectImageCoherentFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDirectImageFamilyExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDirectImageFamilyShiftCompatible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDirectImageStageExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcExchangeCompatibleFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcExchangeStageSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcFiniteStageKaroubian | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcPairFunctorShiftCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcPullbackCoherentFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcQbarCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcQbarCompletedPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcQbarIdempotentComplete | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcScalarExtension | C1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PerAdicCommonStageTruncations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PodCounitScalarWordCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointAutomorphismDerivedTransportInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointAutomorphismRestrictionNatural | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointCompositeComparisonTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointEvaluationCompletionNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFieldTensorDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointFiniteTensorComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointIntegralCompletedTensorComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointIntegralPerfectRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointIntegralSectionsConservative | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointInverseImageCoefficientTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointPullbackDerivedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointPullbackRepresentativeDiagram | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointQbarFibreShiftDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRationalFamilyCommonStageNaturality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRationalFibreExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRationalSectionsHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRationalSectionsLattice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointRestrictionOrdinaryTensorSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointScalarCompatibleTransportTransfer | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointTateRootCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointTorAmplitudeRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PointTransformationRationalNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PreservationConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PrimeToEllDerivedInvariantsReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PrincipalReductionDerivedNormalization | Q8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtalePfAdmissibleModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives | U2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | G7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | A9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProfiniteConstantDerivedFunctions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProfiniteDerivedEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProfiniteDerivedFunctionsFilteredColimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProfiniteFreeSliceDerivedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | H5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | A2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperIntegralOrdinaryInputs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | Y8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ProperWContractibleClosedFibreRigidity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PullbackCommonStrictTowerModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PulledKoszulTowerChainComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PulledKoszulTowerNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PulledReductionNormalizationComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurIntegralReductionUniformTor | M4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | H6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.PurityZeroSupportRetractionTriangle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarProperBaseChange | G1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor | X3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | H8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | B3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | B4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsLisseStratifiedIntegralLattices | A3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | N1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsProperSerreHeartBound | R5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | Y2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QlbarBoundedTensorColimit | N2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | M7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | P7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QlbarTailFiniteFreeAlgebraPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientCompletedCompositorUnit | K3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientExpressionStrictKFlatTowers | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | N3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientSectionTensorNormalization | N4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.QuotientTensorInsertion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonDatum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonScalarSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonStageSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonStructures | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonTransition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonTransitionTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalComparisonValid | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalLatticeAdicDomain | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalLocallyFree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalRestrictionComparisonCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalStratumIntegralModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RationalTensorComparisonSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealSheafSections | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealWeilSheaves | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationAdjointComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationCoefficientSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationCompletedImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationCompletedPullData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationLocalizedPush | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationPullOrdinarySystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationPullRationalDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationRestrictionNormalizations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationScalarFunctor | J5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizationScalarPushMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RealizedPullbackComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | S7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootCoordinateSupportedVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerCoordinateFace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerFiniteTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.RootTowerPunctureInvariance | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarChangeDirectImageUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | P9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarModelRestrictionCriterion | P1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | J8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | Z6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorNormalization | Y7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionKFlatTensorComparison | D4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionOplaxTotalComparison | E3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | J9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SectionwiseOpenLisseHomDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SequenceScalarGeneratorInterchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCommonStageFullFaithfulness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCompleteDirectImageReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCompletedAugmentationAdjunct | K5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | P4 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfExactPullbackQuotientAugmentationSquare | K6 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfExceptionalReductionTransitions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfFrameworkCommonStageDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfFrameworkThetaShiftCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | Q9 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralOrdinaryRecollementRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalSupportedAdjointTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SignedTwistSiteTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SpectralFiniteEtaleTraceLattice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | C8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedDualizableBounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedDualizableHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedLatticeScheme | C3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | F2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedClassEvaluationComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedTensorIsomorphismTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedTorReductionPropagation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameBoundaryScalarComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameInertiaContinuousKoszul | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameInertiaScalarMate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TensorComparisonLocalizationDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TorsionAcyclicNormCoefficientTest | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TowerOperationsGroundFieldRetagging | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TrivialLadicDerivedExterior | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TwoOpenTensorChainNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WContractibleComponentDerivedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WStrictLisseComponentCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilInternalHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WeilTensorWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.PoincareDuality.OpenModuleBalancedProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.RepresentationTheory.ProcyclicScalarCochainEvaluation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization | D8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | D3 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification | Q2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | H2 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | Q1 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteEtaleOpenUniformTorImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeImageComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | T5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares | M5 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | T7 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | S8 | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Topology.ContinuousAbelianProfiniteSheaf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Topology.ContinuousModulePresheafCoordinates | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.Topology.TopologicalModuleCondensation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.IsomorphismRoosUnitCancellation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.NodalChartBoundaryShrinking | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.PointExactRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ScalarModelUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StrictQuotientCompletionUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.StrictQuotientConeAugmentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.TraceFormula.WeilUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.DerivedHomSingleResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.NativeBasicComparisons | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.NativeCompactificationModelComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.NativeCompatibleTowerCalculation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| Sheaf.WeilSheaf.ProperSheafFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| TargetsCheck | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.AdicReconstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImageReduction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionSMulUpperStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIntegrality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeKernel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSemilinear | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerShriekFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFiniteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFinitenessStratum | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissageRegular | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | D4 | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BaseChangeField.Cohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BaseChangeField.Comparison | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ClosedLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstant | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantExt | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyNonneg | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyProEtale | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyResolution | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CompactSupportAdicConstant | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FieldCoefficientFrobeniusTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.FrobeniusTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IntegralCoefficientCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TensorHomAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceCupAdicConstant | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same public declarations and constructions via reexports; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same public declarations and constructions via reexports; no adaptation. |

## Status

landed 20261024T015708-L-2438656 2026-10-24 (merge of deliver/Q3/Sheaf.Paper.IntegralStratifiedPerfectCharacterization)
