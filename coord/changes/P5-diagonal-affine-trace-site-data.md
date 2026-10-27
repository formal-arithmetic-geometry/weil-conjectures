# Diagonal affine trace site-comparison data extraction

## Reason

The main theorem is reduced to three proper geometric steps: actual-map agreement,
the integration site square, and the independent rank-zero identity normalization.
Their signatures use the existing MapAgreement, TraceSquare and RankZeroActual
predicates. Move the existing data block to a shared preceding module to avoid an
import cycle between the assembly theorem and those statements.
All existing public names, signatures, attributes, definition bodies, auxiliary
proofs and public imports are preserved through public reexport. No target changes.
This repair rebases the extraction onto the current source, including Z7's existing
auxiliary proofs. It replaces the stale old/new blocks from returned head a82f51e13.
The delivery file is coord/changes/P5-diagonal-affine-trace-site-data.md;
reviewer fixes must use this full repository-relative path, rather than its basename.

## Old

The following current-source block belongs to
Sheaf.Paper.DiagonalAffineTraceSiteComparison.

```lean
section Original
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
  [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
  (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
  (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K)


/-- Re-expressing the actual integration in the datum's scalar coordinates is unique.
HEq fixes the map, and only definitionally equal endpoint presentations differ.
Source: the finite coefficient-source comparison
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: unfold projectionSetting, its Coefficient and finiteTateCoefficient; they
are the same lifted coefficient quotient with the same ring structure. Unfold the
source support and tensor aliases. The two Hom types coincide, including the chosen
compactification, whose instance is a proposition. Transport the actual proIntegration
along these endpoint equalities. HEq fixes the transported arrow uniquely. -/
theorem integrationInput_existsUnique (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (C.l : Γ(S, ⊤)))
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) :
    ∃! a : IntegrationInput (projectionSetting F C E n) S (C.l ^ (r + 1)) hA d Ke,
      HEq a (proIntegration F C E n S hS r hA d Ke hKe) := by
  refine ⟨proIntegration F C E n S hS r hA d Ke hKe, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha


/-- The canonical scalar-coordinate transport of the actual integration.
Its unique specification fixes the original map, with no purity map involved.
Source: finite coefficient-source coordinates
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def integrationInput (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (C.l : Γ(S, ⊤)))
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) :
    IntegrationInput (projectionSetting F C E n) S (C.l ^ (r + 1)) hA d Ke :=
  projectionChooseUnique (integrationInput_existsUnique F C E n S hS Ke hKe r hA d)


/-- The original diagonal purity and smooth trace, with only their computed endpoints
retained in Sigma types. These are exactly the recorded maps on the original K.
Source: gamma and s in the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def actualMaps (d : ℕ) : MapPair (projectionSetting F C E n) S aS K d :=
  let P := projectionSetting F C E n
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : S.Over (Spec (.of F.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of F.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of F.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact aS)
  letI : LocallyOfFiniteType (X ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aS))
  letI : QuasiCompact (X ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of F.k)) := ⟨rfl⟩
  letI := projectionSmooth S d
  ((⟨_, _, P.smoothPurityMap f d K hK⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N),
    (⟨_, P.coefficientValuedSmoothTrace f d K hK⟩ :
      Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K))


/-- Integration and its ordinary transpose transported to the original intrinsic K.
No purity map enters these arrows. The exceptional comparison is the image of the
comparison unit, hence preserves the actual exceptional counit. The compact-support
map is the proper counit mate after open extension, followed by sourceCoordinates.
Source: a^p, C_V(eta^e), beta and its source identification
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def transportedMaps
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) : MapPair (projectionSetting F C E n) S aS K d :=
  let P := projectionSetting F C E n
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) := ProEtale.AffineLinePurity.primeUnit P S aS
  transportCoordinates P S aS (C.l ^ (r + 1)) (pow_pos C.prime.out.pos _) hA
    (powerUnit C.l S hS r) K Ke eK d
    (exponentIso F C E n r hA d (affineTraceTower S d)
      (ProEtale.AffineLinePurity.primeUnit P _ (affineTraceProjection S d ≫ aS)))
    (integrationInput F C E n S hS Ke hKe r hA d)

end Original

section Comparison
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
  [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]


private theorem baseCoefficient_bounded (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    DerivedCategory.TStructure.t.bounded (Etale.affineLinearBaseCoefficient A N hA T d) := by
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist T N A hA 1) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line T N hN
      (fun x ↦ by
        simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom)
      A hA 1).2.2.1
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat
  have hshift := Etale.DerivedCategory.torAmplitudeIn.shift ht (2 : ℤ)
  induction d with
  | zero =>
    change DerivedCategory.TStructure.t.bounded (Etale.ordinaryFiniteUnit A T)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  | succ d ih =>
    exact Etale.bounded_derivedTensor_of_finiteTorAmplitude (ModuleCat.{u + 1} A) T ih
      ⟨_, _, hshift⟩


/-- Every ordinary finite-Tor constructible coefficient and its affine Tate pullback
are bounded below; this supplies applicability proofs, not extra hypotheses.
Source: K_0 in D^b_ctf and the displayed twisted pullback
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: bounded constructibility gives a lower cohomological bound on K. Exact
inverse image preserves it. Tensor with the locally free shifted root line
translates this bound by -2d. Invertibility of ell follows from ell different
from the characteristic; this applies also to the empty scheme and d=0. -/
theorem ordinaryPlus
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (_hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke) :
    DerivedCategory.TStructure.t.plus Ke ∧
      ∀ (r : ℕ)
        (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0)
        (d : ℕ),
        DerivedCategory.TStructure.t.plus
          (OrdinarySource (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1))
            hA S d Ke) := by
  obtain ⟨_, a, b, _, hv⟩ := _hKe.1
  have hb : DerivedCategory.TStructure.t.bounded Ke :=
    ⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  refine ⟨hb.1, ?_⟩
  intro r hA d
  let A := Scheme.finiteTateCoefficient C.l E n
  let T := affineTraceTower S d
  let f := affineTraceProjection S d
  let B := Etale.affineLinearBaseCoefficient A (C.l ^ (r + 1)) hA T d
  have hT : IsUnit (C.l : Γ(T, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) T (f ≫ aS)
  have hB : DerivedCategory.TStructure.t.bounded B :=
    baseCoefficient_bounded A _ (pow_pos C.prime.out.pos _) hA T
      (powerUnit C.l T hT r) d
  obtain ⟨c, e, _, htor⟩ := _hKe.2
  have ht := Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) f c e
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htor)
  have hbound := Etale.bounded_derivedTensor_of_finiteTorAmplitude
    (ModuleCat.{u + 1} A) T hB ⟨c, e, ht⟩
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).app B).app
      ((Etale.ordinaryFinitePullback A f).obj Ke)) hbound.1


/-- Equality of the original intrinsic maps with the canonical transported arrows.
Source: s=a^p and gamma=C_V(eta^e) with their specified source identifications
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def MapAgreement
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    Prop :=
  SameMaps (projectionSetting F C E n) S aS K d
    (actualMaps F C E n S aS K hK d)
    (transportedMaps F C E n S aS K Ke hKe eK r hA d)


/-- The actual integration square under the canonical compact-support comparison.
Source: a^p beta = C_S(a^e)
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def TraceSquare
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0)
    (d : ℕ) : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) S aS
  IntegrationSiteSquare (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1))
    (pow_pos C.prime.out.pos _) hA S (powerUnit C.l S hS r) d Ke
    ((ordinaryPlus F C E n S aS Ke hKe).2 r hA d)
    (proIntegration F C E n S hS r hA d Ke hKe)


/-- The canonical identity-pullback tensor-unit isomorphism in its computed endpoints.
Source: the rank-zero source-unit identification
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroUnitSource
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (Ke : Etale.DerivedCategoryModule A S) :=
  ((Etale.ordinaryFiniteTensor A S).mapIso
    ((Etale.affineLinearPullbackId A S).app Ke)).app (Etale.ordinaryFiniteUnit A S) ≪≫
      ((Etale.ordinaryFiniteTensor A S).obj Ke).mapIso (smoothPurityUnitIso A S) ≪≫
        Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) S Ke

/-- The empty affine source has the uniquely specified identity/unit isomorphism.
Source: the d=0 normalization of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: unfold OrdinarySource at zero. The affine tower is S, its projection is
identity, and affineLinearBaseCoefficient at zero is the ordinary coefficient unit.
Thus its source is definitionally the computed source of rankZeroUnitSource.
Transport that isomorphism along this equality; heterogeneous equality fixes it uniquely. -/
theorem rankZeroOrdinarySource_existsUnique
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (Ke : Etale.DerivedCategoryModule A S) :
    ∃! e : OrdinarySource A N hA S 0 Ke ≅ Ke, HEq e (rankZeroUnitSource A S Ke) := by
  refine ⟨rankZeroUnitSource A S Ke, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The rank-zero ordinary source identified with K by identity pullback and its tensor unit.
Source: the d=0 normalization of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroOrdinarySource
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (Ke : Etale.DerivedCategoryModule A S) :
    OrdinarySource A N hA S 0 Ke ≅ Ke :=
  projectionChooseUnique (rankZeroOrdinarySource_existsUnique A N hA S Ke)

/-- The canonical compact-support identity: forget supports for the proper identity
and identify its ordinary derived direct image with the identity functor.
Source: p_0=id and the identity-adjunction normalization
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroOrdinarySupport
    (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    [HasCompactification (𝟙 S)] (Ke : Etale.DerivedCategoryModule A S) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)).obj Ke ≅ Ke :=
  ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (𝟙 S)) ≪≫ Etale.rightDerivedLowerStarIdIso A S).app Ke

/-- Canonical rank-zero identity arrows in the actual intrinsic endpoints.
The purity arrow uses only identity pullback, tensor unit and the ordinary exceptional
identity isomorphism. The trace arrow uses only these source coordinates, the proper/open
support comparison, the identity compact-support isomorphism and realization counit.
Thus neither arrow uses smooth purity, an ordered trace or a tower-counit equation.
Source: the d=0 purity and trace identities
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroMaps
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    MapPair (projectionSetting F C E n) S aS K 0 :=
  let P := projectionSetting F C E n
  let N := C.l ^ (r + 1)
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  letI : S.Over (Spec (.of F.k)) := ⟨aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of F.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact aS)
  letI : (affineTraceTower S 0).Over (Spec (.of F.k)) :=
    ⟨affineTraceProjection S 0 ≫ aS⟩
  letI : LocallyOfFiniteType (affineTraceTower S 0 ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection S 0 ≫ aS))
  letI : QuasiCompact (affineTraceTower S 0 ↘ Spec (.of F.k)) :=
    inferInstanceAs (QuasiCompact (affineTraceProjection S 0 ≫ aS))
  letI : (affineTraceProjection S 0).IsOver (Spec (.of F.k)) := ⟨rfl⟩
  let ES := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let hS := ProEtale.AffineLinePurity.primeUnit P S aS
  let e := sourceCoordinates P S 0 (ES.inverse.obj K) Ke eK _
    (exponentIso F C E n r hA 0 S hS)
  let e0 := rankZeroOrdinarySource P.Coefficient N hA S Ke
  let η0 := e0.hom ≫
    ((Etale.rightDerivedUpperShriekIsoOfIso
      (ModuleCat.{u + 1} P.Coefficient) (Iso.refl S)) ≪≫
        Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) S).inv.app Ke
  let η := e.hom ≫ (comparison P.Coefficient S).map η0 ≫
    ProEtale.boundedSiteRho P.Coefficient
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) (𝟙 S)) Ke ≫
    (P.smoothPurityExceptionalOver (𝟙 S) aS).map eK.hom
  let a0 := (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
    (𝟙 S)).map e0.hom ≫
      (rankZeroOrdinarySupport P.Coefficient S Ke).hom
  let a := (P.smoothCompactSupport (affineTraceProjection S 0)).map
      (ES.functor.map e.hom) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification (affineTraceProjection S 0))).hom.app _ ≫
    ES.functor.map
      ((ProEtale.compactSupportSiteComparison P.Coefficient
        (HasCompactification.compactification (affineTraceProjection S 0))).hom.app
          ⟨_, (ordinaryPlus F C E n S aS Ke hKe).2 r hA 0⟩ ≫
        (comparison P.Coefficient S).map a0) ≫
    ES.functor.map eK.hom ≫ ES.counitIso.hom.app K
  ((⟨_, _, ES.functor.map η⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory S P.Ring, M ⟶ N),
    (⟨_, a⟩ : Σ M : Scheme.proEtaleDerivedCategory S P.Ring,
      (P.smoothCompactSupport (affineTraceProjection S 0)).obj M ⟶ K))


/-- The actual diagonal purity and actual smooth trace at rank zero are identities
under the independently specified canonical unit and identity-adjunction coordinates.
Source: the d=0 clause of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def RankZeroActual
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    Prop :=
  SameMaps (projectionSetting F C E n) S aS K 0
    (actualMaps F C E n S aS K hK 0)
    (rankZeroMaps F C E n S aS K Ke hKe eK r hA)


/-- The actual affine trace equality and its site and transpose comparisons.
The universal presentation is only a choice of coordinates for the original K.
HEq retains endpoints computed by the recorded maps; sourceCoordinates and the relative
counit-mate comparison specify all endpoint identifications independently of purity.
Source: all clauses of the diagonal affine-model trace statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def Conclusion
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ) : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) S aS
  ∀ (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0),
    MapAgreement F C E n S aS K hK d Ke hKe eK r hA ∧
    TraceSquare F C E n S aS Ke hKe r hA d ∧
    ProjectiveNormalization C.l E n S hS r hA ∧
    RankZeroActual F C E n S aS K hK Ke hKe eK r hA


```

## New

The identical block now belongs to Sheaf.Paper.DiagonalAffineTraceSiteData.
The item publicly imports it, preserving downstream visibility.

```lean
section Original
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
  [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
  (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
  (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K)


/-- Re-expressing the actual integration in the datum's scalar coordinates is unique.
HEq fixes the map, and only definitionally equal endpoint presentations differ.
Source: the finite coefficient-source comparison
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: unfold projectionSetting, its Coefficient and finiteTateCoefficient; they
are the same lifted coefficient quotient with the same ring structure. Unfold the
source support and tensor aliases. The two Hom types coincide, including the chosen
compactification, whose instance is a proposition. Transport the actual proIntegration
along these endpoint equalities. HEq fixes the transported arrow uniquely. -/
theorem integrationInput_existsUnique (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (C.l : Γ(S, ⊤)))
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) :
    ∃! a : IntegrationInput (projectionSetting F C E n) S (C.l ^ (r + 1)) hA d Ke,
      HEq a (proIntegration F C E n S hS r hA d Ke hKe) := by
  refine ⟨proIntegration F C E n S hS r hA d Ke hKe, HEq.rfl, ?_⟩
  intro a ha
  exact eq_of_heq ha


/-- The canonical scalar-coordinate transport of the actual integration.
Its unique specification fixes the original map, with no purity map involved.
Source: finite coefficient-source coordinates
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def integrationInput (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (C.l : Γ(S, ⊤)))
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) :
    IntegrationInput (projectionSetting F C E n) S (C.l ^ (r + 1)) hA d Ke :=
  projectionChooseUnique (integrationInput_existsUnique F C E n S hS Ke hKe r hA d)


/-- The original diagonal purity and smooth trace, with only their computed endpoints
retained in Sigma types. These are exactly the recorded maps on the original K.
Source: gamma and s in the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def actualMaps (d : ℕ) : MapPair (projectionSetting F C E n) S aS K d :=
  let P := projectionSetting F C E n
  let X := affineTraceTower S d
  let f := affineTraceProjection S d
  letI : S.Over (Spec (.of F.k)) := ⟨aS⟩
  letI : X.Over (Spec (.of F.k)) := ⟨f ≫ aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of F.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact aS)
  letI : LocallyOfFiniteType (X ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (f ≫ aS))
  letI : QuasiCompact (X ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact (f ≫ aS))
  letI : f.IsOver (Spec (.of F.k)) := ⟨rfl⟩
  letI := projectionSmooth S d
  ((⟨_, _, P.smoothPurityMap f d K hK⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory X P.Ring, M ⟶ N),
    (⟨_, P.coefficientValuedSmoothTrace f d K hK⟩ :
      Σ M : Scheme.proEtaleDerivedCategory X P.Ring, (P.smoothCompactSupport f).obj M ⟶ K))


/-- Integration and its ordinary transpose transported to the original intrinsic K.
No purity map enters these arrows. The exceptional comparison is the image of the
comparison unit, hence preserves the actual exceptional counit. The compact-support
map is the proper counit mate after open extension, followed by sourceCoordinates.
Source: a^p, C_V(eta^e), beta and its source identification
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def transportedMaps
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0)
    (d : ℕ) : MapPair (projectionSetting F C E n) S aS K d :=
  let P := projectionSetting F C E n
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) := ProEtale.AffineLinePurity.primeUnit P S aS
  transportCoordinates P S aS (C.l ^ (r + 1)) (pow_pos C.prime.out.pos _) hA
    (powerUnit C.l S hS r) K Ke eK d
    (exponentIso F C E n r hA d (affineTraceTower S d)
      (ProEtale.AffineLinePurity.primeUnit P _ (affineTraceProjection S d ≫ aS)))
    (integrationInput F C E n S hS Ke hKe r hA d)

end Original

section Comparison
variable (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
  [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]


private theorem baseCoefficient_bounded (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    DerivedCategory.TStructure.t.bounded (Etale.affineLinearBaseCoefficient A N hA T d) := by
  have hflat : ObjectProperty.flat (Scheme.finiteEtaleTateTwist T N A hA 1) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line T N hN
      (fun x ↦ by
        simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom)
      A hA 1).2.2.1
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat
  have hshift := Etale.DerivedCategory.torAmplitudeIn.shift ht (2 : ℤ)
  induction d with
  | zero =>
    change DerivedCategory.TStructure.t.bounded (Etale.ordinaryFiniteUnit A T)
    exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  | succ d ih =>
    exact Etale.bounded_derivedTensor_of_finiteTorAmplitude (ModuleCat.{u + 1} A) T ih
      ⟨_, _, hshift⟩


/-- Every ordinary finite-Tor constructible coefficient and its affine Tate pullback
are bounded below; this supplies applicability proofs, not extra hypotheses.
Source: K_0 in D^b_ctf and the displayed twisted pullback
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: bounded constructibility gives a lower cohomological bound on K. Exact
inverse image preserves it. Tensor with the locally free shifted root line
translates this bound by -2d. Invertibility of ell follows from ell different
from the characteristic; this applies also to the empty scheme and d=0. -/
theorem ordinaryPlus
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (_hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke) :
    DerivedCategory.TStructure.t.plus Ke ∧
      ∀ (r : ℕ)
        (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0)
        (d : ℕ),
        DerivedCategory.TStructure.t.plus
          (OrdinarySource (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1))
            hA S d Ke) := by
  obtain ⟨_, a, b, _, hv⟩ := _hKe.1
  have hb : DerivedCategory.TStructure.t.bounded Ke :=
    ⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hv i (Or.inr hi))⟩⟩
  refine ⟨hb.1, ?_⟩
  intro r hA d
  let A := Scheme.finiteTateCoefficient C.l E n
  let T := affineTraceTower S d
  let f := affineTraceProjection S d
  let B := Etale.affineLinearBaseCoefficient A (C.l ^ (r + 1)) hA T d
  have hT : IsUnit (C.l : Γ(T, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) T (f ≫ aS)
  have hB : DerivedCategory.TStructure.t.bounded B :=
    baseCoefficient_bounded A _ (pow_pos C.prime.out.pos _) hA T
      (powerUnit C.l T hT r) d
  obtain ⟨c, e, _, htor⟩ := _hKe.2
  have ht := Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) f c e
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htor)
  have hbound := Etale.bounded_derivedTensor_of_finiteTorAmplitude
    (ModuleCat.{u + 1} A) T hB ⟨c, e, ht⟩
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).app B).app
      ((Etale.ordinaryFinitePullback A f).obj Ke)) hbound.1


/-- Equality of the original intrinsic maps with the canonical transported arrows.
Source: s=a^p and gamma=C_V(eta^e) with their specified source identifications
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def MapAgreement
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    Prop :=
  SameMaps (projectionSetting F C E n) S aS K d
    (actualMaps F C E n S aS K hK d)
    (transportedMaps F C E n S aS K Ke hKe eK r hA d)


/-- The actual integration square under the canonical compact-support comparison.
Source: a^p beta = C_S(a^e)
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def TraceSquare
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0)
    (d : ℕ) : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) S aS
  IntegrationSiteSquare (Scheme.finiteTateCoefficient C.l E n) (C.l ^ (r + 1))
    (pow_pos C.prime.out.pos _) hA S (powerUnit C.l S hS r) d Ke
    ((ordinaryPlus F C E n S aS Ke hKe).2 r hA d)
    (proIntegration F C E n S hS r hA d Ke hKe)


/-- The canonical identity-pullback tensor-unit isomorphism in its computed endpoints.
Source: the rank-zero source-unit identification
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroUnitSource
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (Ke : Etale.DerivedCategoryModule A S) :=
  ((Etale.ordinaryFiniteTensor A S).mapIso
    ((Etale.affineLinearPullbackId A S).app Ke)).app (Etale.ordinaryFiniteUnit A S) ≪≫
      ((Etale.ordinaryFiniteTensor A S).obj Ke).mapIso (smoothPurityUnitIso A S) ≪≫
        Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} A) S Ke

/-- The empty affine source has the uniquely specified identity/unit isomorphism.
Source: the d=0 normalization of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
Proof: unfold OrdinarySource at zero. The affine tower is S, its projection is
identity, and affineLinearBaseCoefficient at zero is the ordinary coefficient unit.
Thus its source is definitionally the computed source of rankZeroUnitSource.
Transport that isomorphism along this equality; heterogeneous equality fixes it uniquely. -/
theorem rankZeroOrdinarySource_existsUnique
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (Ke : Etale.DerivedCategoryModule A S) :
    ∃! e : OrdinarySource A N hA S 0 Ke ≅ Ke, HEq e (rankZeroUnitSource A S Ke) := by
  refine ⟨rankZeroUnitSource A S Ke, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The rank-zero ordinary source identified with K by identity pullback and its tensor unit.
Source: the d=0 normalization of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroOrdinarySource
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (Ke : Etale.DerivedCategoryModule A S) :
    OrdinarySource A N hA S 0 Ke ≅ Ke :=
  projectionChooseUnique (rankZeroOrdinarySource_existsUnique A N hA S Ke)

/-- The canonical compact-support identity: forget supports for the proper identity
and identify its ordinary derived direct image with the identity functor.
Source: p_0=id and the identity-adjunction normalization
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroOrdinarySupport
    (A : Type (u + 1)) [CommRing A] [Finite A] (S : Scheme.{u})
    [HasCompactification (𝟙 S)] (Ke : Etale.DerivedCategoryModule A S) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)).obj Ke ≅ Ke :=
  ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
    (ModuleCat.{u + 1} A) (𝟙 S)) ≪≫ Etale.rightDerivedLowerStarIdIso A S).app Ke

/-- Canonical rank-zero identity arrows in the actual intrinsic endpoints.
The purity arrow uses only identity pullback, tensor unit and the ordinary exceptional
identity isomorphism. The trace arrow uses only these source coordinates, the proper/open
support comparison, the identity compact-support isomorphism and realization counit.
Thus neither arrow uses smooth purity, an ordered trace or a tower-counit equation.
Source: the d=0 purity and trace identities
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def rankZeroMaps
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    MapPair (projectionSetting F C E n) S aS K 0 :=
  let P := projectionSetting F C E n
  let N := C.l ^ (r + 1)
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  letI : S.Over (Spec (.of F.k)) := ⟨aS⟩
  letI : LocallyOfFiniteType (S ↘ Spec (.of F.k)) := inferInstanceAs (LocallyOfFiniteType aS)
  letI : QuasiCompact (S ↘ Spec (.of F.k)) := inferInstanceAs (QuasiCompact aS)
  letI : (affineTraceTower S 0).Over (Spec (.of F.k)) :=
    ⟨affineTraceProjection S 0 ≫ aS⟩
  letI : LocallyOfFiniteType (affineTraceTower S 0 ↘ Spec (.of F.k)) :=
    inferInstanceAs (LocallyOfFiniteType (affineTraceProjection S 0 ≫ aS))
  letI : QuasiCompact (affineTraceTower S 0 ↘ Spec (.of F.k)) :=
    inferInstanceAs (QuasiCompact (affineTraceProjection S 0 ≫ aS))
  letI : (affineTraceProjection S 0).IsOver (Spec (.of F.k)) := ⟨rfl⟩
  let ES := Scheme.sfIntrinsicDerivedEquivalence S P.Ring
  let hS := ProEtale.AffineLinePurity.primeUnit P S aS
  let e := sourceCoordinates P S 0 (ES.inverse.obj K) Ke eK _
    (exponentIso F C E n r hA 0 S hS)
  let e0 := rankZeroOrdinarySource P.Coefficient N hA S Ke
  let η0 := e0.hom ≫
    ((Etale.rightDerivedUpperShriekIsoOfIso
      (ModuleCat.{u + 1} P.Coefficient) (Iso.refl S)) ≪≫
        Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) S).inv.app Ke
  let η := e.hom ≫ (comparison P.Coefficient S).map η0 ≫
    ProEtale.boundedSiteRho P.Coefficient
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) (𝟙 S)) Ke ≫
    (P.smoothPurityExceptionalOver (𝟙 S) aS).map eK.hom
  let a0 := (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
    (𝟙 S)).map e0.hom ≫
      (rankZeroOrdinarySupport P.Coefficient S Ke).hom
  let a := (P.smoothCompactSupport (affineTraceProjection S 0)).map
      (ES.functor.map e.hom) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring
      (HasCompactification.compactification (affineTraceProjection S 0))).hom.app _ ≫
    ES.functor.map
      ((ProEtale.compactSupportSiteComparison P.Coefficient
        (HasCompactification.compactification (affineTraceProjection S 0))).hom.app
          ⟨_, (ordinaryPlus F C E n S aS Ke hKe).2 r hA 0⟩ ≫
        (comparison P.Coefficient S).map a0) ≫
    ES.functor.map eK.hom ≫ ES.counitIso.hom.app K
  ((⟨_, _, ES.functor.map η⟩ :
      Σ M N : Scheme.proEtaleDerivedCategory S P.Ring, M ⟶ N),
    (⟨_, a⟩ : Σ M : Scheme.proEtaleDerivedCategory S P.Ring,
      (P.smoothCompactSupport (affineTraceProjection S 0)).obj M ⟶ K))


/-- The actual diagonal purity and actual smooth trace at rank zero are identities
under the independently specified canonical unit and identity-adjunction coordinates.
Source: the d=0 clause of the affine-model statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
def RankZeroActual
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    Prop :=
  SameMaps (projectionSetting F C E n) S aS K 0
    (actualMaps F C E n S aS K hK 0)
    (rankZeroMaps F C E n S aS K Ke hKe eK r hA)


/-- The actual affine trace equality and its site and transpose comparisons.
The universal presentation is only a choice of coordinates for the original K.
HEq retains endpoints computed by the recorded maps; sourceCoordinates and the relative
counit-mate comparison specify all endpoint identifications independently of purity.
Source: all clauses of the diagonal affine-model trace statement
(blueprint: lem-pur-diagonal-affine-trace-site-comparison). -/
@[irreducible]
def Conclusion
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ) : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  let hS : IsUnit (C.l : Γ(S, ⊤)) :=
    ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) S aS
  ∀ (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0),
    MapAgreement F C E n S aS K hK d Ke hKe eK r hA ∧
    TraceSquare F C E n S aS Ke hKe r hA d ∧
    ProjectiveNormalization C.l E n S hS r hA ∧
    RankZeroActual F C E n S aS K hK Ke hKe eK r hA


```

## Users

`python3 tools/downstream.py Sheaf.Paper.DiagonalAffineTraceSiteComparison
--uses diagonalAffineTraceSiteComparison` reports zero downstream modules. A source
search finds only the item defining the named public predicates; there are no current
Lean consumers to adapt. DAG parents still need the item and are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | P5 | Publicly reexports every moved declaration; assembles the three steps and projective normalization. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | P5, new | Owns the existing data and three proved auxiliary theorems. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | P5, new | Uses the shared actual-map predicates. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | P5, new | Uses the shared integration square. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | P5, new | Uses the shared identity normalization predicate. |

## Status

landed 20261025T164021-L-937086 2026-10-25 (merge of deliver/P5/Sheaf.Paper.DiagonalAffineTraceSiteComparison)
