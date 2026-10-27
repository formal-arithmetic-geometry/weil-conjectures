# Finite exceptional construction block

## Reason

The two proper quotient obligations must import the original definitions without importing
the theorem that uses them. Move the existing construction block to
Sheaf.SixFunctors.FiniteExceptionalData and publicly re-export it from the item.
This breaks a would-be import cycle; it is not a split to evade a compile limit.
All original signatures and data bodies remain verbatim. The proofs of quotient_comp
and quotient_id use a private specialization equality to avoid repeatedly unfolding
constant-sheafification in kernel checking. Local irreducibility
annotations in the data file prevent elaboration from unfolding derived functor choices;
these affect only its proofs and elaboration, not the exported mathematical data.

## Old

The following construction block was in Sheaf.SixFunctors.FiniteExceptional:

```lean
/-- The existing positive-level finite-Tor constructible predicate.
Source: blueprint finite-Tor domain (blueprint: lem-coef-finite-exceptional). -/
abbrev domain (T : Scheme.{u}) (n : ℕ) :
    ObjectProperty (proEtaleDerivedCategory T
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T

/-- Actual quotient scalar extension, before restriction to finite Tor.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
abbrev reduction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (m + 1)) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  pbcDerivedExtend ((PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1)).map T)

attribute [local irreducible] reductionDerivedChange in
/-- Finite-Tor constructibility survives the actual quotient tensor.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: apply the arbitrary finite-ring scalar-extension theorem to the actual quotient
map. Its bounded flat model remains flat in the same interval after scalar extension.
The scalar-extension constructibility theorem supplies the constructible cohomology;
the Tor interval also bounds its cohomological support. The scalar functor is exactly
the published derived quotient tensor, including equal indices. -/
theorem reduction_preserves (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : (domain l E T m).FullSubcategory) :
    domain l E T n ((reduction l E T h).obj K.obj) := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos m)
  have : Finite B := Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos n)
  let φ : A →+* B := compactSupportLevelQuotient l E m n h
  have hF : reduction l E T h = ProEtale.scalarExtensionFunctor φ T := by
    apply congrArg (reductionDerivedChange T)
    rfl
  rw [hF]
  obtain ⟨⟨hb, hc⟩, a, b, ht⟩ := K.property
  have ht' := ProEtale.scalarExtension_tor φ T K.obj a b ht
  have hb' := ProEtale.scalarExtension_bounded_of_tor T B _ a b ht'
  have hc' := ProEtale.scalarExtension_constructible φ T K.obj hb hc
  exact ⟨⟨hb', hc'⟩, a, b, ht'⟩

/-- Restriction of the actual quotient tensor, with unchanged morphisms.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
def Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (domain l E T m).FullSubcategory ⥤ (domain l E T n).FullSubcategory :=
  (domain l E T n).lift ((domain l E T m).ι ⋙ reduction l E T h)
    (reduction_preserves l E T h)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

set_option linter.unusedSectionVars false in
include D hl Xbase Ybase Xft Xqc Yft Yqc Xsep Ysep fbase fsep fft fqc in
/-- The two specified finite functors preserve their constructible finite-Tor domains.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional).
Proof: bound the dimension of the proper compactification over the field and apply
exists_sfFiniteExceptionalOperations at the given field and positive level. Its literal
ambient-functor equalities give preservation for compact support and for the specified
ordinary-etale right adjoint transported to intrinsic coefficients. Right-adjoint
uniqueness identifies that adjoint with sfFiniteExceptionalFixed. Repleteness of the
finite-Tor constructible subcategory transports preservation along this canonical
isomorphism. The finite-dimension theorem includes the empty scheme. -/
theorem operations_preserve (n : ℕ) :
    (∀ K : (domain l E X n).FullSubcategory,
      domain l E Y n ((sfIntrinsicCompactSupport c
        (Padic.coefficientExtensionRing l E (n + 1))).obj K.obj)) ∧
    (∀ L : (domain l E Y n).FullSubcategory,
      domain l E X n ((ProEtale.sfFiniteExceptional
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj)) := by
  let E' : ConstructibleExceptionalCoefficients.FieldStage.{u} l :=
    { carrier := E }
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ (Y ↘ Spec (.of D.k)))
  obtain ⟨cMinus, cPlus, h⟩ := exists_sfFiniteExceptionalOperations D l hl f c d hd
  obtain ⟨F', G', eF, eG, _⟩ := h E' ⟨n + 1, Nat.succ_pos n⟩
  constructor
  · intro K
    have he := congrArg
      (fun H : (domain l E X n).FullSubcategory ⥤
          proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ↦ H.obj K) eF
    exact he ▸ (F'.obj K).property
  · intro L
    have he := congrArg
      (fun H : (domain l E Y n).FullSubcategory ⥤
          proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) ↦ H.obj L) eG
    have hG : domain l E X n
        ((sfFiniteOperationsIntrinsicRight l E' ⟨n + 1, Nat.succ_pos n⟩ c).obj L.obj) :=
      he ▸ (G'.obj L).property
    have : (domain l E X n).IsClosedUnderIsomorphisms :=
      (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).1
    let : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
    let e : ProEtale.sfFiniteExceptionalFixed
        (Padic.coefficientExtensionRing l E (n + 1)) c ≅
          ProEtale.sfFiniteExceptionalAt
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
      letI := c.hasCompactification
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _
          ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
            (Adjunction.ofIsLeftAdjoint
              (Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} (ULift.{u + 1, u}
                  (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _
    exact (domain l E X n).prop_of_iso
      ((Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          (sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).inverse e)
        (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).functor).symm.app L.obj) hG

/-- Rf_! is the restriction of the specified compactification construction.
Source: blueprint F_r (blueprint: lem-coef-finite-exceptional). -/
def F (n : ℕ) :
    (domain l E X n).FullSubcategory ⥤ (domain l E Y n).FullSubcategory :=
  (domain l E Y n).lift ((domain l E X n).ι ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    (operations_preserve l E D hl f c n).1

/-- Rf^! is the restriction of Rnu_* followed by the etale adjoint and nu^*.
Source: blueprint G_r (blueprint: lem-coef-finite-exceptional). -/
def G (n : ℕ) :
    (domain l E Y n).FullSubcategory ⥤ (domain l E X n).FullSubcategory :=
  (domain l E X n).lift ((domain l E Y n).ι ⋙
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c)
    (operations_preserve l E D hl f c n).2

/-- The recorded Verdier dual into the actual structural exceptional image of the unit.
Source: blueprint omega and D (blueprint: lem-coef-finite-exceptional). -/
def dual (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] (n : ℕ) :
    (proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)))ᵒᵖ ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Functor.curry.obj (finiteIntrinsicDerivedInternalHom l E T n)).flip.obj
    (integralDualizingFiniteTerm l E D T n)

/-- The double-dual pullback formula as an actual covariant ambient functor.
Source: blueprint first display (blueprint: lem-coef-finite-exceptional). -/
def H (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (dual l E D Y n).rightOp ⋙ (finiteDerivedPullback l E n f).op ⋙ dual l E D X n

/-- The canonical compact-support scalar mate, in the intrinsic realization.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def supportMap {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        reduction l E Y h ⟶
      reduction l E X h ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.whiskerRight (PurCompactSupport.finiteImageIso l E m c).inv
      (reduction l E Y h) ≫
    PurCompactSupport.comparison (PurCompactSupport.finiteQuotientChange l E
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1)) c ≫
    Functor.whiskerLeft (reduction l E X h)
      (PurCompactSupport.finiteImageIso l E n c).hom

/-- Quotient composition as an equality of actual constant-ring maps.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction sends both composites to the same residue class.
The constant-sheaf functor preserves this equality, including equal indices. -/
theorem quotient_comp (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map T ≫
      (PurCompactSupport.finiteQuotientChange l E (n + 1) (t + 1)
        (Nat.succ_pos n) (Nat.succ_pos t) (Nat.add_le_add_right k 1)).map T =
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (t + 1)
      (Nat.succ_pos m) (Nat.succ_pos t) (Nat.add_le_add_right (k.trans h) 1)).map T := by
  change (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ ≫
      (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _ =
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- The identical quotient induces the identity map of coefficient sheaves.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction gives identity on each residue class, and constant
sheafification preserves identities. -/
theorem quotient_id (T : Scheme.{u}) (n : ℕ) :
    (PurCompactSupport.finiteQuotientChange l E (n + 1) (n + 1)
      (Nat.succ_pos n) (Nat.succ_pos n) (Nat.add_le_add_right (le_refl n) 1)).map T =
      𝟙 _ := by
  change (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (compactSupportLevelQuotient l E n n le_rfl).ulift) = 𝟙 _
  have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
    Ideal.Quotient.factor_eq
  rw [hq]
  exact (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id _

/-- Actual tensor associativity restricted through the full finite-Tor inclusion.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional). -/
def reassoc (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    Q l E T h ⋙ Q l E T k ≅ Q l E T (k.trans h) :=
  Functor.fullyFaithfulCancelRight (domain l E T t).ι
    (Functor.isoWhiskerLeft (domain l E T m).ι
      (PurCompactSupport.tensorComposition _ _ _ (quotient_comp l E T h k)))

/-- Actual multiplication unit for self reduction, restricted to finite Tor.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional). -/
def selfReduction (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (domain l E T n).ι
    (Functor.isoWhiskerLeft (domain l E T n).ι
      (eqToIso (congrArg pbcDerivedExtend (quotient_id l E T n)) ≪≫
        PurCompactSupport.tensorIdentity _))

/-- Brown representability for the specified ordinary etale compact-support candidate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
instance fixedSupport_isLeftAdjoint (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c

/-- The specified fixed-scalar exceptional realization is identified with the
right adjoint of the very same compactification by uniqueness of right adjoints.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedExceptionalIso (n : ℕ) :
    ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
  letI := c.hasCompactification
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft _
      ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _

/-- The canonical fixed-scalar Hom bijection, with an arbitrary retained etale origin.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedHom (n : ℕ)
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    ((ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      M.obj ⟶ L.obj) ≃
      (M.obj ⟶ (ProEtale.sfFiniteExceptionalFixed
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj) :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  (ProEtale.specifiedExceptionalHomEquiv _ c M W L).trans
    ((fixedExceptionalIso l E f c n).symm.app L.obj).homToEquiv

/-- The normalization on every etale-origin representative fixes the adjunction,
including its units and counits. There is no choice of adjunction in this predicate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def AdjunctionNormalized (n : ℕ) (a : F l E D hl f c n ⊣ G l E D hl f c n) : Prop :=
  ∀ (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (hM : domain l E X n
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        M.obj))
    (hL : domain l E Y n
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        L.obj))
    (v : (ProEtale.sfFixedCompactSupport
      (Padic.coefficientExtensionRing l E (n + 1)) c).obj M.obj ⟶ L.obj),
    (a.homEquiv ⟨_, hM⟩ ⟨_, hL⟩
      (ObjectProperty.homMk
        ((ProEtale.sfIntrinsicCompactSupportComparison _ c).hom.app M.obj ≫
          (sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).functor.map v))).hom =
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (fixedHom l E D f c n M W L v ≫
            (ProEtale.sfFiniteExceptionalFixed
              (Padic.coefficientExtensionRing l E (n + 1)) c).map
                ((sfIntrinsicDerivedEquivalence Y
                  (Padic.coefficientExtensionRing l E (n + 1))).unitIso.hom.app L.obj))

/-- The constructible adjunction is uniquely fixed by the recorded bounded Hom chain.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional).
Proof: lem-sf-proetale-constructible-origin supplies a bounded etale representative
for every constructible input. Transport specifiedExceptionalHomEquiv through the
canonical coefficient realizations. Its naturality supplies Adjunction.mkOfHomEquiv.
Full faithfulness and independence of the representative give the displayed
normalization for every witness. Each Hom bijection is therefore determined, so the
adjunction is unique. Preservation and Tor domains are operations_preserve. -/
theorem adjunction_existsUnique (n : ℕ) :
    ∃! a : F l E D hl f c n ⊣ G l E D hl f c n,
      AdjunctionNormalized l E D hl f c n a := by
  sorry

/-- The specified constructible adjunction, selected only by its unique Hom normalization.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def adjunction (n : ℕ) : F l E D hl f c n ⊣ G l E D hl f c n :=
  (adjunction_existsUnique l E D hl f c n).choose

set_option linter.unusedSectionVars false in
/-- The finite constant-ring pull identifications respect compactification composition.
Source: blueprint proof step 3, projection construction
(blueprint: lem-coef-finite-exceptional).
Proof: the canonical inverse-image comparison sends every constant section to itself.
The inverse-image composition comparison has the same action. The constant-sheaf
universal property identifies the two ring maps, hence their isomorphisms. -/
theorem finitePull_comp (n : ℕ) :
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ c.g) =
      proEtaleRingCompositeCoefficients c.i c.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i) := by
  exact (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
    (Padic.coefficientExtensionRing l E (n + 1))).symm

/-- The ordinary pullback presentation comparison, descended termwise. It is fixed
by the constant-section adjunction, before any exceptional formula is considered.
Source: blueprint proof step 3, ordinary pullback
(blueprint: lem-coef-finite-exceptional). -/
def formulaPullIso (n : ℕ) :
    PurCompactSupport.pull (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) f ≅
      finiteDerivedPullback l E n f := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive _ f
  letI : HasDerivedCategory (proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  exact Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (D := proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1))))
    (PurCompactSupport.finitePullbackIso.{u} l E n f)

/-- Evaluation and absolute-trace normalization of the finite dual-formula comparison.
All tensor presentations have their existing K-flat/evaluation normalization, and
sX is the descended Koszul symmetry. The trace is the existing structural-counit
transpose through compact-support composition, transported by the canonical site
comparisons. Thus this equation excludes rescaling the dual-formula isomorphism.
Source: blueprint proof steps 3--5; finite analogue of FormulaNormalized in
CoefDualFormulaScalarTranspose (blueprint: lem-coef-finite-exceptional). -/
def FormulaNormalized (n : ℕ)
    (k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n) : Prop :=
  ∀ (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (L : (domain l E Y n).FullSubcategory),
    ((PurCompactSupport.projectionMap
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (finitePull_comp l E f c n)).app ((G l E D hl f c n).obj L).obj).app
        ((dual l E D Y n).obj (op L.obj)) ≫
      (PurCompactSupport.image
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map
        (aX.tensor.map (Prod.mkHom (𝟙 _)
          ((formulaPullIso l E f n).hom.app ((dual l E D Y n).obj (op L.obj)))) ≫
          (sX.swap ((G l E D hl f c n).obj L).obj
            ((finiteDerivedPullback l E n f).obj
              ((dual l E D Y n).obj (op L.obj)))).hom ≫
          aX.tensor.map (Prod.mkHom (𝟙 _) (k.hom.app L)) ≫
          (aX.adjunction ((finiteDerivedPullback l E n f).obj
            ((dual l E D Y n).obj (op L.obj)))).counit.app
              (integralDualizingFiniteTerm l E D X n)) ≫
      (PurCompactSupport.finiteImageIso l E n c).hom.app
        (integralDualizingFiniteTerm l E D X n) ≫
      CoefDualFormulaScalarTranspose.finiteTrace D l E f c n =
    aY.tensor.map (Prod.mkHom
      ((PurCompactSupport.finiteImageIso l E n c).hom.app
        ((G l E D hl f c n).obj L).obj ≫
        ((adjunction l E D hl f c n).counit.app L).hom) (𝟙 _)) ≫
      (aY.tensor.map (Prod.mkHom (𝟙 L.obj) (𝟙 _))) ≫
      (aY.adjunction L.obj).counit.app (integralDualizingFiniteTerm l E D Y n)

/-- The finite dual formula has a unique evaluation/trace-normalized natural isomorphism.
Source: blueprint proof steps 2--5 (blueprint: lem-coef-finite-exceptional).
Proof: finite Verdier biduality and pullback Tor preservation put H in the domain.
Form the structural relative trace by transposing the absolute counit through support
composition. Projection, the ordinary counit and evaluation define the exchange
pairing. The absolute-trace-exchange lemma identifies its Hom action and proves it
invertible. Biduality, the ordinary adjunction, this exchange and biduality give the
four natural Hom bijections displayed in the blueprint. They make H a right adjoint
to F. Uniqueness of right adjoints compares it with the specified adjunction F ⊣ G.
Uncurrying the image of its counit gives exactly the displayed normalization, for
every normalized tensor presentation. Conversely, tensor-Hom injectivity, projection
invertibility on the finite-Tor domain and Verdier duality force each component from
this equation. Naturality then gives uniqueness of the natural isomorphism. -/
theorem dualFormula_existsUnique (n : ℕ) :
    ∃! k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n,
      FormulaNormalized l E D hl f c n k := by
  sorry

/-- The canonical finite dual formula, chosen only from its unique evaluation/trace
normalization. Source: blueprint proof step 5
(blueprint: lem-coef-finite-exceptional). -/
def dualFormulaIso (n : ℕ) :
    G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n :=
  (dualFormula_existsUnique l E D hl f c n).exists.choose

/-- The compact-support comparison restricted through the full inclusion.
Its orientation is Q_Y F_m to F_n Q_X, as in the displayed unit/counit identities.
Source: blueprint second paragraph (blueprint: lem-coef-finite-exceptional). -/
def qMap {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ⟶ Q l E X h ⋙ F l E D hl f c n :=
  ((domain l E Y n).fullyFaithfulι.whiskeringRight
    (domain l E X m).FullSubcategory).preimage
    (Functor.whiskerLeft (domain l E X m).ι (supportMap l E f c h))

omit Xsep Ysep in
/-- The normalized coefficient comparison is invertible before choosing finite coordinates. -/
private theorem coefficientComparison_isIso
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (R : ConstructibleExceptionalCoefficients.RingSystem l Ω D hl (f := f))
    {s t : ConstructibleExceptionalCoefficients.RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : ConstructibleExceptionalCoefficients.Allowed l a)
    (K : ConstructibleExceptionalCoefficients.C l Ω X (s.stage l)) :
    IsIso ((PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K)) := by
  let := (R.scalar (s := s) (t := t) a ha true).commShift
  let := (R.scalar (s := s) (t := t) a ha false).commShift
  let i :=
    (ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω Y t).mapIso
        ((R.comparison c (s := s) (t := t) a ha).q.app K) ≪≫
      (R.left c t).app ((R.scalar (s := s) (t := t) a ha true).functor.obj K) ≪≫
      (PurCompactSupport.image (t.coefficients l) c).mapIso
        ((R.scalar (s := s) (t := t) a ha true).realization.app K)
  let j :=
    (R.scalar (s := s) (t := t) a ha false).realization.app ((R.operation c (s.stage l)).F.obj K) ≪≫
      (pbcDerivedExtend (a.map Y)).mapIso ((R.left c s).app K)
  have he : j.hom ≫ (PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K) = i.hom := by
    simpa only [j, i, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc] using (R.comparison_normalized c (s := s) (t := t) a ha K).symm
  have hi : IsIso (j.hom ≫ (PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K)) :=
    he.symm ▸ i.isIso_hom
  exact IsIso.of_isIso_comp_left j.hom _

attribute [local irreducible] reductionDerivedChange PurCompactSupport.comparison
  PurCompactSupport.finiteImageIso in
/-- The actual compact-support comparison is invertible on the stated domain.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: lem-fix-compact-support-coefficient-change gives invertibility on the etale
origin of every bounded constructible finite-Tor input. The canonical intrinsic
realization preserves this comparison. The full inclusion reflects isomorphisms. -/
theorem qMap_isIso {m n : ℕ} (h : n ≤ m) : IsIso (qMap l E D hl f c h) := by
  let Ω := AlgebraicClosure (ULift.{u} (Padic l))
  obtain ⟨S⟩ := ConstructibleExceptionalCoefficients.exists_system l Ω D hl f
  let R := S.ring
  let E' : ConstructibleExceptionalCoefficients.FieldStage.{u} l := { carrier := E }
  let s : ConstructibleExceptionalCoefficients.RingStage.{u} l :=
    .finite E' ⟨m + 1, Nat.succ_pos m⟩
  let t : ConstructibleExceptionalCoefficients.RingStage.{u} l :=
    .finite E' ⟨n + 1, Nat.succ_pos n⟩
  let a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l) :=
    PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
  let ha : ConstructibleExceptionalCoefficients.Allowed l
      (s := .finite E' ⟨m + 1, Nat.succ_pos m⟩)
      (t := .finite E' ⟨n + 1, Nat.succ_pos n⟩) a :=
    .quotient E' ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right h 1)
  have hcomp (K : (domain l E X m).FullSubcategory) :
      IsIso ((PurCompactSupport.comparison a c).app K.obj) :=
    coefficientComparison_isIso l D hl f c Ω R (s := s) (t := t) a ha K
  let e : ((F l E D hl f c m ⋙ Q l E Y h) ⋙ (domain l E Y n).ι) ≅
      ((Q l E X h ⋙ F l E D hl f c n) ⋙ (domain l E Y n).ι) :=
    NatIso.ofComponents (fun K ↦
      (reduction l E Y h).mapIso ((PurCompactSupport.finiteImageIso l E m c).symm.app K.obj) ≪≫
        @asIso _ _ _ _ ((PurCompactSupport.comparison a c).app K.obj) (hcomp K) ≪≫
        (PurCompactSupport.finiteImageIso l E n c).app ((reduction l E X h).obj K.obj))
      (by
        intro K K' v
        exact (supportMap l E f c h).naturality v.hom)
  let ff := (domain l E Y n).fullyFaithfulι.whiskeringRight
    (domain l E X m).FullSubcategory
  exact (ff.preimageIso e).isIso_hom

/-- The canonical compact-support coefficient isomorphism.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def q {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ≅ Q l E X h ⋙ F l E D hl f c n :=
  @asIso _ _ _ _ (qMap l E D hl f c h) (qMap_isIso l E D hl f c h)

/-- The exceptional coefficient map is the counit transpose of inverse q. This
formula fixes the map itself before its invertibility, rather than choosing an
isomorphism. Source: blueprint proof paragraphs 2 and 3
(blueprint: lem-coef-finite-exceptional). -/
def b {m n : ℕ} (h : n ≤ m) :
    G l E D hl f c m ⋙ Q l E X h ⟶ Q l E Y h ⋙ G l E D hl f c n :=
  mateEquiv (adjunction l E D hl f c m) (adjunction l E D hl f c n)
    (q l E D hl f c h).inv

```

## New

The Old declaration block is in Sheaf.SixFunctors.FiniteExceptionalData, with identical
names, signatures, public visibility, attributes, and data bodies. The two quotient
identity theorem proofs are refactored through a proved private helper quotient_map. The original module
publicly imports this data module, preserving its public import closure. The final
finite_exceptional statement stays verbatim in the original module and is proved by
combining quotient invertibility and coherence with choice specification and the two
Mathlib mate identities. Two original unique-existence holes remain unchanged.
No target meaning changes. No source-library module is edited.

## Users

The downstream inventory used tools/downstream.py for the module and every moved name.
All 79 transitive consumers remain valid because the original import publicly re-exports
exactly the same declarations and all original public imports. No consumer is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FiniteExceptional | S2 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.CartesianSectionData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.FiniteAdjointMateCompatibility | V6 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.FiniteTorStability | J2 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.GeometricComparisonData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.GeometricOperations | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RamifiedScalarSystemTranspose | R8 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RelativeKunneth | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | U9 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TraceCorrespondences | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackSquareScalars | S2 | unchanged public names, signatures and data; no adaptation |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Q9 | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | B8 | unchanged public names, signatures and data; no adaptation |
| Sheaf.SixFunctors.FiniteExceptionalData | new | owns unchanged construction block |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | new | quotient invertibility only |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | new | quotient cocycle and identity only |

## Status

landed 20261025T164236-L-981366 2026-10-25 (merge of deliver/S2/Sheaf.SixFunctors.FiniteExceptional)
