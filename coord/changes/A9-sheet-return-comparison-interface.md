# SheetReturn and sheet-return comparison interfaces

## Reason

The three strict parts of the original eleven-step proof need its existing comparison
predicates without importing the theorem which imports them. Extract those interfaces
into ConstantExtensionReturnData and publicly reexport them. This prevents an import
cycle. Every existing signature and non-proof body is unchanged. No arbitrary witness
is chosen, and the stalk isomorphism still uses its uniquely determining formula.
The three normalization proofs already recorded in the Q4 ledger are preserved; they
were still holes in the shared source read at session start. Challenge.lean and the
mathematical interpretation of all its definitions are unchanged.

## Old

The following block was directly in ConstantExtensionReturnLocalOperators:

```lean
namespace SheetReturn

/-- Concatenating positive blocks, retaining the order of every transport factor.
The compositor is directed from the pullback of a composite to successive pullbacks.
Source: Deligne, Weil II (1.1.7)--(1.1.10), ordered block comparison
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def blocks {C : Type a} [Category.{b} C] {V : Type c} [Category.{d} V]
    (B : C ⥤ V) (F : ℕ → C ⥤ C)
    (I : ∀ (n : ℕ) (M : C), B.obj M ⟶ B.obj ((F n).obj M))
    (comp : ∀ (i j : ℕ), F (i + j) ≅ F j ⋙ F i) (m : ℕ) (M : C) :
    (r : ℕ) → B.obj M ⟶ B.obj ((F (m * (r + 1))).obj M)
  | 0 => I m M ≫ eqToHom (congrArg (fun n ↦ B.obj ((F n).obj M))
      (Nat.mul_one m).symm)
  | r + 1 => blocks B F I comp m M r ≫
      I m ((F (m * (r + 1))).obj M) ≫
      B.map ((comp m (m * (r + 1))).inv.app M) ≫
      eqToHom (congrArg (fun n ↦ B.obj ((F n).obj M))
        ((Nat.add_comm m (m * (r + 1))).trans (Nat.mul_succ m (r + 1)).symm))

/-- The equality used by the compositor is an equality of the actual scheme maps.
Source: Deligne, Weil II (1.1.7), Frobenius powers
(blueprint: lem-zl-constant-extension-return-local-operators).
Proof: commute the natural-number summands, use pow_add on the automorphism group,
and apply Iso.hom. Multiplication of automorphisms reverses composition notation. -/
theorem powerEquality {S : Type a} [Category.{b} S] {s : S} (g : Aut s) (i j : ℕ) :
    (g ^ (i + j)).hom = (g ^ i).hom ≫ (g ^ j).hom := by
  rw [Nat.add_comm i j, pow_add]
  rfl

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite compositor, conjugated by the prescribed unit-normalized presentations.
Source: Deligne, Weil II (1.1.7)--(1.1.10); Stacks 0D6D
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def finiteComp (n i j : ℕ) :
    finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ (i + j)).hom ≅
      finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ j).hom ⋙
        finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ i).hom :=
  eqToIso (congrArg (finiteDerivedPullback l E n) (powerEquality (pointFrobeniusAut D) i j))
    ≪≫ pointPowerPullbackModel l E n
      (((pointFrobeniusAut D) ^ i).hom ≫ ((pointFrobeniusAut D) ^ j).hom)
    ≪≫ integralFiniteCanonicalPullbackComposition l E
      ((pointFrobeniusAut D) ^ i).hom ((pointFrobeniusAut D) ^ j).hom n
    ≪≫ Functor.isoWhiskerRight
      (pointPowerPullbackModel l E n ((pointFrobeniusAut D) ^ j).hom).symm _
    ≪≫ Functor.isoWhiskerLeft _
      (pointPowerPullbackModel l E n ((pointFrobeniusAut D) ^ i).hom).symm

/-- The whole-system compositor, before any evaluation or derived inverse limit.
Source: Deligne, Weil II (1.1.7)--(1.1.10), integral enhancement; Stacks 0941
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def towerComp (i j : ℕ) :
    IntegralPointTransportTower.pullback D l E (i + j) ≅
      IntegralPointTransportTower.pullback D l E j ⋙
        IntegralPointTransportTower.pullback D l E i :=
  eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
    (powerEquality (pointFrobeniusAut D) i j)) ≪≫
      integralComparisonSystemComposition l E
        ((pointFrobeniusAut D) ^ i).hom ((pointFrobeniusAut D) ^ j).hom

/-- Finite point sections in the same derived-category presentation as the specified
point transport. Both derived-category instances are explicitly retained.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-zl-constant-extension-return-local-operators). -/
abbrev finiteFibre (n : ℕ) :=
  @Functor.mapDerivedCategory
    (SheafOfModules.{u + 1} (integralCoefficientSheaf l E (Spec (.of D.k)) n)) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual ordered block equations at finite level and on whole integral towers.
The last equation realizes the whole-system transport through its specified zeta and nu.
Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, integral enhancement
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def TransportLaws (hl : l ≠ D.p) (m : ℕ) : Prop :=
  (∀ (n r : ℕ) (M : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))),
    intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)) M →
    blocks
      (finiteFibre D l E n)
      (fun t ↦ finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ t).hom)
      (fun t M ↦ pointPowerTransportFinite D l hl E t n M)
      (finiteComp D l E n) m M r = pointPowerTransportFinite D l hl E (m * (r + 1)) n M) ∧
  (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k))),
    blocks (IntegralPointTransportTower.sections D l E)
      (IntegralPointTransportTower.pullback D l E)
      (fun t C ↦ (IntegralPointTransportTower.transport D l E t).app C)
      (towerComp D l E) m C r =
        (IntegralPointTransportTower.transport D l E (m * (r + 1))).app C) ∧
  (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
    (IntegralPointTransportTower.moduleLimit l E).map
        ((IntegralPointTransportTower.transport D l E (m * (r + 1))).app C) ≫
        (IntegralPointTransportTower.zeta D l E).hom.app
          ((IntegralPointTransportTower.pullback D l E (m * (r + 1))).obj C) =
      (IntegralPointTransportTower.zeta D l E).hom.app C ≫
        IntegralPointTransportTower.iota D l E hl (m * (r + 1))
          ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
        (pointFibreIntegralAmbient D l E).map
          (IntegralPointTransportTower.nu D l E hl (m * (r + 1)) C hC).hom)

end SheetReturn

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The rational point fibre depends on k, not on which finite subfield is the base.
Source: Deligne, Weil II, paragraph after (1.1.10), p. 152
(blueprint: lem-zl-constant-extension-return-local-operators).
Proof: both integral constructions are the same point sections with the same completed
coefficient action. Their normalization on rationalized integral objects and fractions
is identical, so uniqueness of scalar-localization descent gives equality of functors. -/
theorem sheetReturnPointFibre_eq :
    pointRationalFibre (constantExtensionDatum D m hm) l hl E =
      pointRationalFibre D l hl E := by
  rfl

/-- The sheet pullback at a finite rational coefficient field.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def sheetReturnRationalPull :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (constantExtensionSheet D m hm X₀)
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀))
    (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))

/-- The rational sheet-return comparison, with precisely the specified compositors.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def sheetReturnRationalComparison
    (M : sfRationalConstructibleCategory l E
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left) :=
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  (localPullbackComposition l E
    ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom (constantExtensionSheet D m hm X₀) M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (constantExtensionSheet_return D m hm X₀)) ≪≫
    localPullbackComposition l E (constantExtensionSheet D m hm X₀)
      (localPositivePower
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1)) M

/-- A finite rational presentation is the actual return if its carrier comparison
identifies its Weil map with the ordered m-fold iterate, through the fixed compositor.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def SheetReturnRationalSpec
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier) : Prop :=
  (sfWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E).map α.hom ≫
      (sheetReturnRationalComparison D m hm X₀ l hl E N.carrier).hom ≫
      (sheetReturnRationalPull D m hm X₀ l hl E).map
        (localWeilIterate l E D hl (constantExtensionOriginalModel D m hm X₀)
          N (m - 1)).hom = A.str.hom ≫ α.hom

/-- The canonical identification is uniquely fixed by pullback composition, the carrier
comparison, and equality of the two point-fibre functors. HEq only suppresses the
subsingleton prime-invertibility witnesses used by the two pullback presentations.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: lem-zl-constant-extension-return-local-operators).
Proof: identify the prime-invertibility instances by Subsingleton.elim. Pull back alpha
along x, compose with the inverse normalized compositor for x and the sheet inclusion,
and apply point sections. Equality of the point-fibre functors supplies the first
comparison. This explicit formula determines the isomorphism and proves uniqueness. -/
theorem sheetReturnStalkIso_existsUnique
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left) :
    ∃! e : localPointComplex l E (constantExtensionDatum D m hm) hl
        (constantExtensionModel D m hm X₀) A x ≅
      localPointComplex l E D hl (constantExtensionOriginalModel D m hm X₀)
        N (x ≫ constantExtensionSheet D m hm X₀),
      HEq e.hom
        ((eqToIso (sheetReturnPointFibre_eq D m hm l hl E)).hom.app
          (localDerivedStalk l E (constantExtensionDatum D m hm) hl
            (constantExtensionModel D m hm X₀) A x) ≫
          (pointRationalFibre D l hl E).map
            ((@rationalDerivedPullback l _ E _ _ _ _ _ x
              (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
              (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
                (constantExtensionModel D m hm X₀))).map α.hom) ≫
          (pointRationalFibre D l hl E).map
            (@localPullbackComposition l _ E _ _ _ _ _ _ x
              (constantExtensionSheet D m hm X₀)
              (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
              (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
                (constantExtensionModel D m hm X₀))
              (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
              N.carrier).inv) := by
  let e : localPointComplex l E (constantExtensionDatum D m hm) hl
      (constantExtensionModel D m hm X₀) A x ≅
      localPointComplex l E D hl (constantExtensionOriginalModel D m hm X₀)
        N (x ≫ constantExtensionSheet D m hm X₀) :=
    (eqToIso (sheetReturnPointFibre_eq D m hm l hl E)).app
        (localDerivedStalk l E (constantExtensionDatum D m hm) hl
          (constantExtensionModel D m hm X₀) A x) ≪≫
      (pointRationalFibre D l hl E).mapIso
        ((@rationalDerivedPullback l _ E _ _ _ _ _ x
          (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
            (constantExtensionModel D m hm X₀))).mapIso α) ≪≫
      (pointRationalFibre D l hl E).mapIso
        (@localPullbackComposition l _ E _ _ _ _ _ _ x
          (constantExtensionSheet D m hm X₀)
          (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
          (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
            (constantExtensionModel D m hm X₀))
          (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
          N.carrier).symm
  have he : HEq e.hom _ := HEq.rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  exact eq_of_heq (he'.trans he.symm)

/-- The uniquely normalized stalk comparison, with no arbitrary choice of conjugacy.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def sheetReturnStalkIso
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left) :=
  (sheetReturnStalkIso_existsUnique D m hm X₀ l hl E N A α x).exists.choose

/-- Canonical finite-stage local comparison, for compatible geometric points and their
actual return squares. The two operators are the original iterated-transport recipes.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def SheetReturnRationalOperators : Prop :=
  ∀ (N : sfWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilSheaf (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.obj.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.obj.carrier),
    SheetReturnRationalSpec D m hm X₀ l hl E N.obj A.obj α →
    ∀ (r : ℕ)
      (x : Spec (.of D.k) ⟶
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left)
      (hA : x ≫ localPositivePower
          ((constantExtensionDatum D m hm).geometricFrobenius
            (constantExtensionModel D m hm X₀)).hom r =
        localPositivePower (frobeniusPointIso (constantExtensionDatum D m hm)).hom r ≫ x)
      (hN : (x ≫ constantExtensionSheet D m hm X₀) ≫ localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m * (r + 1) - 1) =
        localPositivePower (frobeniusPointIso D).hom (m * (r + 1) - 1) ≫
          (x ≫ constantExtensionSheet D m hm X₀)),
      (sheetReturnStalkIso D m hm X₀ l hl E N.obj A.obj α x).hom ≫
          localFrobeniusOperator l E D hl (constantExtensionOriginalModel D m hm X₀)
            N.obj (x ≫ constantExtensionSheet D m hm X₀) (m * (r + 1) - 1) hN =
        localFrobeniusOperator l E (constantExtensionDatum D m hm) hl
          (constantExtensionModel D m hm X₀) A.obj x r hA ≫
          (sheetReturnStalkIso D m hm X₀ l hl E N.obj A.obj α x).hom

/-- The identification is natural on all underlying arrows and hence on Weil morphisms.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def SheetReturnStalkNaturality : Prop :=
  ∀ (N N' : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A A' : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (α' : A'.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N'.carrier)
    (f : N ⟶ N') (g : A ⟶ A'),
    g.hom.f ≫ α'.hom = α.hom ≫ (sheetReturnRationalPull D m hm X₀ l hl E).map f.hom.f →
    ∀ (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left),
      HEq
        ((pointRationalFibre (constantExtensionDatum D m hm) l hl E).map
          ((@rationalDerivedPullback l _ E _ _ _ _ _ x
            (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
            (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
              (constantExtensionModel D m hm X₀))).map g.hom.f) ≫
          (sheetReturnStalkIso D m hm X₀ l hl E N' A' α' x).hom)
        ((sheetReturnStalkIso D m hm X₀ l hl E N A α x).hom ≫
          (pointRationalFibre D l hl E).map
            ((@rationalDerivedPullback l _ E _ _ _ _ _
              (x ≫ constantExtensionSheet D m hm X₀)
              (frobeniusPointPrimeInvertible D l hl)
              (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).map
                f.hom.f))

/-- Scalar extension of a stalk, through the normalized point and pullback comparisons.
Source: Deligne, Weil II (1.1.3) and (1.1.8), pp. 150--151
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def sheetReturnScalarStalk
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (N : sfWeilComplex D l hl Y₀ E) (N' : sfWeilComplex D l hl Y₀ L)
    (ε : N'.carrier ≅
      (sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N.carrier)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (pointRationalFibreScalarIso D l hl E L ι).symm.app
      (localDerivedStalk l E D hl Y₀ N x) ≪≫
    (pointRationalFibre D l hl L).mapIso
      ((rationalPullbackScalarComparison l E L ι x).app N.carrier ≪≫
        (rationalDerivedPullback l L x).mapIso ε.symm)

/-- The canonical sheet comparison commutes with finite extension of coefficients.
The carrier squares specify scalar extension, rather than arbitrary stalk isomorphisms.
Identity extensions are included; successive extensions use the same tensor associators.
Source: Deligne, Weil II (1.1.3), (1.1.8)--(1.1.10), pp. 150--152
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def SheetReturnScalarCompatibility : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (N' : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) L)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (A' : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) L)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (α' : A'.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl L).obj N'.carrier)
    (εN : N'.carrier ≅
      (sfRationalScalarExtension l E
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N.carrier)
    (εA : A'.carrier ≅
      (sfRationalScalarExtension l E
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj A.carrier),
    HEq (εA.hom ≫
      (sfRationalScalarExtension l E
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map α.hom ≫
      (@rationalPullbackScalarComparison l _ E _ _ _ L _ _ _ ι _ _
        (constantExtensionSheet D m hm X₀)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀))
        (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).hom.app
          N.carrier)
      (α'.hom ≫ (sheetReturnRationalPull D m hm X₀ l hl L).map εN.hom) →
    ∀ (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left),
    HEq
      ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (sheetReturnStalkIso D m hm X₀ l hl E N A α x).hom ≫
        (sheetReturnScalarStalk D l hl E L ι
          (constantExtensionOriginalModel D m hm X₀) N N' εN
          (x ≫ constantExtensionSheet D m hm X₀)).hom)
      ((sheetReturnScalarStalk (constantExtensionDatum D m hm) l hl E L ι
          (constantExtensionModel D m hm X₀) A A' εA x).hom ≫
        (sheetReturnStalkIso D m hm X₀ l hl L N' A' α' x).hom)

/-- Subobjects and finite chains, with their actual quotient objects and every specified
pure weight. Equality is equality of subobjects, not chosen monomorphism representatives.
Source: Deligne, Weil II, p. 152 and (1.2.6), p. 154
(blueprint: lem-zl-constant-extension-return-local-operators). -/
def SheetReturnFiltrations (iota : Ω ≃+* ℂ)
    (R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) [PreservesFiniteLimits R] : Prop :=
  ∀ N, ∃ e : Subobject N ≃o Subobject (R.obj N),
    (∀ U, e U = Subobject.mk (R.map U.arrow)) ∧
    (∀ (U V : Subobject N) (h : U ≤ V),
      Nonempty (R.obj (cokernel (Subobject.ofLE U V h)) ≅
        cokernel (Subobject.ofLE (e U) (e V) (e.monotone h))) ∧
      ∀ w : ℝ,
        (SfIsPunctuallyPureOfWeight D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) iota
            (cokernel (Subobject.ofLE U V h)) w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota
            (cokernel (Subobject.ofLE (e U) (e V) (e.monotone h))) w)) ∧
    (∀ t : ℕ, ∃ eF : (Fin (t + 1) →o Subobject N) ≃
        (Fin (t + 1) →o Subobject (R.obj N)),
      (∀ (s : Fin (t + 1) →o Subobject N) (i : Fin (t + 1)), (eF s) i = e (s i)) ∧
      (∀ s, (s 0 = ⊥ ∧ s (Fin.last t) = ⊤) ↔
        ((eF s) 0 = ⊥ ∧ (eF s) (Fin.last t) = ⊤)))

```

## New

The block now lives in ConstantExtensionReturnData, publicly imported by the original
module. Only theorem proofs and blueprint ownership tags differ:

```lean
namespace SheetReturn

/-- Concatenating positive blocks, retaining the order of every transport factor.
The compositor is directed from the pullback of a composite to successive pullbacks.
Source: Deligne, Weil II (1.1.7)--(1.1.10), ordered block comparison
(blueprint: def-zl-sheet-return-data). -/
def blocks {C : Type a} [Category.{b} C] {V : Type c} [Category.{d} V]
    (B : C ⥤ V) (F : ℕ → C ⥤ C)
    (I : ∀ (n : ℕ) (M : C), B.obj M ⟶ B.obj ((F n).obj M))
    (comp : ∀ (i j : ℕ), F (i + j) ≅ F j ⋙ F i) (m : ℕ) (M : C) :
    (r : ℕ) → B.obj M ⟶ B.obj ((F (m * (r + 1))).obj M)
  | 0 => I m M ≫ eqToHom (congrArg (fun n ↦ B.obj ((F n).obj M))
      (Nat.mul_one m).symm)
  | r + 1 => blocks B F I comp m M r ≫
      I m ((F (m * (r + 1))).obj M) ≫
      B.map ((comp m (m * (r + 1))).inv.app M) ≫
      eqToHom (congrArg (fun n ↦ B.obj ((F n).obj M))
        ((Nat.add_comm m (m * (r + 1))).trans (Nat.mul_succ m (r + 1)).symm))

/-- The equality used by the compositor is an equality of the actual scheme maps.
Source: Deligne, Weil II (1.1.7), Frobenius powers
(blueprint: def-zl-sheet-return-data).
Proof: commute the natural-number summands, use pow_add on the automorphism group,
and apply Iso.hom. Multiplication of automorphisms reverses composition notation. -/
theorem powerEquality {S : Type a} [Category.{b} S] {s : S} (g : Aut s) (i j : ℕ) :
    (g ^ (i + j)).hom = (g ^ i).hom ≫ (g ^ j).hom :=
  by
    rw [Nat.add_comm i j, pow_add]
    rfl

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite compositor, conjugated by the prescribed unit-normalized presentations.
Source: Deligne, Weil II (1.1.7)--(1.1.10); Stacks 0D6D
(blueprint: def-zl-sheet-return-data). -/
def finiteComp (n i j : ℕ) :
    finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ (i + j)).hom ≅
      finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ j).hom ⋙
        finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ i).hom :=
  eqToIso (congrArg (finiteDerivedPullback l E n) (powerEquality (pointFrobeniusAut D) i j))
    ≪≫ pointPowerPullbackModel l E n
      (((pointFrobeniusAut D) ^ i).hom ≫ ((pointFrobeniusAut D) ^ j).hom)
    ≪≫ integralFiniteCanonicalPullbackComposition l E
      ((pointFrobeniusAut D) ^ i).hom ((pointFrobeniusAut D) ^ j).hom n
    ≪≫ Functor.isoWhiskerRight
      (pointPowerPullbackModel l E n ((pointFrobeniusAut D) ^ j).hom).symm _
    ≪≫ Functor.isoWhiskerLeft _
      (pointPowerPullbackModel l E n ((pointFrobeniusAut D) ^ i).hom).symm

/-- The whole-system compositor, before any evaluation or derived inverse limit.
Source: Deligne, Weil II (1.1.7)--(1.1.10), integral enhancement; Stacks 0941
(blueprint: def-zl-sheet-return-data). -/
def towerComp (i j : ℕ) :
    IntegralPointTransportTower.pullback D l E (i + j) ≅
      IntegralPointTransportTower.pullback D l E j ⋙
        IntegralPointTransportTower.pullback D l E i :=
  eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
    (powerEquality (pointFrobeniusAut D) i j)) ≪≫
      integralComparisonSystemComposition l E
        ((pointFrobeniusAut D) ^ i).hom ((pointFrobeniusAut D) ^ j).hom

/-- Finite point sections in the same derived-category presentation as the specified
point transport. Both derived-category instances are explicitly retained.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: def-zl-sheet-return-data). -/
abbrev finiteFibre (n : ℕ) :=
  @Functor.mapDerivedCategory
    (SheafOfModules.{u + 1} (integralCoefficientSheaf l E (Spec (.of D.k)) n)) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    _ _ (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual ordered block equations at finite level and on whole integral towers.
The last equation realizes the whole-system transport through its specified zeta and nu.
Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, integral enhancement
(blueprint: def-zl-sheet-return-data). -/
def TransportLaws (hl : l ≠ D.p) (m : ℕ) : Prop :=
  (∀ (n r : ℕ) (M : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))),
    intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k)) M →
    blocks
      (finiteFibre D l E n)
      (fun t ↦ finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ t).hom)
      (fun t M ↦ pointPowerTransportFinite D l hl E t n M)
      (finiteComp D l E n) m M r = pointPowerTransportFinite D l hl E (m * (r + 1)) n M) ∧
  (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k))),
    blocks (IntegralPointTransportTower.sections D l E)
      (IntegralPointTransportTower.pullback D l E)
      (fun t C ↦ (IntegralPointTransportTower.transport D l E t).app C)
      (towerComp D l E) m C r =
        (IntegralPointTransportTower.transport D l E (m * (r + 1))).app C) ∧
  (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
    (IntegralPointTransportTower.moduleLimit l E).map
        ((IntegralPointTransportTower.transport D l E (m * (r + 1))).app C) ≫
        (IntegralPointTransportTower.zeta D l E).hom.app
          ((IntegralPointTransportTower.pullback D l E (m * (r + 1))).obj C) =
      (IntegralPointTransportTower.zeta D l E).hom.app C ≫
        IntegralPointTransportTower.iota D l E hl (m * (r + 1))
          ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
        (pointFibreIntegralAmbient D l E).map
          (IntegralPointTransportTower.nu D l E hl (m * (r + 1)) C hC).hom)

end SheetReturn

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

variable (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The rational point fibre depends on k, not on which finite subfield is the base.
Source: Deligne, Weil II, paragraph after (1.1.10), p. 152
(blueprint: def-zl-sheet-return-data).
Proof: both integral constructions are the same point sections with the same completed
coefficient action. Their normalization on rationalized integral objects and fractions
is identical, so uniqueness of scalar-localization descent gives equality of functors. -/
theorem sheetReturnPointFibre_eq :
    pointRationalFibre (constantExtensionDatum D m hm) l hl E =
      pointRationalFibre D l hl E := by
  rfl

/-- The sheet pullback at a finite rational coefficient field.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: def-zl-sheet-return-data). -/
def sheetReturnRationalPull :=
  @rationalDerivedPullback l _ E _ _ _ _ _ (constantExtensionSheet D m hm X₀)
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀))
    (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))

/-- The rational sheet-return comparison, with precisely the specified compositors.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: def-zl-sheet-return-data). -/
def sheetReturnRationalComparison
    (M : sfRationalConstructibleCategory l E
      (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left) :=
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  (localPullbackComposition l E
    ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom (constantExtensionSheet D m hm X₀) M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M)
      (constantExtensionSheet_return D m hm X₀)) ≪≫
    localPullbackComposition l E (constantExtensionSheet D m hm X₀)
      (localPositivePower
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1)) M

/-- A finite rational presentation is the actual return if its carrier comparison
identifies its Weil map with the ordered m-fold iterate, through the fixed compositor.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: def-zl-sheet-return-data). -/
def SheetReturnRationalSpec
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier) : Prop :=
  (sfWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E).map α.hom ≫
      (sheetReturnRationalComparison D m hm X₀ l hl E N.carrier).hom ≫
      (sheetReturnRationalPull D m hm X₀ l hl E).map
        (localWeilIterate l E D hl (constantExtensionOriginalModel D m hm X₀)
          N (m - 1)).hom = A.str.hom ≫ α.hom

/-- The canonical identification is uniquely fixed by pullback composition, the carrier
comparison, and equality of the two point-fibre functors. HEq only suppresses the
subsingleton prime-invertibility witnesses used by the two pullback presentations.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: def-zl-sheet-return-data).
Proof: identify the prime-invertibility instances by Subsingleton.elim. Pull back alpha
along x, compose with the inverse normalized compositor for x and the sheet inclusion,
and apply point sections. Equality of the point-fibre functors supplies the first
comparison. This explicit formula determines the isomorphism and proves uniqueness. -/
theorem sheetReturnStalkIso_existsUnique
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left) :
    ∃! e : localPointComplex l E (constantExtensionDatum D m hm) hl
        (constantExtensionModel D m hm X₀) A x ≅
      localPointComplex l E D hl (constantExtensionOriginalModel D m hm X₀)
        N (x ≫ constantExtensionSheet D m hm X₀),
      HEq e.hom
        ((eqToIso (sheetReturnPointFibre_eq D m hm l hl E)).hom.app
          (localDerivedStalk l E (constantExtensionDatum D m hm) hl
            (constantExtensionModel D m hm X₀) A x) ≫
          (pointRationalFibre D l hl E).map
            ((@rationalDerivedPullback l _ E _ _ _ _ _ x
              (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
              (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
                (constantExtensionModel D m hm X₀))).map α.hom) ≫
          (pointRationalFibre D l hl E).map
            (@localPullbackComposition l _ E _ _ _ _ _ _ x
              (constantExtensionSheet D m hm X₀)
              (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
              (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
                (constantExtensionModel D m hm X₀))
              (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
              N.carrier).inv) := by
  let e := (eqToIso (sheetReturnPointFibre_eq D m hm l hl E)).app
      (localDerivedStalk l E (constantExtensionDatum D m hm) hl
        (constantExtensionModel D m hm X₀) A x) ≪≫
    (pointRationalFibre D l hl E).mapIso
      ((@rationalDerivedPullback l _ E _ _ _ _ _ x
        (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀))).mapIso α ≪≫
      (@localPullbackComposition l _ E _ _ _ _ _ _ x
        (constantExtensionSheet D m hm X₀)
        (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀))
        (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
        N.carrier).symm)
  refine ⟨e, ?_, ?_⟩
  · simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.map_comp]
    rfl
  · intro e' he'
    apply Iso.ext
    exact eq_of_heq (he'.trans (show HEq e.hom _ by
      simp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Functor.map_comp]
      rfl).symm)

/-- The uniquely normalized stalk comparison, with no arbitrary choice of conjugacy.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: def-zl-sheet-return-data). -/
def sheetReturnStalkIso
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left) :=
  (sheetReturnStalkIso_existsUnique D m hm X₀ l hl E N A α x).exists.choose

/-- Canonical finite-stage local comparison, for compatible geometric points and their
actual return squares. The two operators are the original iterated-transport recipes.
Source: Deligne, Weil II (1.1.8)--(1.1.10), pp. 151--152
(blueprint: def-zl-sheet-return-data). -/
def SheetReturnRationalOperators : Prop :=
  ∀ (N : sfWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A : sfWeilSheaf (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.obj.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.obj.carrier),
    SheetReturnRationalSpec D m hm X₀ l hl E N.obj A.obj α →
    ∀ (r : ℕ)
      (x : Spec (.of D.k) ⟶
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left)
      (hA : x ≫ localPositivePower
          ((constantExtensionDatum D m hm).geometricFrobenius
            (constantExtensionModel D m hm X₀)).hom r =
        localPositivePower (frobeniusPointIso (constantExtensionDatum D m hm)).hom r ≫ x)
      (hN : (x ≫ constantExtensionSheet D m hm X₀) ≫ localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m * (r + 1) - 1) =
        localPositivePower (frobeniusPointIso D).hom (m * (r + 1) - 1) ≫
          (x ≫ constantExtensionSheet D m hm X₀)),
      (sheetReturnStalkIso D m hm X₀ l hl E N.obj A.obj α x).hom ≫
          localFrobeniusOperator l E D hl (constantExtensionOriginalModel D m hm X₀)
            N.obj (x ≫ constantExtensionSheet D m hm X₀) (m * (r + 1) - 1) hN =
        localFrobeniusOperator l E (constantExtensionDatum D m hm) hl
          (constantExtensionModel D m hm X₀) A.obj x r hA ≫
          (sheetReturnStalkIso D m hm X₀ l hl E N.obj A.obj α x).hom

/-- The identification is natural on all underlying arrows and hence on Weil morphisms.
Source: Deligne, Weil II (1.1.10), p. 152
(blueprint: def-zl-sheet-return-data). -/
def SheetReturnStalkNaturality : Prop :=
  ∀ (N N' : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (A A' : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (α' : A'.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N'.carrier)
    (f : N ⟶ N') (g : A ⟶ A'),
    g.hom.f ≫ α'.hom = α.hom ≫ (sheetReturnRationalPull D m hm X₀ l hl E).map f.hom.f →
    ∀ (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left),
      HEq
        ((pointRationalFibre (constantExtensionDatum D m hm) l hl E).map
          ((@rationalDerivedPullback l _ E _ _ _ _ _ x
            (frobeniusPointPrimeInvertible (constantExtensionDatum D m hm) l hl)
            (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
              (constantExtensionModel D m hm X₀))).map g.hom.f) ≫
          (sheetReturnStalkIso D m hm X₀ l hl E N' A' α' x).hom)
        ((sheetReturnStalkIso D m hm X₀ l hl E N A α x).hom ≫
          (pointRationalFibre D l hl E).map
            ((@rationalDerivedPullback l _ E _ _ _ _ _
              (x ≫ constantExtensionSheet D m hm X₀)
              (frobeniusPointPrimeInvertible D l hl)
              (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).map
                f.hom.f))

/-- Scalar extension of a stalk, through the normalized point and pullback comparisons.
Source: Deligne, Weil II (1.1.3) and (1.1.8), pp. 150--151
(blueprint: def-zl-sheet-return-data). -/
def sheetReturnScalarStalk
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (N : sfWeilComplex D l hl Y₀ E) (N' : sfWeilComplex D l hl Y₀ L)
    (ε : N'.carrier ≅
      (sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N.carrier)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (pointRationalFibreScalarIso D l hl E L ι).symm.app
      (localDerivedStalk l E D hl Y₀ N x) ≪≫
    (pointRationalFibre D l hl L).mapIso
      ((rationalPullbackScalarComparison l E L ι x).app N.carrier ≪≫
        (rationalDerivedPullback l L x).mapIso ε.symm)

/-- The canonical sheet comparison commutes with finite extension of coefficients.
The carrier squares specify scalar extension, rather than arbitrary stalk isomorphisms.
Identity extensions are included; successive extensions use the same tensor associators.
Source: Deligne, Weil II (1.1.3), (1.1.8)--(1.1.10), pp. 150--152
(blueprint: def-zl-sheet-return-data). -/
def SheetReturnScalarCompatibility : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (N : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) E)
    (N' : sfWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) L)
    (A : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) E)
    (A' : sfWeilComplex (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) L)
    (α : A.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl E).obj N.carrier)
    (α' : A'.carrier ≅ (sheetReturnRationalPull D m hm X₀ l hl L).obj N'.carrier)
    (εN : N'.carrier ≅
      (sfRationalScalarExtension l E
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N.carrier)
    (εA : A'.carrier ≅
      (sfRationalScalarExtension l E
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj A.carrier),
    HEq (εA.hom ≫
      (sfRationalScalarExtension l E
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).left 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map α.hom ≫
      (@rationalPullbackScalarComparison l _ E _ _ _ L _ _ _ ι _ _
        (constantExtensionSheet D m hm X₀)
        (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀))
        (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).hom.app
          N.carrier)
      (α'.hom ≫ (sheetReturnRationalPull D m hm X₀ l hl L).map εN.hom) →
    ∀ (x : Spec (.of D.k) ⟶
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).left),
    HEq
      ((DerivedCategory.pointFdScalarExtension ι.toRingHom).map
        (sheetReturnStalkIso D m hm X₀ l hl E N A α x).hom ≫
        (sheetReturnScalarStalk D l hl E L ι
          (constantExtensionOriginalModel D m hm X₀) N N' εN
          (x ≫ constantExtensionSheet D m hm X₀)).hom)
      ((sheetReturnScalarStalk (constantExtensionDatum D m hm) l hl E L ι
          (constantExtensionModel D m hm X₀) A A' εA x).hom ≫
        (sheetReturnStalkIso D m hm X₀ l hl L N' A' α' x).hom)

/-- Subobjects and finite chains, with their actual quotient objects and every specified
pure weight. Equality is equality of subobjects, not chosen monomorphism representatives.
Source: Deligne, Weil II, p. 152 and (1.2.6), p. 154
(blueprint: def-zl-sheet-return-data). -/
def SheetReturnFiltrations (iota : Ω ≃+* ℂ)
    (R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω) [PreservesFiniteLimits R] : Prop :=
  ∀ N, ∃ e : Subobject N ≃o Subobject (R.obj N),
    (∀ U, e U = Subobject.mk (R.map U.arrow)) ∧
    (∀ (U V : Subobject N) (h : U ≤ V),
      Nonempty (R.obj (cokernel (Subobject.ofLE U V h)) ≅
        cokernel (Subobject.ofLE (e U) (e V) (e.monotone h))) ∧
      ∀ w : ℝ,
        (SfIsPunctuallyPureOfWeight D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) iota
            (cokernel (Subobject.ofLE U V h)) w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota
            (cokernel (Subobject.ofLE (e U) (e V) (e.monotone h))) w)) ∧
    (∀ t : ℕ, ∃ eF : (Fin (t + 1) →o Subobject N) ≃
        (Fin (t + 1) →o Subobject (R.obj N)),
      (∀ (s : Fin (t + 1) →o Subobject N) (i : Fin (t + 1)), (eF s) i = e (s i)) ∧
      (∀ s, (s 0 = ⊥ ∧ s (Fin.last t) = ⊤) ↔
        ((eF s) 0 = ⊥ ∧ (eF s) (Fin.last t) = ⊤)))

```

The original theorem retains its exact signature and is proved using the three
comparison statements and explicit categorical/weight arguments.

## Users

The read-only downstream.py scan found zero current Lean importers of the original
module. Every moved name was used only in that module. The DAG parents remain in place;
no node or module is withdrawn on the basis of the zero-importer observation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | A9 | Reexports every original public prerequisite and declaration, and proves its unchanged theorem. |
| Sheaf.Paper.ConstantExtensionReturnData | new in this delivery | Holds unchanged interfaces and the three proved normalization lemmas. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | new in this delivery | States only the normalized return equivalence construction. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | new in this delivery | States only ordered transport, rational naturality and scalar comparison. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | new in this delivery | States only local spectra, degree and conjugacy consequences. |

## Status

landed 20261025T161911-L-141922 2026-10-25 (merge of deliver/A9/Sheaf.Paper.ConstantExtensionReturnLocalOperators)
