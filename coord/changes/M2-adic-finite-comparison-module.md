# WeilConjectures.AdicSmoothDualizing.finitePowerComparison

## Reason

Profiling found repeated unfolding of the exact-derived realization in the finite
comparison's kernel check (11.1 seconds in one profile). The two named helper
isomorphisms cache the original site and intrinsic single-shift endpoints. The
outer functor is now written exactly as in the result type. The composed maps,
objects, normalization, hypotheses and conclusion are unchanged.

After these endpoint and transparency improvements the combined module still
exceeded 60 seconds. Extract its existing finite-comparison declarations into
`Sheaf.Paper.AdicSmoothDualizingFiniteComparison`, publicly reexported by the item.
This moves the original projection and realization obligations without adding a
hole or a new mathematical assertion. All old qualified names and signatures
remain. The finite-power block within the old interval below is extracted
separately, as documented by `M2-adic-finite-power-module.md`.

## Old

The contiguous old finite-model interval, including its already separately
recorded etale-power declarations:

```lean
/-- The positive completed coefficient line already used by the signed twists.
Source: the corollary proof, completed coefficient object and its Tate power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev line (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistPower T
    (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension T)
    (purTwistIntegralModule T P.coefficients.l P.extension) d

/-- Pure completed-coefficient root tensors in that line, including its zero power.
Source: the corollary proof, the projection-normalized integral Tate line
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def generator (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted
      P.coefficients.l P.extension T).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W) →
      (line P T d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction T P.coefficients.l P.extension W).toSMul a
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x 0))
  | d + 2, x => SheafOfModules.siteSheafTensorTmul
      (line P T (d + 1)) (purTwistIntegralModule T P.coefficients.l P.extension) W
      (generator P T W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x (Fin.last (d + 1))))

/-- The finite projection of a completed Tate power is fixed on every local root
and completed scalar, rather than chosen as an unnormalized line isomorphism.
Source: corollary proof, reduction to the normalized finite coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: project completed scalars to the finite quotient. The integral root tensor
is defined over the discrete constants; its quotient is purTwistFiniteOne.
The tensor universal property gives the first-power map and its tensor powers.
At power zero use the coefficient projection. These generators generate locally,
so the displayed equations determine the morphism uniquely, including on the empty site. -/
theorem existsUnique_lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! p : line P T d ⟶
        (scalarReductionRestriction P.coefficients.l P.extension T n).obj
          (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)),
      ∀ (W : T.ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted
          P.coefficients.l P.extension T).obj.obj W)
        (x : Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W),
        p.val.app W (generator P T W a d x) =
          @SMul.smul ((integralCoefficientSheaf
              P.coefficients.l P.extension T n).obj.obj W)
            ((finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W)
            (
              (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W
            ).isModule.toSMul
            ((completedIntegralCommRingProjectionUnrestricted
              P.coefficients.l P.extension T n).hom.app W a)
            (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 d x) := by
  sorry

/-- The fixed positive finite level, with the original global conventions unchanged.
Source: corollary proof, reductions modulo every positive power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }

/-- The projection selected by its unique root-tensor equations.
Source: corollary proof, integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_lineProjection P T n d).exists.choose

/-- Reassociation of the nonnegative etale Tate powers, with the unit at degree zero.
Source: corollary proof and the detailed coefficient-twist conventions
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etalePowerProduct (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates d ⊗
      finiteEtaleTateLine T P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates

/-- The underlying sheaf tensor unitor, before endpoint presentation transport.
Source: corollary, zero-power tensor normalization
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerUnitor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  λ_ (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
    P.diagonalExponent_annihilates)

/-- The zero power-step has the specified tensor-unitor data.
Source: corollary, coefficient unit at power zero
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the zero finite Tate power and the tensor unit are the same constant regular
module sheaf, obtained by sheafifying that constant presheaf. Thus the unitor has
exactly these endpoints. Heterogeneous equality fixes its data uniquely. -/
theorem existsUnique_etalePowerZero (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    ∃! e : etalePowerProduct P T 0 ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates 1,
      HEq e (etalePowerUnitor P T) := by
  refine ⟨etalePowerUnitor P T, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- A subsequent sheaf tensor power is literally the preceding power tensor the line.
Source: corollary, positive tensor powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: this is the successor clause of finiteEtaleTateTwist, with the same sheaf
monoidal structure. Its comparison is identity, so the prescribed data is unique. -/
theorem existsUnique_etalePowerPositive (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (d : ℕ) :
    ∃! e : etalePowerProduct P T (d + 1) ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 2),
      HEq e (Iso.refl (etalePowerProduct P T (d + 1))) := by
  refine ⟨Iso.refl _, HEq.rfl, ?_⟩
  intro e he
  exact eq_of_heq he

/-- The power-step comparison is exactly the tensor unitor at zero and identity
thereafter. Its specified data is preserved by the endpoint transports.
Source: corollary proof, positive tensor powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerStep (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (d : ℕ) → etalePowerProduct P T d ≅
      finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
        P.diagonalExponent_annihilates (d + 1)
  | 0 => (existsUnique_etalePowerZero P T).exists.choose
  | d + 1 => (existsUnique_etalePowerPositive P T d).exists.choose

/-- Every nonnegative finite Tate power is flat, including the coefficient unit.
Source: corollary proof and finite Tate descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the normalized root line is locally free of rank one because ell is invertible.
Its positive tensor powers remain locally free of rank one; power zero is the unit.
Tensoring with a locally free rank-one sheaf is locally the identity and hence exact. -/
theorem etalePowerFlat (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d) := by
  let e := finiteEtaleTateTensorFamily T P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
    P.diagonalExponent_annihilates hT
  have h := (e.tensorInverse (d : ℤ)).flat
  dsimp only [e] at h
  rw [finiteEtaleTateTensorFamily_obj] at h
  exact h

/-- The finite Tate sheaf placed in degree zero.
Source: the corollary's finite coefficient model
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etaleSingle (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates d)

/-- The existing ordered derived tensor, with its site and coefficients explicit.
Source: the corollary's ordered tensor convention
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev etaleTensor (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) T

/-- The comparison family is fixed by the actual tensor map, shift comparison,
flat single-complex comparison, and sheaf-power step. HEq only transports their
endpoint presentations; it fixes the data of every factor.
Source: the corollary's normalized finite powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: at zero use the zero-shift unitor. At the successor tensor the preceding
comparison with the shifted root line. Move the two shifts outside tensor using
derivedTensorShiftIso, use singleFunctorObjTensorIso for the flat Tate power,
then etalePowerStep and PurityFiniteSetting.frameDegreeNext. These maps have the displayed
endpoints by unfolding the definitions. Induction constructs the family. HEq fixes each factor
uniquely; induction therefore also proves uniqueness of the whole family. -/
structure EtalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) where
  comparison : (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧
  normalized :
    letI := Sheaf.monoidalCategory T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    HEq (comparison 0) (((shiftFunctorZero _ ℤ).app (P.diagonalTwistEtale T 0)).symm) ∧
      ∀ d : ℕ,
        ∃ (e₁ : P.diagonalTwistEtale T (d + 1) ≅
              ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧))
          (e₂ : ((etaleTensor P T).obj ((etaleSingle P T d)⟦2 * (d : ℤ)⟧)).obj
                ((etaleSingle P T 1)⟦(2 : ℤ)⟧) ≅
              (((etaleTensor P T).obj (etaleSingle P T d)).obj
                (etaleSingle P T 1))⟦2 * (d : ℤ) + 2⟧)
          (e₃ : ((etaleTensor P T).obj (etaleSingle P T d)).obj (etaleSingle P T 1) ≅
              (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d))
          (e₄ : (DerivedCategory.singleFunctor _ 0).obj (etalePowerProduct P T d) ≅
              etaleSingle P T (d + 1)),
          HEq e₁ ((Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) T
            ((etaleSingle P T 1)⟦(2 : ℤ)⟧)).mapIso (comparison d)) ∧
          HEq e₂ (Etale.derivedTensorShiftIso (ModuleCat.{u + 1} P.Coefficient) (X := T)
            (etaleSingle P T d) (etaleSingle P T 1) (2 * (d : ℤ)) 2) ∧
          HEq e₃ (Etale.singleFunctorObjTensorIso
            (A := ModuleCat.{u + 1} P.Coefficient) (X := T)
            (finiteEtaleTateTwist T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates d)
            (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
              P.diagonalExponent_annihilates) (etalePowerFlat P T hT d)) ∧
          HEq e₄ ((DerivedCategory.singleFunctor _ 0).mapIso (etalePowerStep P T d)) ∧
          comparison (d + 1) = e₁ ≪≫ e₂ ≪≫
            (shiftFunctor _ (2 * (d : ℤ) + 2)).mapIso (e₃ ≪≫ e₄) ≪≫
            eqToIso (congrArg (fun j : ℤ ↦ (etaleSingle P T (d + 1))⟦j⟧)
              (PurityFiniteSetting.frameDegreeNext d))

/-- The canonical finite tensor presentation, with its full normalization stored
in its type, is uniquely determined.
Source: the corollary's ordered Tate powers
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: construct the comparison by induction from the zero-shift unitor using
exactly the four normalized factors. HEq fixes each factor, so induction proves
uniqueness of the comparison. The normalization proof is unique by proof irrelevance. -/
theorem existsUnique_etalePowerPresentation (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    ∃! e : EtalePowerPresentation P T hT, True := by
  sorry

/-- The canonical ordered-tensor family selected by its uniquely determining recursion.
Source: the corollary's finite Tate presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def etalePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    (d : ℕ) → P.diagonalTwistEtale T d ≅ (etaleSingle P T d)⟦2 * (d : ℤ)⟧ :=
  ((existsUnique_etalePowerPresentation P T hT).exists.choose).comparison

attribute [local irreducible] etalePowerComparison

set_option backward.isDefEq.respectTransparency false in
/-- The unique finite site comparison fixed by the root-limit projections.
Source: corollary proof, finite normalization; finite Tate site descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: finite Tate site descent gives the comparison for the annihilator ell^(n+1).
The displayed projection formula is its defining normalization. Local root lifts
and pure tensor generation make two such comparisons equal. -/
theorem existsUnique_rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (_aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    ∃! b : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).obj
        (finiteEtaleTateTwist T (levelSetting P n).diagonalExponent
          (levelSetting P n).Coefficient (levelSetting P n).diagonalExponent_annihilates d) ≅
        finiteTateProSheaf P.coefficients.l P.extension n T d,
      IsFiniteTateSiteComparison P.coefficients.l P.extension n T n
        (levelSetting P n).diagonalExponent_annihilates d b := by
  sorry

/-- The finite comparison selected from its unique root-projection characterization.
Source: corollary proof, finite coefficient comparisons
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :=
  (existsUnique_rootComparison P T aT n d).exists.choose

/-- A realization comparison fixes each scalar-unit section of the original sheaf.
Source: the corollary's fixed-to-intrinsic finite coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsScalarUnitRealization (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : proEtaleRingModules T (proEtaleConstantRing T A))
    (e : (sfIntrinsicModuleEquivalence T A).functor.obj M ≅ N) : Prop :=
  ∀ (W : T.ProEtᵒᵖ) (y : M.obj.obj W),
    HEq (e.hom.val.app W (sfIntrinsicRealizationUnit T A M W y)) y

/-- The finite fixed-scalar realization is fixed on every scalar-unit section.
Source: corollary proof, canonical finite coefficient presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: restriction to the constant scalar action is inverse to the canonical
finite coefficient realization. The realization unit sends a section to its
scalar-unit generator. Extend the identity on these sections by local scalar
linearity and sheafification. The two inverse composites are identities on those
generators, which also proves uniqueness. -/
theorem existsUnique_finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d) ≅
        finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ),
      IsScalarUnitRealization T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        (finiteTateProSheaf P.coefficients.l P.extension n T d)
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)) e := by
  sorry

/-- The preceding canonical realization, with no generator or orientation choice.
Source: corollary proof, finite comparison
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_finiteRealization P T n d).exists.choose

attribute [local irreducible] finiteRealization

/-- Exact functors carry shifted single complexes to the shifted single image.
The data is the standard shift comparison followed by the single-complex comparison.
Source: the corollary's exact coefficient and site transports
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def exactSingleShiftIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (M : C) (j : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M))⟦j⟧ :=
  (F.mapDerivedCategory.commShiftIso j).app _ ≪≫
    (shiftFunctor _ j).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)

attribute [local irreducible] exactSingleShiftIso

set_option backward.isDefEq.respectTransparency false in
/-- Canonical comparison from the finite purity orientation's ordered shifted tensor
model to the specified intrinsic finite Tate power placed in degree -2d.
Source: corollary proof, normalized finite purity at each reduction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)))⟦2 * (d : ℤ)⟧ :=
  Functor.mapIso (Functor.mapDerivedCategory (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor)
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).mapDerivedCategory.mapIso
      (etalePowerComparison (levelSetting P n) T
        ((levelSetting P n).diagonalExponent_isUnit aT) d) ≪≫
      exactSingleShiftIso (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T) _ (2 * (d : ℤ)) ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (rootComparison P T aT n d))) ≪≫
    exactSingleShiftIso (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor _
      (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (finiteRealization P T n d))

```

## New

The finite-comparison declarations, in their new module:

```lean
/-- The positive completed coefficient line already used by the signed twists.
Source: the corollary proof, completed coefficient object and its Tate power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev line (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistPower T
    (R := completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension T)
    (purTwistIntegralModule T P.coefficients.l P.extension) d

/-- Pure completed-coefficient root tensors in that line, including its zero power.
Source: the corollary proof, the projection-normalized integral Tate line
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def generator (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (W : T.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted
      P.coefficients.l P.extension T).obj.obj W) :
    (d : ℕ) → (Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W) →
      (line P T d).val.obj W
  | 0, _ => a
  | 1, x => @SMul.smul _ _ (purTwistIntegralAction T P.coefficients.l P.extension W).toSMul a
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x 0))
  | d + 2, x => SheafOfModules.siteSheafTensorTmul
      (line P T (d + 1)) (purTwistIntegralModule T P.coefficients.l P.extension) W
      (generator P T W a (d + 1) (fun i ↦ x i.castSucc))
      (purTwistIntegralTensor T P.coefficients.l P.extension W 1 (x (Fin.last (d + 1))))

/-- The finite projection of a completed Tate power is fixed on every local root
and completed scalar, rather than chosen as an unnormalized line isomorphism.
Source: corollary proof, reduction to the normalized finite coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: project completed scalars to the finite quotient. The integral root tensor
is defined over the discrete constants; its quotient is purTwistFiniteOne.
The tensor universal property gives the first-power map and its tensor powers.
At power zero use the coefficient projection. These generators generate locally,
so the displayed equations determine the morphism uniquely, including on the empty site. -/
theorem existsUnique_lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! p : line P T d ⟶
        (scalarReductionRestriction P.coefficients.l P.extension T n).obj
          (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)),
      ∀ (W : T.ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted
          P.coefficients.l P.extension T).obj.obj W)
        (x : Fin d → (purTwistZlOne T P.coefficients.l).obj.obj W),
        p.val.app W (generator P T W a d x) =
          @SMul.smul ((integralCoefficientSheaf
              P.coefficients.l P.extension T n).obj.obj W)
            ((finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W)
            (
              (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)).val.obj W
            ).isModule.toSMul
            ((completedIntegralCommRingProjectionUnrestricted
              P.coefficients.l P.extension T n).hom.app W a)
            (finiteTateProPowerGenerator P.coefficients.l P.extension n T W 1 d x) := by
  sorry

/-- The fixed positive finite level, with the original global conventions unchanged.
Source: corollary proof, reductions modulo every positive power
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev levelSetting (P : PurityFiniteSetting.{u}) (n : ℕ) : PurityFiniteSetting.{u} :=
  { P with level := n + 1, level_pos := Nat.succ_pos n }

/-- The projection selected by its unique root-tensor equations.
Source: corollary proof, integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def lineProjection (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_lineProjection P T n d).exists.choose

attribute [local irreducible] etalePowerComparison

set_option backward.isDefEq.respectTransparency false in
/-- The unique finite site comparison fixed by the root-limit projections.
Source: corollary proof, finite normalization; finite Tate site descent
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: finite Tate site descent gives the comparison for the annihilator ell^(n+1).
The displayed projection formula is its defining normalization. Local root lifts
and pure tensor generation make two such comparisons equal. -/
theorem existsUnique_rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (_aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    ∃! b : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).obj
        (finiteEtaleTateTwist T (levelSetting P n).diagonalExponent
          (levelSetting P n).Coefficient (levelSetting P n).diagonalExponent_annihilates d) ≅
        finiteTateProSheaf P.coefficients.l P.extension n T d,
      IsFiniteTateSiteComparison P.coefficients.l P.extension n T n
        (levelSetting P n).diagonalExponent_annihilates d b := by
  have hpow : IsUnit ((P.coefficients.l ^ (n + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa [levelSetting, PurityFiniteSetting.diagonalExponent] using
      (levelSetting P n).diagonalExponent_isUnit _aT
  have hl : IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
    apply (isUnit_pow_iff (Nat.ne_of_gt (Nat.zero_lt_succ n))).mp
    simpa [Nat.succ_eq_add_one] using hpow
  obtain ⟨b, hb, _⟩ := finite_tate_site_descent P.coefficients.l P.extension n
  refine ⟨b T hl n (levelSetting P n).diagonalExponent_annihilates d,
    hb T hl n (levelSetting P n).diagonalExponent_annihilates d, ?_⟩
  intro b' hb'
  apply Iso.ext
  apply finiteTate_local_root_tensors_hom_ext P.coefficients.l P.extension n T hl n
    (levelSetting P n).diagonalExponent_annihilates d
  intro U W v a z x hx
  exact (hb' U W v a z x hx).trans
    ((hb T hl n (levelSetting P n).diagonalExponent_annihilates d U W v a z x hx).symm)

/-- The finite comparison selected from its unique root-projection characterization.
Source: corollary proof, finite coefficient comparisons
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def rootComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :=
  (existsUnique_rootComparison P T aT n d).exists.choose

/-- A realization comparison fixes each scalar-unit section of the original sheaf.
Source: the corollary's fixed-to-intrinsic finite coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsScalarUnitRealization (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : proEtaleRingModules T (proEtaleConstantRing T A))
    (e : (sfIntrinsicModuleEquivalence T A).functor.obj M ≅ N) : Prop :=
  ∀ (W : T.ProEtᵒᵖ) (y : M.obj.obj W),
    HEq (e.hom.val.app W (sfIntrinsicRealizationUnit T A M W y)) y

/-- The finite fixed-scalar realization is fixed on every scalar-unit section.
Source: corollary proof, canonical finite coefficient presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: restriction to the constant scalar action is inverse to the canonical
finite coefficient realization. The realization unit sends a section to its
scalar-unit generator. Extend the identity on these sections by local scalar
linearity and sheafification. The two inverse composites are identities on those
generators, which also proves uniqueness. -/
theorem existsUnique_finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d) ≅
        finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ),
      IsScalarUnitRealization T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
        (finiteTateProSheaf P.coefficients.l P.extension n T d)
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)) e := by
  sorry

/-- The preceding canonical realization, with no generator or orientation choice.
Source: corollary proof, finite comparison
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (n d : ℕ) :=
  (existsUnique_finiteRealization P T n d).exists.choose

attribute [local irreducible] finiteRealization

/-- Exact functors carry shifted single complexes to the shifted single image.
The data is the standard shift comparison followed by the single-complex comparison.
Source: the corollary's exact coefficient and site transports
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def exactSingleShiftIso {C : Type u₁} [Category.{v₁} C] [Abelian C]
    [HasDerivedCategory.{w₁} C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (M : C) (j : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor D 0).obj (F.obj M))⟦j⟧ :=
  (F.mapDerivedCategory.commShiftIso j).app _ ≪≫
    (shiftFunctor _ j).mapIso ((F.mapDerivedCategorySingleFunctor 0).app M)

attribute [local irreducible] exactSingleShiftIso

/-- The exact single-complex comparison in the literal intrinsic-derived coordinates.
This exposes its endpoints without repeatedly unfolding the derived equivalence.
Source: the corollary's exact coefficient transport
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def intrinsicExactSingleShiftIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) (j : ℤ) :
    (sfIntrinsicDerivedEquivalence T A).functor.obj
        (((DerivedCategory.singleFunctor _ 0).obj M)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((sfIntrinsicModuleEquivalence T A).functor.obj M))⟦j⟧ :=
  exactSingleShiftIso (sfIntrinsicModuleEquivalence T A).functor M j

attribute [local irreducible] intrinsicExactSingleShiftIso

/-- The site part of the finite-power comparison, with its normalized root target.
This is the same three factors as in the original finitePowerComparison.
Source: the corollary's finite normalized Tate presentation
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def finiteSitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (levelSetting P n).diagonalTwist T d ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteTateProSheaf P.coefficients.l P.extension n T d))⟦2 * (d : ℤ)⟧ :=
  (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T).mapDerivedCategory.mapIso
    (etalePowerComparison (levelSetting P n) T
      ((levelSetting P n).diagonalExponent_isUnit aT) d) ≪≫
    exactSingleShiftIso (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) T) _ (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (rootComparison P T aT n d))

attribute [local irreducible] finiteSitePowerComparison

/-- Canonical comparison from the finite purity orientation's ordered shifted tensor
model to the specified intrinsic finite Tate power placed in degree -2d.
Source: corollary proof, normalized finite purity at each reduction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finitePowerComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        (finiteCoefficientTwist P.coefficients.l P.extension T n (d : ℤ)))⟦2 * (d : ℤ)⟧ :=
  (sfIntrinsicDerivedEquivalence T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.mapIso
    (finiteSitePowerComparison P T aT n d) ≪≫
    intrinsicExactSingleShiftIso T
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) _
      (2 * (d : ℤ)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (finiteRealization P T n d))

```

The item now publicly imports the new module. Its statements and definitions
continue to see the old declarations through this import.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | M2 | same finite model, imported from its own module |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | same names and signatures through public reexport |
| Sheaf.Paper.RationalSmoothPurityFiniteTrace | unclaimed | same names and signatures through public reexport |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | same names and signatures through public reexport |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | same names and signatures through public reexport |

There are no edits to consumer sources. Consumer verification and baseline
limitations are recorded in report.md. The DAG's new construction node owns the
moved declarations; the corollary's dependency route includes this construction.

## Status

landed 20261028T055716-L-798391 2026-10-28 (merge of deliver/M2/Sheaf.Paper.AdicSmoothDualizingComplexes)
