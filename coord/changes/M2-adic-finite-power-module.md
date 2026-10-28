# WeilConjectures.AdicSmoothDualizing finite-power declarations

## Reason

After simplifying the finite-unit bound and level-setting transparency, the item
compiled in 47.8 seconds, but its delivery compile with declaration probes still
took 62.3 seconds. Extract the self-contained finite-power block into
`Sheaf.Paper.AdicSmoothDualizingFinitePowers`. This is the file split allowed
after improving slow definitions. Every qualified name, signature and body in
this block is preserved, including the existing presentation-uniqueness hole.
The original module publicly imports the new module. The existing definition
node `def-sf-etale-power-presentation` now records the new module. No new
mathematical statements or holes are introduced.

## Old

The following block was in `Sheaf.Paper.AdicSmoothDualizingComplexes`:

```lean
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
```

## New

The identical block is in `Sheaf.Paper.AdicSmoothDualizingFinitePowers`:

```lean
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
```

The original module adds `public import Sheaf.Paper.AdicSmoothDualizingFinitePowers`.
Its statement and all remaining declarations retain their original signatures.

## Users

The current downstream scan for all eleven moved declaration names finds only
the original module and `PurityOrientationDatum`; the other direct importers
still see the identical declarations through the original module's public import.
No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | M2 | imports identical finite-power declarations |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | same etalePowerComparison through public import |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | same public interface |
| Sheaf.Paper.RationalSmoothPurityFiniteTrace | unclaimed | same public interface |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | same public interface |

## Status

landed 20261028T055716-L-798391 2026-10-28 (merge of deliver/M2/Sheaf.Paper.AdicSmoothDualizingComplexes)
