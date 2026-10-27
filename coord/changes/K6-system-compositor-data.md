# AlgebraicGeometry.ProEtale.SemilinearProperOpen compositor data

## Reason

The finite evaluation lemma must mention the system word and its prescribed support
transports, while the normalization theorem must import that lemma. Move the ten
existing data declarations into a shared module to avoid a cycle. Their names,
signatures, attributes and defining terms stay identical. The original module
publicly imports the shared data module, preserving its public API.
This is a module ownership change, with no change in the meaning of any definition
or target statement. No source-library module is edited.

## Old

Module: `Sheaf.Paper.SystemCompatibleCompositorNormalization`.

```lean
/-- The actual three-factor proper/open word, on the ordinary derived system category.
Source: Stacks 0F7J, the four displayed identifications
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compatibleCompositorWord {X V XB Y YB Z : Scheme.{u}}
    (j : X ⟶ V) (b : V ⟶ XB) (q : V ⟶ Y) (p : XB ⟶ YB)
    (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact b] [QuasiCompact i] [IsProper q] [IsProper p]
    (h : b ≫ p = q ≫ i) :
    (J C τ j ⋙ R C τ q) ⋙ (J C τ i ⋙ R C τ s) ⟶
      J C τ (j ≫ b) ⋙ R C τ (p ≫ s) :=
  (Functor.associator (J C τ j) (R C τ q) (J C τ i ⋙ R C τ s)).hom ≫
    Functor.whiskerLeft (J C τ j)
      ((Functor.associator (R C τ q) (J C τ i) (R C τ s)).inv ≫
        Functor.whiskerRight (gamma C τ b q p i h) (R C τ s) ≫
        (Functor.associator (J C τ b) (R C τ p) (R C τ s)).hom ≫
        Functor.whiskerLeft (J C τ b) (sComp C τ p s).hom) ≫
    (Functor.associator (J C τ j) (J C τ b) (R C τ (p ≫ s))).inv ≫
    Functor.whiskerRight (jComp C τ j b).hom (R C τ (p ≫ s))

/-- The n-th level in the same constant-ring module presentation used by the mate API.
Source: Zheng 4.1, 4.10; Stacks 0F7J
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
abbrev compositorLevel (X : Scheme.{u}) (n : ℕ) :=
  E C τ n X ⋙ StrictTower.ev (C n) X 0

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Open evaluation, including the constant-tower presentation comparison.
Source: Zheng 4.10; Stacks 03DI
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorLevelJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    J C τ j ⋙ compositorLevel C τ X n ≅ compositorLevel C τ U n ⋙
      (StrictTower.moduleJ (C n) j).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (evalJ C τ n j) (StrictTower.ev (C n) X 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E C τ n U) (StrictTower.evalJ (C n) j 0) ≪≫
    (Functor.associator _ _ _).symm

/-- Direct-image evaluation with its prescribed adjunction mate.
Source: Zheng 4.10; Stacks 07A4
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorLevelR {U X : Scheme.{u}} (q : U ⟶ X) (n : ℕ) :
    R C τ q ⋙ compositorLevel C τ X n ≅ compositorLevel C τ U n ⋙
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@asIso _ _ _ _ (evalR C τ n q) (evalR_isIso C τ n q))
      (StrictTower.ev (C n) X 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E C τ n U)
      (@asIso _ _ _ _ (StrictTower.evalR (C n) q 0) (StrictTower.evalR_isIso (C n) q 0)) ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical comparison for one compact-support factor, retaining both evaluations.
Source: Stacks 0F7J; Zheng 4.10
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorSupportEvaluation {X V Y : Scheme.{u}} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    (J C τ j ⋙ R C τ q) ⋙ compositorLevel C τ Y n ≅
      compositorLevel C τ X n ⋙ ((StrictTower.moduleJ (C n) j).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J C τ j) (compositorLevelR C τ q n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compositorLevelJ C τ j n)
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor ≪≫
    Functor.associator _ _ _

/-- Transport one compact-support factor using the canonical proper mate and open unit.
The supplied input identification is propagated functorially, never replaced by a choice.
Source: Stacks 099R, 09AF and 0F7J
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorSupportTransport {X V Y : Scheme.{u}} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion j] [IsProper q] (n : ℕ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (φ : C n →+* Λ) (L : FiniteSiteTower.DE Λ X) (M : Derived C τ X)
    (e : (StrictTower.HD (C n) X Λ φ).obj L ≅ (compositorLevel C τ X n).obj M) :
    (StrictTower.HD (C n) Y Λ φ).obj
        ((FiniteSiteTower.PE Λ q).obj ((FiniteSiteTower.JE Λ j).obj L)) ≅
      (compositorLevel C τ Y n).obj ((J C τ j ⋙ R C τ q).obj M) :=
  (@asIso _ _ _ _ (StrictTower.hR (C n) q Λ φ)
      (StrictTower.hR_isIso (C n) q Λ φ)).app ((FiniteSiteTower.JE Λ j).obj L) ≪≫
    (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor.mapIso
      ((StrictTower.hJ (C n) j Λ φ).app L) ≪≫
    ((StrictTower.moduleJ (C n) j).mapDerivedCategory ⋙
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor).mapIso e ≪≫
    (compositorSupportEvaluation C τ j q n).symm.app M

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Input transport for the iterated compact-support word, with all four geometric factors.
Source: Stacks 0F7J, 099R and 09AF
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorFiniteSource {X V Y YB Z : Scheme.{u}}
    (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsProper q] [IsProper s]
    (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorSupportTransport C τ i s n w.Λ w.φ
    ((FiniteSiteTower.PE w.Λ q).obj ((FiniteSiteTower.JE w.Λ j).obj w.origin.L))
    ((J C τ j ⋙ R C τ q).obj M)
    (compositorSupportTransport C τ j q n w.Λ w.φ w.origin.L M
      (StrictTower.originIso (C n) w))

/-- Output transport for the composite compactification, using the very same origin witness.
Source: Stacks 0F7J, 099R and 09AF
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorFiniteTarget {X V XB YB Z : Scheme.{u}}
    (j : X ⟶ V) (b : V ⟶ XB) (p : XB ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsProper p] [IsProper s]
    (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorSupportTransport C τ (j ≫ b) (p ≫ s) n w.Λ w.φ w.origin.L M
    (StrictTower.originIso (C n) w)

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- Bounded constructibility at one level, using the recorded fixed-module predicate.
The interval belongs to this level only. Source: blueprint, the domain of the compositor
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorBoundedConstructible (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : _root_.DerivedCategory (StrictTower.Modules (ULift.{u + 1, u} A) X)) : Prop :=
  (∀ r : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1, u} A)
    ((Scheme.proEtaleModuleRestriction X A).obj
      ((_root_.DerivedCategory.homologyFunctor _ r).obj K))) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ r : ℤ, (r < a ∨ b < r) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj K)

variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]

/-- The full levelwise bounded constructible domain; there is no uniform bound,
normalization or Tor-amplitude requirement. Source: blueprint, final sentence
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compatibleCompositorDomain (X : Scheme.{u})
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X) :
    Prop :=
  ∀ n : ℕ, @compositorBoundedConstructible X
    (Padic.coefficientExtensionRing l E₀ (n + 1)) _
    (Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n))
    ((compositorLevel (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) X n).obj M)

```

## New

Module: `Sheaf.Paper.SystemCompatibleCompositorData`.
The exact declaration text above is moved unchanged. The original module reexports it:

```lean
public import Sheaf.Paper.SystemCompatibleCompositorData
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SystemCompatibleCompositorNormalization | K6 | Publicly imports the unchanged data; proves normalization from finite evaluation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | no local claim recorded | Same public declarations and definition bodies through the original import; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | no local claim recorded | Same public declarations and definition bodies through the original import; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | no local claim recorded | Transitive import API preserved; no adaptation. |
| Sheaf.Paper.SystemCompositorFiniteWordEvaluation | new K6 module | Imports the shared definitions to state the finite word equation. |

The downstream list was read using tools/downstream.py with all ten declaration names.
No existing consumer requires a forced adaptation. The owner node's Lean module/file
attachment moves with the unchanged data. The normalization node now attaches only
its theorem, so it agrees with the actual definition owner.

## Status

landed 20261025T213034-L-277426 2026-10-25 (merge of deliver/K6/Sheaf.Paper.SystemCompatibleCompositorNormalization)
