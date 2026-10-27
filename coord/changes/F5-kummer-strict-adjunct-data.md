# AlgebraicGeometry.ProEtale.kummerStrictAdjunctCompatibilityStatement

## Reason

Move four existing definitions from `Sheaf.Paper.KummerStrictAdjunctCompatibility`
to `Sheaf.Paper.KummerStrictAdjunctData`, preserving every name, signature,
attribute and definition body. The original module publicly imports the new data
module and keeps its existing public import. The normalization theorem can then
refer to the actual named Kummer class without importing the theorem it proves.
Direct specialization with an expanded duplicate of that class exceeded 120 s
in kernel checking even after the proof was assembled over abstract categories.
The normalized-target predicate also retains coefficient constructions as parameters.
No target or mathematical definition changes meaning.

The moved declarations are `KummerTargetAdjunctCompatibility`, `kummerComparedUnit`,
`kummerRootNormalization` and `kummerStrictAdjunctCompatibilityStatement` in
`AlgebraicGeometry.ProEtale`. Only documentation blueprint labels change.

## Old

In `Sheaf.Paper.KummerStrictAdjunctCompatibility`:

```lean
@[irreducible] def KummerTargetAdjunctCompatibility
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ U ≅ rootsTower)
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
    (∀ n, rootNorm H roots n (t n)) ∧
    ∀ (n : ℕ) (S : A)
      (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
        (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S)),
      a.hom = diagonalDerivedSingleCounit ℓ L D S →
      ∀ (Q : C n) (s : (D.ordinary.E.obj S).obj (op n) ≅ (F n).obj Q)
        (g : S ⟶ (V n).obj Q),
        HEq (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) g →
        ∀ (f : Ext S M 1) (e : Ext Q (P n) 2),
          exactFunctorExtImage (F n) e =
            (Ext.mk₀ s.inv).comp
              (((Ext.homEquiv.symm (a.inv ≫ D.T.map f.hom ≫ b.hom)).mapExactFunctor
                ((evaluation ℕᵒᵖ B).obj (op n))).comp
                (Ext.mk₀ (t n).hom) (add_zero 2)) (zero_add 2) →
          (Ext.mk₀ g).comp (e.mapExactFunctor (V n)) (zero_add 2) = -(f.comp (κ n) rfl)

/-- The positive Kummer unit after the comparison isomorphism on units.
This is the actual Ext composite, named to share its coefficient constructions
rather than checking the concrete sheaf abelian structures at each occurrence.
Source: the units-comparison composite in the diagonal tower proof, step (4)
(blueprint: lem-sfb-kummer-strict-target-transport). -/
@[irreducible] def kummerComparedUnit (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (n : ℕ) :
    Ext.{u + 1} ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
      ((cartierForget (diagonalResidue.{u} ℓ n) W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) 1 :=
  (Ext.mk₀ (cartierUnitsComparison W)).comp
    (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1))) (zero_add 1)

/-- The actual roots comparison equation, named before derived specialization.
Source: diagonal tower system proof, step (3), target normalization
(blueprint: lem-sfb-kummer-strict-target-transport).
This is precisely the canonical underlying-map equation, with no chosen data. -/
def kummerRootNormalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (H : DiagonalSystems ℓ W)
    (roots : H ⋙ diagonalForget ℓ W ≅
      Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (n : ℕ) (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) : Prop :=
  HEq ((diagonalForget ℓ W).map t.hom)
    (roots.hom.app (op n) ≫ cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)))

/-- The concrete compatibility formula, with its coefficient expressions shared.
This is a real proposition definition and chooses no data.
(blueprint: lem-sfb-kummer-strict-adjunct-compatibility). -/
@[irreducible] def kummerStrictAdjunctCompatibilityStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  KummerTargetAdjunctCompatibility
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := fun n => diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := fun n => kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := fun n => diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := fun n => diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := fun n => diagonalFiniteToPadicColimits ℓ n W)
    (Vadd := fun n => cartierForgetAdditive (diagonalResidue.{u} ℓ n) W)
    (Vlim := fun n => cartierForgetLimits (diagonalResidue.{u} ℓ n) W)
    (Vcolim := fun n => cartierForgetColimits (diagonalResidue.{u} ℓ n) W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)
```

## New

In `Sheaf.Paper.KummerStrictAdjunctData`:

```lean
@[irreducible] def KummerTargetAdjunctCompatibility
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ U ≅ rootsTower)
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)),
    (∀ n, rootNorm H roots n (t n)) ∧
    ∀ (n : ℕ) (S : A)
      (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
        (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S)),
      a.hom = diagonalDerivedSingleCounit ℓ L D S →
      ∀ (Q : C n) (s : (D.ordinary.E.obj S).obj (op n) ≅ (F n).obj Q)
        (g : S ⟶ (V n).obj Q),
        HEq (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) g →
        ∀ (f : Ext S M 1) (e : Ext Q (P n) 2),
          exactFunctorExtImage (F n) e =
            (Ext.mk₀ s.inv).comp
              (((Ext.homEquiv.symm (a.inv ≫ D.T.map f.hom ≫ b.hom)).mapExactFunctor
                ((evaluation ℕᵒᵖ B).obj (op n))).comp
                (Ext.mk₀ (t n).hom) (add_zero 2)) (zero_add 2) →
          (Ext.mk₀ g).comp (e.mapExactFunctor (V n)) (zero_add 2) = -(f.comp (κ n) rfl)

/-- The positive Kummer unit after the comparison isomorphism on units.
This is the actual Ext composite, named to share its coefficient constructions
rather than checking the concrete sheaf abelian structures at each occurrence.
Source: the units-comparison composite in the diagonal tower proof, step (4)
(blueprint: def-sfb-kummer-strict-adjunct-data). -/
@[irreducible] def kummerComparedUnit (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (n : ℕ) :
    Ext.{u + 1} ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
      ((cartierForget (diagonalResidue.{u} ℓ n) W).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) W)) 1 :=
  (Ext.mk₀ (cartierUnitsComparison W)).comp
    (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1))) (zero_add 1)

/-- The actual roots comparison equation, named before derived specialization.
Source: diagonal tower system proof, step (3), target normalization
(blueprint: def-sfb-kummer-strict-adjunct-data).
This is precisely the canonical underlying-map equation, with no chosen data. -/
def kummerRootNormalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤))) (H : DiagonalSystems ℓ W)
    (roots : H ⋙ diagonalForget ℓ W ≅
      Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (n : ℕ) (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n W).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W)) : Prop :=
  HEq ((diagonalForget ℓ W).map t.hom)
    (roots.hom.app (op n) ≫ cartierProRootMap (diagonalResidue.{u} ℓ n)
      (ℓ ^ (n + 1)) (cartierResidue_cast ℓ (n + 1)) W
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1)))

/-- The concrete compatibility formula, with its coefficient expressions shared.
This is a real proposition definition and chooses no data.
(blueprint: def-sfb-kummer-strict-adjunct-data). -/
@[irreducible] def kummerStrictAdjunctCompatibilityStatement (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  KummerTargetAdjunctCompatibility
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := fun n => diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := fun n => kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := fun n => diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := fun n => diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := fun n => diagonalFiniteToPadicColimits ℓ n W)
    (Vadd := fun n => cartierForgetAdditive (diagonalResidue.{u} ℓ n) W)
    (Vlim := fun n => cartierForgetLimits (diagonalResidue.{u} ℓ n) W)
    (Vcolim := fun n => cartierForgetColimits (diagonalResidue.{u} ℓ n) W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)
```

The original module retains `public import Sheaf.Paper.CanonicalSheafExt` and adds:

```lean
public import Sheaf.Paper.KummerStrictAdjunctData
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.KummerStrictAdjunctCompatibility | F5 | Definitions move to a public data import; theorem statement unchanged. |
| Sheaf.Paper.KummerStrictTargetTransport | unclaimed in shared snapshot | Direct importer; all four names are still public, no source adaptation. |
| Sheaf.Paper.DiagonalCartierAdjunctUniqueness | unclaimed in shared snapshot | Indirect name user; the same public declaration is re-exported, no source adaptation. |
| Sheaf.Paper.DiagonalFiniteCartierNormalization | unclaimed in shared snapshot | Indirect name user; the same public declaration is re-exported, no source adaptation. |
| Sheaf.Paper.KummerSheafClassCondition | unclaimed in shared snapshot | Indirect name user; the same public declaration is re-exported, no source adaptation. |
| Sheaf.Paper.SheafKummerTransportAssembly | unclaimed in shared snapshot | Indirect name user; the same public declaration is re-exported, no source adaptation. |
| Sheaf.Paper.KummerSheafConclusion | unclaimed in shared snapshot | Indirect name user; the same public declaration is re-exported, no source adaptation. |

No existing consumer is changed. The direct importer is checked against the packet
and is not included as an unchanged source copy in the delivery. The required
delivery tool also checks the indirect users selected by these moved names.

## Status

landed 20261027T180605-L-3879427 2026-10-27 (merge of deliver/F5/Sheaf.Paper.KummerStrictAdjunctCompatibility)
