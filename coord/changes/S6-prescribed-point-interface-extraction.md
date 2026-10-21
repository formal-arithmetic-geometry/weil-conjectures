# AlgebraicGeometry prescribed-point system interfaces

## Reason

Move the seven existing concrete constructions to PrescribedPointSystemData so that
independent interpolation and fixed-system Bertini lemmas can state their conclusions
without importing their own consumer. This breaks the prospective import cycle.
The original module publicly imports the interface module. Qualified names, universes,
binders, visibility, data and theorem signature are unchanged. Only docstring node
references change. No source-library declaration is edited.

## Old

In lean/Sheaf/AlgebraicGeometry/BertiniPrescribedPointSmoothSystem.lean:

```lean
abbrev prescribedPointTwist {k : Type u} [Field k] {N : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (n : ℕ) : Y.Modules :=
  (tensorPullback c).obj (ProjectiveSpace.twist _ _ (n : ℤ))

/-- The section with the given coefficients in a finite family, with scalars supplied by
its specified structure morphism. Source: blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointCombination {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (a : I → k) : Γ(M, ⊤) :=
  ∑ i, f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a i)) • s i

/-- Vanishing on a reduced finite set, tested in the residue-field fibres.
Source: blueprint, finite-cover-curve proof, paragraph 2, definition of `V_n`.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointVanishes {X : Scheme.{u}} (M : X.Modules) (S : Finset X)
    (v : Γ(M, ⊤)) : Prop :=
  ∀ x ∈ S, M.presheaf.germ ⊤ x trivial v ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))

/-- A concrete canonical model of the first-order target at a prescribed point.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
abbrev PrescribedPointJet {X : Scheme.{u}} (M : X.Modules) (x : X) : Type u :=
  TensorProduct (X.presheaf.stalk x) (IsLocalRing.CotangentSpace (X.presheaf.stalk x))
    (M.presheaf.stalk x)

/-- First-order value of a section vanishing at `x`. In a stalk frame `e`, write its germ
as `a * e⁻¹(1)` and take `[a] ⊗ e⁻¹(1)`. Changing the frame cancels between the two
factors. The value off the vanishing subspace is set to zero and is never used below.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointJet {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (x : X) (v : Γ(M, ⊤)) : PrescribedPointJet M x := by
  classical
  let e := Classical.choice (invertible_stalk_linearEquiv X M x)
  let a := e (M.presheaf.germ ⊤ x trivial v)
  exact if h : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) then
    TensorProduct.tmul (X.presheaf.stalk x)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨a, h⟩) (e.symm 1)
    else 0

/-- Restrict a family of sections to an open, using the canonical tensor-pullback unit,
and convert it to the compatible-section encoding used by the projective morphism.
Source: Stacks Project, Tag 0FD5, restriction of the kernel linear system.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointRestrictedFamily {Y : Scheme.{u}} (M : Y.Modules)
    {X : Scheme.{u}} (j : X ⟶ Y) (U : X.Opens) {I : Type u}
    (s : I → Γ(M, ⊤)) : I → ((tensorPullback (U.ι ≫ j)).obj M).sections :=
  bertiniSectionFamily _ (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i))

/-- The actual zero scheme of the restricted section with coefficient tuple `a`.
Source: blueprint, finite-cover-curve proof, paragraph 2, `H_v = Z(v|_X)`.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointMember {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (M : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤)) (a : I → k) : X.IdealSheafData :=
  (homOfGlobalSection ((tensorPullback j).obj M)
    (tensorSectionsUnit j M (prescribedPointCombination f M s a))).zeroLocus
```

## New

In lean/Sheaf/AlgebraicGeometry/PrescribedPointSystemData.lean, publicly imported by
the original module:

```lean
abbrev prescribedPointTwist {k : Type u} [Field k] {N : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (n : ℕ) : Y.Modules :=
  (tensorPullback c).obj (ProjectiveSpace.twist _ _ (n : ℤ))

/-- The section with the given coefficients in a finite family, with scalars supplied by
its specified structure morphism. Source: blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: def-zl-prescribed-point-system-data). -/
def prescribedPointCombination {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (a : I → k) : Γ(M, ⊤) :=
  ∑ i, f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a i)) • s i

/-- Vanishing on a reduced finite set, tested in the residue-field fibres.
Source: blueprint, finite-cover-curve proof, paragraph 2, definition of `V_n`.
(blueprint: def-zl-prescribed-point-system-data). -/
def prescribedPointVanishes {X : Scheme.{u}} (M : X.Modules) (S : Finset X)
    (v : Γ(M, ⊤)) : Prop :=
  ∀ x ∈ S, M.presheaf.germ ⊤ x trivial v ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))

/-- A concrete canonical model of the first-order target at a prescribed point.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: def-zl-prescribed-point-system-data). -/
abbrev PrescribedPointJet {X : Scheme.{u}} (M : X.Modules) (x : X) : Type u :=
  TensorProduct (X.presheaf.stalk x) (IsLocalRing.CotangentSpace (X.presheaf.stalk x))
    (M.presheaf.stalk x)

/-- First-order value of a section vanishing at `x`. In a stalk frame `e`, write its germ
as `a * e⁻¹(1)` and take `[a] ⊗ e⁻¹(1)`. Changing the frame cancels between the two
factors. The value off the vanishing subspace is set to zero and is never used below.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: def-zl-prescribed-point-system-data). -/
def prescribedPointJet {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (x : X) (v : Γ(M, ⊤)) : PrescribedPointJet M x := by
  classical
  let e := Classical.choice (invertible_stalk_linearEquiv X M x)
  let a := e (M.presheaf.germ ⊤ x trivial v)
  exact if h : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) then
    TensorProduct.tmul (X.presheaf.stalk x)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨a, h⟩) (e.symm 1)
    else 0

/-- Restrict a family of sections to an open, using the canonical tensor-pullback unit,
and convert it to the compatible-section encoding used by the projective morphism.
Source: Stacks Project, Tag 0FD5, restriction of the kernel linear system.
(blueprint: def-zl-prescribed-point-system-data). -/
def prescribedPointRestrictedFamily {Y : Scheme.{u}} (M : Y.Modules)
    {X : Scheme.{u}} (j : X ⟶ Y) (U : X.Opens) {I : Type u}
    (s : I → Γ(M, ⊤)) : I → ((tensorPullback (U.ι ≫ j)).obj M).sections :=
  bertiniSectionFamily _ (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i))

/-- The actual zero scheme of the restricted section with coefficient tuple `a`.
Source: blueprint, finite-cover-curve proof, paragraph 2, `H_v = Z(v|_X)`.
(blueprint: def-zl-prescribed-point-system-data). -/
def prescribedPointMember {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (M : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤)) (a : I → k) : X.IdealSheafData :=
  (homOfGlobalSection ((tensorPullback j).obj M)
    (tensorSectionsUnit j M (prescribedPointCombination f M s a))).zeroLocus
```

## Users

The read-only downstream.py query reports zero existing Lean importers and zero uses.
A complete Lean/quarantine search likewise found no direct consumers. The unfinished
DAG parent lem-zl-bertini-finite-cover-curve is preserved, as is the unit route.
The seven definition bodies and all signatures compare identically after removing
comments and whitespace. Existing public imports remain publicly available transitively.
No target statement uses a changed construction: the constructions themselves do not change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem | S6 | Publicly reexports identical definitions; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.PrescribedPointSystemData | S6, new | Defines the identical existing interface. |
| Sheaf.AlgebraicGeometry.PrescribedPointEventualJetSystem | S6, new | Statements use the interface. |
| Sheaf.AlgebraicGeometry.PrescribedPointBertiniOpen | S6, new | Statements use the interface. |
| Sheaf.AlgebraicGeometry.PrescribedPointSmoothMember | S6, new | Statements and proofs use the interface. |

## Status

landed 20261021T151200-L-1170451 2026-10-21 (merge of deliver/S6/Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem)
