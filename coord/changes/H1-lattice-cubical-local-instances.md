# Profinite.DiscreteLattice.CubicalEvaluation local instance conversion

## Reason

Returned-delivery repair (head `178863bcf98`, reviewer C-17886): the review passed,
but landing rejected the basename used for a reviewer fix. This repository file
is delivered at `coord/changes/H1-lattice-cubical-local-instances.md`. The separate
flat `--apply-fixes` filename required by `tools/batch_land.py:fixes` is
`H1-lattice-cubical-local-instances.change.md`. Use that key only for a reviewer
override; keep this repository path unchanged. The complete record is included
in the rebased repair packet. Its status remains open until actual landing.

The original module exceeded the 60-second single-file limit. Profiling isolated
kernel conversion in the existing tensor augmentation, cubical model, invariant
inclusion and evaluation model; the new zero-map proof itself was inexpensive.
Within sections, use the canonical imported instances directly instead of the
three aliases declared by this module. All aliases and their public instance
attributes remain available to importers after the section closes.

Re-enable respectTransparency, make the two linear-endomorphism function
applications explicit, make the three complex-functor abbreviations ordinary definitions with the same
bodies, and apply the existing irreducible attribute of unitComparison earlier.
This avoids eager expansion while elaborating subsequent statements.
The explicit toFun projections are precisely the functions previously inserted by
coercion. No mathematical hypothesis, conclusion, object or action is changed.
No target changes meaning. No definition uses data selected from a new theorem.

## Old

The two existing structures, verbatim:

```lean
structure DiscreteComparison where
  equivalence : CondensedBar.Equivariant A (D r) ≌ DiscreteLattice.Equivariant A.toMon r
  underlying : equivalence.functor ⋙ Action.forget _ _ ≅ CondensedBar.forgetAction
  additive : equivalence.functor.Additive
  action : ∀ (M : CondensedBar.Equivariant A (D r)) (S : Profinite.{u})
      (v : Fin r → ℤ) (x : sections A (equivalence.functor.obj M).V S),
    (underlying.hom.app M).hom.hom.app (op S)
        (((equivalence.functor.obj M).ρ (Multiplicative.ofAdd v)).hom.hom.app (op S) x) =
      M.act S (ContinuousMap.const S (vector v))
        ((underlying.hom.app M).hom.hom.app (op S) x)

structure CubicalModel where
  L : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ
  ι : ∀ n : ℤ, Cells r (-n) → (𝟙_ (CondensedBar.Modules A) ⟶ (L.X n).module)
  coproduct : ∀ n : ℤ, IsColimit (Cofan.mk (L.X n).module (ι n))
  boundary : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ (L.d n (n + 1)).val =
      ∑ i ∈ I, ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card) •
        (cell A r L ι (n + 1) (v + IntegralLatticeCubical.unitVector r i) (I.erase i) -
          cell A r L ι (n + 1) v (I.erase i))
  translation : ∀ (n : ℤ) (v w : Fin r → ℤ) (I : Finset (Fin r))
      (S : Profinite.{u}) (x : sections A (𝟙_ (CondensedBar.Modules A)) S),
    (L.X n).act S (ContinuousMap.const S (vector w))
        ((cell A r L ι n v I).hom.hom.app (op S) x) =
      (cell A r L ι n (v + w) I).hom.hom.app (op S) x
  ε : L ⟶ HomologicalComplex.tensorUnit _ (.up ℤ)
  augmentation : ∀ v : Fin r → ℤ,
    cell A r L ι 0 v ∅ ≫ (ε.f 0).val ≫ (unitComparison A r).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom = 𝟙 _
  s : HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) ⟶
    (forgetComplex A r).obj L
  sectionOrigin : s.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom ≫
      cell A r L ι 0 0 ∅
  retraction : s ≫ (forgetComplex A r).map ε ≫ (unitComparison A r).hom = 𝟙 _
  contraction : Homotopy (𝟙 ((forgetComplex A r).obj L))
    ((forgetComplex A r).map ε ≫ (unitComparison A r).hom ≫ s)
  integral : ∀ a : ℤ,
    IntegralLatticeCubical.Chains r a →ₗ[ℤ] IntegralLatticeCubical.Chains r (a + 1)
  integralIdentity : ∀ (a : ℤ) (_ : 0 ≤ a) (x : IntegralLatticeCubical.Chains r a),
    IntegralLatticeCubical.incomingBoundary r a (integral a x) +
      LinearEquiv.cast (R := ℤ) (M := IntegralLatticeCubical.Chains r)
        (sub_add_cancel a 1)
          (integral (a - 1) (IntegralLatticeCubical.boundary r a x)) =
      x - IntegralLatticeCubical.originProjection r a x
  integralCoefficients : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ contraction.hom n (n - 1) =
      (integral (-n) (IntegralLatticeCubical.cell r (-n) v I)).sum
        (fun c m ↦ m • cell A r L ι (n - 1) c.1 c.2.val)
```

The original complex functors and unit comparison were:

```lean
abbrev forgetComplex :
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ ⥤
      CochainComplex (CondensedBar.Modules A) ℤ :=
  (CondensedBar.forgetAction (A := A) (G := D r)).mapHomologicalComplex (.up ℤ)

/-- The degreewise trivial-action functor on actual complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
abbrev trivialComplex : CochainComplex (CondensedBar.Modules A) ℤ ⥤
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ :=
  (CondensedAction.trivial (R := A.toMon) (P := D r)).mapHomologicalComplex (.up ℤ)

/-- The canonical underlying comparison for the equivariant tensor unit complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def unitComparison :
    (forgetComplex A r).obj (HomologicalComplex.tensorUnit
      (CondensedBar.Equivariant A (D r)) (.up ℤ)) ≅
        HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (CondensedBar.forgetAction (A := A) (G := D r)) (.up ℤ) 0).app (𝟙_ _)) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (actionTensor A (D r)).forgetCore.εIso.symm
```

```lean
abbrev invariantComplex :=
  (CondensedDerivedRestriction.invariants A (D r)).functor.mapHomologicalComplex (.up ℤ)
```

The original options were:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

The same structures with explicit function projections, verbatim:

```lean
structure DiscreteComparison where
  equivalence : CondensedBar.Equivariant A (D r) ≌ DiscreteLattice.Equivariant A.toMon r
  underlying : equivalence.functor ⋙ Action.forget _ _ ≅ CondensedBar.forgetAction
  additive : equivalence.functor.Additive
  action : ∀ (M : CondensedBar.Equivariant A (D r)) (S : Profinite.{u})
      (v : Fin r → ℤ) (x : sections A (equivalence.functor.obj M).V S),
    (underlying.hom.app M).hom.hom.app (op S)
        (((equivalence.functor.obj M).ρ (Multiplicative.ofAdd v)).hom.hom.app (op S) x) =
      (M.act S (ContinuousMap.const S (vector v))).toFun
        ((underlying.hom.app M).hom.hom.app (op S) x)

structure CubicalModel where
  L : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ
  ι : ∀ n : ℤ, Cells r (-n) → (𝟙_ (CondensedBar.Modules A) ⟶ (L.X n).module)
  coproduct : ∀ n : ℤ, IsColimit (Cofan.mk (L.X n).module (ι n))
  boundary : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ (L.d n (n + 1)).val =
      ∑ i ∈ I, ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card) •
        (cell A r L ι (n + 1) (v + IntegralLatticeCubical.unitVector r i) (I.erase i) -
          cell A r L ι (n + 1) v (I.erase i))
  translation : ∀ (n : ℤ) (v w : Fin r → ℤ) (I : Finset (Fin r))
      (S : Profinite.{u}) (x : sections A (𝟙_ (CondensedBar.Modules A)) S),
    ((L.X n).act S (ContinuousMap.const S (vector w))).toFun
        ((cell A r L ι n v I).hom.hom.app (op S) x) =
      (cell A r L ι n (v + w) I).hom.hom.app (op S) x
  ε : L ⟶ HomologicalComplex.tensorUnit _ (.up ℤ)
  augmentation : ∀ v : Fin r → ℤ,
    cell A r L ι 0 v ∅ ≫ (ε.f 0).val ≫ (unitComparison A r).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom = 𝟙 _
  s : HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) ⟶
    (forgetComplex A r).obj L
  sectionOrigin : s.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom ≫
      cell A r L ι 0 0 ∅
  retraction : s ≫ (forgetComplex A r).map ε ≫ (unitComparison A r).hom = 𝟙 _
  contraction : Homotopy (𝟙 ((forgetComplex A r).obj L))
    ((forgetComplex A r).map ε ≫ (unitComparison A r).hom ≫ s)
  integral : ∀ a : ℤ,
    IntegralLatticeCubical.Chains r a →ₗ[ℤ] IntegralLatticeCubical.Chains r (a + 1)
  integralIdentity : ∀ (a : ℤ) (_ : 0 ≤ a) (x : IntegralLatticeCubical.Chains r a),
    IntegralLatticeCubical.incomingBoundary r a (integral a x) +
      LinearEquiv.cast (R := ℤ) (M := IntegralLatticeCubical.Chains r)
        (sub_add_cancel a 1)
          (integral (a - 1) (IntegralLatticeCubical.boundary r a x)) =
      x - IntegralLatticeCubical.originProjection r a x
  integralCoefficients : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ contraction.hom n (n - 1) =
      (integral (-n) (IntegralLatticeCubical.cell r (-n) v I)).sum
        (fun c m ↦ m • cell A r L ι (n - 1) c.1 c.2.val)
```

The revised complex functors and unit comparison are:

```lean
def forgetComplex :
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ ⥤
      CochainComplex (CondensedBar.Modules A) ℤ :=
  (CondensedBar.forgetAction (A := A) (G := D r)).mapHomologicalComplex (.up ℤ)

/-- The degreewise trivial-action functor on actual complexes.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def trivialComplex : CochainComplex (CondensedBar.Modules A) ℤ ⥤
    CochainComplex (CondensedBar.Equivariant A (D r)) ℤ :=
  (CondensedAction.trivial (R := A.toMon) (P := D r)).mapHomologicalComplex (.up ℤ)

/-- The canonical underlying comparison for the equivariant tensor unit complex.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def unitComparison :
    (forgetComplex A r).obj (HomologicalComplex.tensorUnit
      (CondensedBar.Equivariant A (D r)) (.up ℤ)) ≅
        HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (CondensedBar.forgetAction (A := A) (G := D r)) (.up ℤ) 0).app (𝟙_ _)) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (actionTensor A (D r)).forgetCore.εIso.symm

attribute [irreducible] unitComparison
```

```lean
def invariantComplex :=
  (CondensedDerivedRestriction.invariants A (D r)).functor.mapHomologicalComplex (.up ℤ)
```

The two options are true. An enclosing section removes only the local instance
registrations of sheafMonoidal, latticeTopologicalGroup and moduleMonoidal;
the section restores them. The three complex functors remain reducible by ordinary unification and by
explicit unfolding. The existing public irreducible attributes on total,
bicomplex and unitComparison are retained; only the point at which the latter
is applied inside this file moves earlier.
All explicit definition bodies remain unchanged.

After these improvements, the combined file passed once at 59.3 seconds but took
81 seconds when recompiled in the required consumer check. Therefore the existing
core declarations are extracted into LatticeCubicalEvaluationCore, the existing
CubicalModel and coordinate maps into LatticeCubicalEvaluationModel, and the item
retains Evaluation, RankZero and the main theorem. Each module uses the same
public namespace. The model publicly imports the core, and the item publicly
imports the model; all original public imports are retained. No declarations are
removed or duplicated, and the sole original hole remaining is the main theorem.

The existing total/bicomplex irreducible attributes now live at the end of their
owning core module. During construction of the coordinate maps, the model uses
local semireducible attributes, restored when its section ends. This retains the
original public irreducibility while allowing the same internal construction.

Two new nodes record the moved zero-map theorem and cubical-model definition.
The original node's Lean declaration list is restricted to its three physically
remaining declarations; the new node records preserve all moved attachments.
Its statement dependencies gain these two nodes. The mathematical statement,
proof, proof dependencies, source and unit route are unchanged.

## Users

The downstream.py scan for the module and CubicalModel lists only the following
direct importer. It uses the same declarations and definitionally identical fields.
No consumer adaptation is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.LatticeCubicalEvaluationCore | new | Existing core declarations and proved koszulZero, preserving names. |
| Sheaf.CategoryTheory.LatticeCubicalEvaluationModel | new | Existing cubical data and coordinate maps, preserving names. |
| Sheaf.CategoryTheory.LatticeCubicalAugmentationEvaluation | H1 | Public reexport of extracted data; same Evaluation, RankZero and main theorem signatures. |
| Sheaf.CategoryTheory.LatticeCubicalMultiplicationRoof | H2 | Same public declarations and attributes; unchanged consumer compiled in 46.4 seconds (reviewer: compiled against the delivered modules). |

Validation: core 32.6 s; model 29.6 s; item 29.8 s; unchanged direct importer
46.4 s. All four files compiled successfully against this delivery. The temporary
unchanged importer copy was removed before submission.

Repair dry run: rebased commit `93151f438d1` compiled and passed server
preflight; no push. The subsequent delivery is regenerated on current sheaf-dag.

## Status

landed 20261026T091658-L-3363427 2026-10-26 (merge of deliver/H1/Sheaf.CategoryTheory.LatticeCubicalAugmentationEvaluation)
