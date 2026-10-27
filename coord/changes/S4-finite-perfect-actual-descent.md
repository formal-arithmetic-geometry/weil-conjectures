# AlgebraicGeometry.Scheme.finitePerfectAdic_actual_realization

## Reason

The old interface takes arbitrary `L : FinitePerfectAdicActualLevelData X d M V T`.
The parameter M is phantom in that structure: its fields state boundedness, lisse
cohomology, stalkwise agreement with T, and universal consecutive arrows. None
asserts that L is a descent of M. Thus the theorem is false.

For example, let X = Spec(R), V = X, A = F3, I = 0. Take the rank-one constant
algebraic tower and take M to be the sign local system for Gal(C/R), concentrated
in degree zero. The separate markings hold after Spec(C) -> X. Let L be the
constant etale tower. It satisfies the level-data fields. Its inputs to
`realization` in `actual` and `model` are then identical, so these two isomorphisms
would identify the nontrivial sign local system with the trivial local system on X.
No requirement on the arbitrary functor can avoid that contradiction.

Stacks 09C6 instead chooses L_n with K_n = epsilon inverse L_n, retains these
isomorphisms, and descends the actual consecutive arrows. The repaired theorem
chooses L and its realization together. It changes no target, unit statement,
existing data structure, or conclusion of the parent normalization theorem.

## Old

```lean
theorem finitePerfectAdic_actual_realization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (L : FinitePerfectAdicActualLevelData X d M V T)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    Nonempty (FinitePerfectAdicActualRealizationData X d M V T L)
```

## New

```lean
theorem finitePerfectAdic_actual_realization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    ∃ L : FinitePerfectAdicActualLevelData X d M V T,
      Nonempty (FinitePerfectAdicActualRealizationData X d M V T L)
```

## Users

The source scan and `tools/downstream.py --uses finitePerfectAdic_actual_realization`
find exactly the item and its sole caller below. Other transitive importers do not
mention the changed theorem; the parent retains its public signature and structures.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicActualRealization | S4 | Correct universal quantification over arbitrary L to existence of L with retained actual descent. |
| Sheaf.Paper.FinitePerfectAdicActualNormalization | unclaimed at inspection | Replace two incompatible existence choices by one joint choice; theorem signature and every structure field stay verbatim. |

The only DAG citer is
`lem-weil-pbc-finite-perfect-adic-actual-normalization`: it still needs exactly
existence of L and its realization. Its proof dependency is updated accordingly.
The item node gains a statement_change with this complete citer audit. Its inherited
blueprint.from names a non-blueprint split node; this metadata problem is reported
for maintenance, without changing that stage-3-restricted field.

The source-library tree lean/WeilConjectures is untouched. New definitions construct
functors termwise. The compositor comes from a proved unique isomorphism whose
components are explicitly extended from the sheafification unit. No object is
selected from an unproved mere existence assertion.

## Status

landed 20261027T210227-L-1674906 2026-10-27 (merge of deliver/S4/Sheaf.Paper.FinitePerfectAdicActualRealization)
