# WeilConjectures.PurScalarProjection.realization_existsUnique and gamma_identification

## Reason

The proofs of realization_existsUnique and gamma_identification are added, with
no changes to their statements. The existing realization definition is unchanged.

After profiling the complete item at 84 seconds, explicit isomorphism cancellation
replaced costly Mono-instance search on large derived functor images. The resulting
file still measured 70 seconds. The finite comparison is also identified with the
ordered proper/open finiteTensorMap by comparison_factorization, avoiding unfolding
the large mate definition. The self-contained proved components are then isolated:

- WeilConjectures.PurScalarProjection.realization_existsUnique and realization move
  from Sheaf.Paper.CompactSupportScalarProjectionIdentification to
  Sheaf.Paper.CompactSupportProjectionRealization.
- WeilConjectures.PurScalarProjection.gamma_identification moves to
  Sheaf.Paper.CompactSupportScalarGammaIdentification.
- The original module publicly imports both components, preserving all existing
  public names, binders, visibility and the chosen realization map.
- Sheaf.Paper.CompactSupportProjectionRealizationLift is a new proved construction
  from the existing strict reduction comparison. It adds no theorem hole.

The new nodes carry the moved Lean attachments. The original node retains the
projection-square statement and records the component dependencies. No definition
is made irreducible globally, no instance or simp API is changed, and no adopted
source-library file is changed. Local irreducibility prevents unfolding the large
derived-functor presentations during these proofs. All new modules keep the normal
transparency options.

There are no direct Lean importers of the original item in the shared snapshot
checked with rg. Thus no existing consumer module needs an adaptation. The original
module is compiled against the component files as the re-export/consumer check.
No target statement or definition changes its mathematical meaning.


## Old

The original module declares these exact signatures and chosen definition.
The theorem proofs are sorry; the definition selects the uniquely normalized isomorphism.

```lean
theorem realization_existsUnique
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∃! ρ : (image (completed l E) c).obj M ≅
        (PurStrictScalar.scalarSupport l E c S).obj M,
      ∀ n : ℕ,
        (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
            ρ.hom ≫ PurStrictScalar.scalarSupportCounit l E c S n M =
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M

theorem gamma_identification
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ∃ hCM : finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          (realization l E D hl f c SE M hM).hom ≫
          PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM =
        (comparison (completedChange l E F i) c).app M ≫
          (realization l F D hl f c SF
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hCM).hom

def realization
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  (realization_existsUnique l E D hl f c S M hM).exists.choose
```

## New

The signatures and chosen definition stay verbatim below. Their proved bodies and
attachments move to CompactSupportProjectionRealization and
CompactSupportScalarGammaIdentification. The original item publicly imports both
components. The new lift theorem is an additional proved construction, not an
interface replacement.

```lean
theorem realization_existsUnique
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∃! ρ : (image (completed l E) c).obj M ≅
        (PurStrictScalar.scalarSupport l E c S).obj M,
      ∀ n : ℕ,
        (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
            ρ.hom ≫ PurStrictScalar.scalarSupportCounit l E c S n M =
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M

theorem gamma_identification
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SF : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (e : ℕ) (he : Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ∃ hCM : finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M),
      (pbcDerivedExtend (completedCoefficientMap l E F i Y)).map
          (realization l E D hl f c SE M hM).hom ≫
          PurScalarArrow.completedArrow l E F i D hl f c SE SF e he hepos M hM =
        (comparison (completedChange l E F i) c).app M ≫
          (realization l F D hl f c SF
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hCM).hom

def realization
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  (realization_existsUnique l E D hl f c S M hM).exists.choose
```

## Users

No existing direct Lean importer of the item was found in the current shared
snapshot. The consumers inside this delivery are:

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | B3 | Publicly re-exports the same declarations and compiles as the assembly consumer. |
| `Sheaf.Paper.CompactSupportProjectionRealization` | B3 (new) | Proves the existing unique realization, preserving its exact statement and chosen map. |
| `Sheaf.Paper.CompactSupportScalarGammaIdentification` | B3 (new) | Uses the realization normalization and proves the existing gamma equality. |
| `Sheaf.Paper.CompactSupportProjectionRealizationLift` | B3 (new) | Supplies the proved normalized morphism used by the realization proof. |

For the separate declaration-specific DAG prerequisite correction in finite mates,
see B3-compact-support-finite-mate-prerequisite.md.

No target statement or referenced definition changes meaning. There are no forced
adaptations of another group's file, and no existing external consumer changes.

## Status

landed 20261027T012808-L-2331698 2026-10-27 (merge of deliver/B3/Sheaf.Paper.CompactSupportScalarProjectionIdentification)
