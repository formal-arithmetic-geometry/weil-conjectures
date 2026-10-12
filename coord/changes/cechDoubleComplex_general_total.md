# CategoryTheory.Sheaf.cechDoubleComplex_general_total

## Reason

Review X-e14bd, head e14bd9fd9, E1 / point 4 requests withdrawal of a false
assertion. On the site of finite C4-sets with the jointly-surjective topology, take
the terminal object X, singleton cover C4/C2 → X and trivial coefficient A = Z/2. The column-only bicomplex
has zero vertical differential; its total degree-one cohomology is
H¹(C2,A) ⊕ H⁰(C2,H¹(C2,A)) = A ⊕ A, whereas H¹(C4,A) = A.
Here the Cech nerve of C4/C2 computes the quotient group C4/C2 = C2;
the cohomology presheaf on its terms is H^q(C2,A), with trivial quotient action.
Thus the two summands are H^1(C4/C2,A) and H^0(C4/C2,H^1(C2,A)).
The zero vertical differential splits total degree-one cohomology into these
summands. Their cardinalities (four versus two) rule out an isomorphism.
Column comparisons therefore do not imply the asserted total comparison.

## Old

```lean
theorem Sheaf.cechDoubleComplex_general_total
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (X : C) {ι : Type w} {U : ι → C}
    (π : ∀ i, U i ⟶ X) (hπ : Sieve.ofArrows U π ∈ J X)
    (D : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (hcol : ∀ q : ℕ, Nonempty (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ)
      q).mapHomologicalComplex (ComplexShape.up ℕ)).obj D ≅
      (cechComplexFunctor fun i ↦ Over.mk (π i)).obj
        ((Over.forget X).op ⋙ F.cohomologyPresheaf q))) :
    ∀ n : ℕ, Nonempty ((D.total (ComplexShape.up ℕ)).homology n ≅ F.H' n X)
```

Its proof was `by sorry`.

## New

The declaration and its obsolete docstring are removed, with no replacement
assertion. The dispute explanation and counterexample remain in the module.
The historical node `stage3-cech-general-total` has `lean: null`, no proof
steps or proof dependencies, and records the withdrawal in `proof_origin`.
Its historical mathematical statement is retained as disputed, not as a lemma.

The existing `CategoryTheory.Sheaf.exists_cechDoubleComplex_general` has its
entire signature and visibility preserved. Its two-line proof is replaced
with `by sorry`, restoring obligation `stage3-cech-general-double-complex`.
The now-empty `CechGeneralTotal` import is also removed from this adapted
module because no declaration from it remains available or needed.
The latter node no longer cites the withdrawn assertion or the column-only
construction. Its open plan requires one resolution bicomplex satisfying
both comparisons. No target statement or definition changes.

## Users

The declaration-use search (`tools/downstream.py` with `--uses`) lists only
its own declaration module and the caller below. Other transitive importers
have no direct use of the removed name and keep their signatures and proofs.
CechGeneralTotal removes its public import of CechGeneralColumns and its plain import of CechResolutionTotal. The column declaration consequently becomes unavailable to its sole direct importer, CechGeneral. The delivered adaptation removes that caller’s column-only proof and unused CechGeneralTotal import while preserving its signature and visibility.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneralTotal | U2 | Remove false declaration and obsolete docstring; retain dispute explanation. |
| Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneral | unclaimed | Forced: restore existing theorem proof to `by sorry`; signature unchanged. |

The original caller against the delivered dependencies fails at line 51:22 with Unknown constant CategoryTheory.Sheaf.exists_cechDoubleComplex_general_columns, followed by an rcases failure at 51:9. Adding a plain CechGeneralColumns import in a scratch copy exposes the further Unknown constant CategoryTheory.Sheaf.cechDoubleComplex_general_total at the exact call.
Only lines 50–52 of the original caller change: the final `:= by` and its
`obtain`/`exact` proof become `:= by sorry`. The proof docstring is updated to record the joint construction and its
unresolved resolution-existence issue; the dispute text is preserved. The
obsolete import line is also removed because the adapted proof has no dependency on the empty module. These
changes are necessary because the removed name was the total-comparison step.
No unrelated proof is adapted.

## Status

landed 20261012T194146-L-466702 2026-10-12 (merge of deliver/U2/Sheaf.CategoryTheory.Sites.SheafCohomology.CechGeneralTotal)
