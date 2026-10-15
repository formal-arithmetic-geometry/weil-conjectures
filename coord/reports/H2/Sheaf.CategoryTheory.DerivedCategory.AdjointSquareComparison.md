## What changed

Proved `CategoryTheory.Adjunction.derived_adjoint_square_comparison` in
`Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`, with its complete signature
and public imports unchanged. The canonicality hypotheses `hcan` and `hcan0` directly identify
the derived units on localized complexes. The proof transports the underived unit equation
degreewise and uses `hb`, `haD`, and naturality to compare those units. Localization extends
the equality to all derived objects. The Hom and counit formulas then follow by the unit
formula for adjuncts and the triangle identity.

All proof steps are local `have` declarations with complete proofs. No declaration, module,
axiom, or intermediate obligation was added. Updated the existing DAG node's proof,
proof dependencies, and proof origin to describe this argument. The unit record
`sk-prop-sf-kunneth-ordinary` has no realized statement or steps here; its route is unchanged.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Adjunction.derived_adjoint_square_comparison`
(node `lem-kun-derived-adjoint-square-comparison`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
This is a proof, not a decomposition. The local compile passes without warnings.
An independent scratch copy with `#print axioms` also checks the theorem; the delivery
dry run checks compilation and axioms again.

## No longer needed

Removed the direct proof imports:

- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`

The proof does not invoke nodes `lem-weil-pbc-exact-functor-derived-functor`,
`lem-pc-pre-derived-adjoint-functors-general`, or
`lem-pc-derived-adjoint-functors`; only
`lem-weil-pbc-localization-universal-property` remains as a proof dependency.
The existing public import `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors` stays
unchanged because it supplies interfaces occurring in the statement. Its transitive imports
may still retain these modules in the global closure; this report claims removal of the
item's direct proof imports and proof edges, not global unreachability.

## Where the brief, the DAG or earlier work was wrong

The original first DAG step reconstructs the canonical derived-unit formula through general
pre-derived adjunctions and exact-functor derivedness. The actual Lean statement already
assumes the stronger, directly usable complex-level canonical Hom formulas `hcan` and
`hcan0`, so those reconstruction dependencies are unnecessary. No mathematical statement
was changed. In particular the unused essential-constancy hypotheses `hR` and `hR0` stay
in the signature; the proof retains explicit references to them to avoid unused-parameter warnings.


## Second reading by H2

1. **Visible interface: PASS.** Read the whole delivered module and its `diff -u` against
   the shared repository. The sole existing theorem is
   `CategoryTheory.Adjunction.derived_adjoint_square_comparison`; its entire signature,
   including `hR`, `hR0`, `hcan`, `hcan0`, `hb` and `haD`, is byte for byte identical
   (also checked by a Python comparison). There are no definitions or added public
   declarations. Both public imports are unchanged. No change record is needed.
2. **Proof: PASS.** The initial independent `lcompile.py` run completed without errors
   or warnings. Inspected every local `have`: `hη` and `hη0` specialize the given Hom
   formulas at identity maps; `hcC` is exactly `hc` in each degree; `haDi` cancels only
   the stipulated isomorphisms. The `hq` calculation uses naturality of `b`, the exact
   localization factors, `γ0`, and `d0.unit`, with `hb` and `haD` in their given
   directions. No invertibility of `b`, `γ`, or `γ0` is assumed. `hu` uses localization
   extensionality; `hh` follows from its unit equation and naturality of `b`. Applying
   `hh` to the counit, then the inverse second Hom equivalence, proves the final
   conjunct by the triangle identity. No `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, or hidden witness construction occurs in the file.
   The scratch-copy `#print axioms` run completed without warnings and reported
   exactly `[propext, Classical.choice, Quot.sound]` for the delivered theorem.
3. **Split statements: PASS (none).** There are no split-off statements, new modules,
   or new nodes. The original hole is closed without adding a hole. The calculation
   never cancels the comparison transformations, so it also handles noninvertible
   comparisons. When the square and vertical functors are identities it reduces to
   the original adjunction's unit and triangle equations; zero complexes introduce
   no exceptional case. There is no restatement standing in for the proof.
4. **Route and pruning: PASS.** Read Stacks Tags
   [09T5](https://stacks.math.columbia.edu/tag/09T5),
   [0DVC](https://stacks.math.columbia.edu/tag/0DVC), and
   [0FND](https://stacks.math.columbia.edu/tag/0FND) online because the literature
   checkout is absent on this machine. These supply the canonical derived Hom
   construction; the compatible-square calculation is explicitly identified as an
   agent generalization, rather than attributed verbatim to those tags. Ran a fresh
   recorded LeanFinder search for a natural transformation between localized right
   adjoints as the mate of a localized left-adjoint isomorphism. Read
   `Mathlib/CategoryTheory/Adjunction/Mates.lean` (`mateEquiv`, `unit_mateEquiv`,
   `mateEquiv_counit`), `Localization/Adjunction.lean` (the two `CatCommSq`
   hypotheses), and `Functor/Derived/Adjunction.lean` (the absolute-derived-functor
   assumptions), and searched `lean/Sheaf/CategoryTheory` and
   `lean/WeilConjectures/CategoryTheory`. None supplies this comparison directly:
   mates still require identifying `b`, ordinary localization of adjunctions requires
   invertible right comparison maps, and the general derived-adjunction constructor
   assumes extra postcomposition instances. The given `hcan` and `hcan0` already
   yield the needed unit formulas in one specialization each. The three deleted
   old proof dependencies are all listed under `No longer needed`; the two removable
   direct proof imports are deleted. `Localization.Predicate` supplies
   `Localization.natTrans_ext`. The public imports supply the derived-functor and
   essential-constancy interfaces in the signature. Read the unit record
   `sk-prop-sf-kunneth-ordinary`: its `realized.statement` and `realized.steps` are
   both empty, and neither the unit nor a realized route is changed. No claim of
   global module unreachability is made.
5. **DAG agreement: PASS.** Compared the delivered node with the repository JSON.
   Only `proof`, `proof_deps`, and `proof_origin` changed; the mathematical statement,
   source, Lean signature record, unit and chapter are unchanged. The union of the
   proof steps' `uses` is exactly the sole remaining dependency,
   `lem-weil-pbc-localization-universal-property`. Read that Mathlib leaf: its clause
   (3) is precisely `Localization.natTrans_ext`, the theorem used in `hu`. The first
   two steps now describe `hcan`/`hcan0`, `hcC`, `haDi`, and `hq`; the last three
   describe `hu`, `hh`, and the counit argument. `proof_origin` correctly marks the
   direct calculation as agent work based on the cited canonical Hom formulas.

**Changes made by this second reading.** Corrected the theorem docstring's first proof
step: it still described reconstructing the derived unit via
`preDerivedAdjunctionGeneral` and `exactFunctor_derivedFunctor`, although the actual
proof specializes the already assumed `hcan` and `hcan0`. The proof term, signatures,
imports, and node supplied by the first worker needed no repair. Added this independent
review and the explicit axiom-check evidence. Holes closed remain 1; holes added remain 0.
