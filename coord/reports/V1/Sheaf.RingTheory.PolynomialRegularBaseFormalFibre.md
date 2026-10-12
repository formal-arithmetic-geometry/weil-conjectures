## What changed

Filled `Polynomial.regularBase_formalFibre_isRegular` using regularity of the
localization and completion, the zero-prime localization case, and the explicit
nonzero-fibre hypersurface presentation. Added the helper module
`Sheaf.RingTheory.PolynomialNonzeroFibreHypersurface`.

## Proved and sorry left

Hole closed: `Polynomial.regularBase_formalFibre_isRegular`
(node `lem-weil-pbc-polynomial-regular-base-formal-fibre`). Its proof now combines
regular completion, regular localization, the zero-prime fibre equivalence,
derivation extension, and hypersurface regularity.

Hole added: `Polynomial.nonzero_fibre_hypersurface_presentation`
(node `lem-weil-pbc-polynomial-nonzero-fibre-hypersurface`). This supplies only
an algebraic quotient presentation and a unit derivative, with no regularity
assertion or completion assumptions. This is a decomposition: one hole closed,
one hole added, net zero immediate holes. The item has no direct sorry remaining,
but depends on this helper and still-open imported results; it is not axiom-free.

## No longer needed

No stated proof dependency was removed. All imported regularity and derivation
modules are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG did not include a node for the nonzero-prime hypersurface
presentation required by the proof; this delivery adds that strictly smaller node.

## Earlier second reading (a previous round; superseded)

The target proof was compiled together with the helper module. The target statement
is unchanged, and the new helper is strictly smaller: it supplies only the explicit
nonzero-prime hypersurface presentation and derivative-unit fact used in the target.

## New nodes

`lem-weil-pbc-polynomial-nonzero-fibre-hypersurface` is added for the helper
presentation theorem.

## Second reading by V1

1. Compared the delivered item module with its repository version using `diff`.
   The existing theorem signature is byte-for-byte unchanged, as are its docstring
   and public imports. The added helpers are private and have real bodies.
   The only other Lean module is new; no existing definition was changed. PASS.
2. Both modules compiled locally through `lcompile.py --all`, without errors or
   warnings. Scratch-copy `#print axioms` checks of both public declarations show
   only `propext`, `Classical.choice`, `Quot.sound`, and expected `sorryAx`.
   The single delivered sorry is the named presentation theorem; no forbidden
   declarations or hollow definitions occur. PASS as a decomposition.
3. Checked the presentation proof from fraction-field localization, the PID
   generator, the field quotient, and characteristic-zero separability. Checked
   A a field with r = (X), a denominator-cleared generator over a nonfield domain,
   and the zero S-algebra. All are consistent: in the last case the quotient is
   the zero ring and zero is a unit. The assertion is strictly smaller than the
   item: it contains no regularity or completion claim. Independent leanfinder,
   loogle, and grep searches found ingredients but no complete theorem; searched
   lean/ and the upstream ring-theory files too. Mathlib's
   `Ideal.exists_mem_span_singleton_map_residueField_eq` supplies the generator
   ingredient and `Irreducible.separable` the separability ingredient, but closing
   the localization/fibre equivalence is not a few-minute proof. PASS.
4. Read the proof top down: the zero case uses Mathlib's explicit fibre quotient
   equivalence, and the nonzero case uses the existing planned regularity and
   derivation lemmas. Every old proof dependency is used and no module is pruned.
   Added imports are proof-only. All public imports support signature types.
   Read `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed or
   changed by this lower-level algebraic decomposition. PASS.
5. Repaired the item's DAG proof and proof_deps to include the presentation node.
   Checked the helper's source, docstring, Lean record, chapter, unit, creation
   record and blueprint ancestry. Corrected its prose statement to match Lean:
   the existential polynomial is not required to be in r by the signature.
   Replaced unsupported search summaries with actual independently recorded
   queries and results, retaining the recorded unavailable LeanSearch attempt; recorded that the general helper is an agent adaptation
   of the source argument rather than a verbatim sourced statement. PASS.

Second reading changed the two DAG records and this report. The Lean proofs and
signatures needed no repair. No change record is needed: existing interfaces are
unchanged. Source review used Stacks Tags [07PU](https://stacks.math.columbia.edu/tag/07PU)
and [07PV](https://stacks.math.columbia.edu/tag/07PV); the quotient presentation is
adapted from 07PU and the regular completion step follows 07PV.
