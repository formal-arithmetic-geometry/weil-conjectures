## What changed

The item's existing statement and docstring are unchanged. Its proof now applies the
already-proved `DerivedCategory.prop_of_bounded` to the essential image of integral
bounded constructible scalar extension. `ObjectProperty.isoClosure` supplies the
isomorphism-invariant cohomology property needed by that theorem. This writes the actual
bounded truncation reduction rather than passing the whole problem to an equivalence.

Added two proof dependencies, each in its own new module:
`Sheaf.Paper.ContinuousConstructibleIntegralSingle` states the degree-zero lattice case;
`Sheaf.Paper.ContinuousConstructibleIntegralImage` states triangulated closure of the image.
Their imports are public only for the coefficient definitions appearing in their statements.
All three additional imports of the item are proof-only imports. No existing definition,
visibility, target signature, or module belonging to another group was changed.

Removed the unpublished `ContinuousConstructibleIntegralEquivalence` module and node from
the first worker's sandbox: its claimed equivalence before rationalizing the source is false.
It was never a library declaration, so its removal needs no interface change record.

## Proved and sorry left

Hole closed in the item, by a proof from two strictly partial obligations:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_model`.

Holes added and left, each with proof in words and a matching new node:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_single_model`
  (`lem-weil-pbc-continuous-constructible-integral-single`): the degree-zero case only.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_image_triangulated`
  (`lem-weil-pbc-continuous-constructible-integral-image`): closure under zero, shifts and
  triangles only, with no assertion that every bounded E complex is in the image.

This is a decomposition, not a completed proof of the integral-model theorem. Relative to
this item's original hole, one hole is closed and two holes are added (net -1). Neither new
obligation is reported as solved. The imported coefficient definitions are unchanged.
No new data is chosen from an unproved mere-existence theorem and no definition contains
`sorry`. The item contains no `sorry`; each new theorem has precisely `:= by sorry`.

All three files compile cleanly in import order through `lcompile.py`. Scratch
`#print axioms` checks for all three declarations show only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. The reused `DerivedCategory.prop_of_bounded` has only the three
permitted axioms. The remaining work requires the integral lattice and derived-Hom
localization arguments, whose existing DAG nodes do not provide a locally compiled
applicable theorem; the lattice node's recorded signature also has additional geometric
hypotheses, so it cannot directly discharge the new degree-zero obligation.

## No longer needed

No original library import or module is pruned. The original direct proof dependencies
`lem-weil-pbc-lisse-e-constructible-integral-lattice`,
`lem-weil-pbc-condensed-e-realization`, and
`def-weil-pbc-continuous-integral-coefficients` are replaced in this node's `proof_deps`
by the two new obligations. The lattice argument remains below the single-model node;
the needed continuous-coefficient realization and localization calculations remain below
both new obligations. The broad `lem-weil-pbc-condensed-e-realization` theorem, which also
includes functor and exchange comparisons, is not itself used by this reduction; its full
statement is unnecessary here. Coefficient definitions remain a statement dependency.

The unpublished equivalence node and its import were removed rather than queued for
pruning. No unit-level statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's `continuousConstructible_integral_equivalence` claimed that the actual
functor from integral complexes to E complexes is an equivalence. This is false before
localizing the source category. For E = Q_ℓ and a nonempty geometric point, the constant
integral rank-one object has an endomorphism of its rationalization given by multiplication
by 1/ℓ which is not an integral endomorphism; also an integral ℓ-torsion sheaf rationalizes
to zero. Proposition 6.8.14(2) of Bhatt--Scholze instead gives an equivalence from
`D_cons(O_E)[1/ℓ]`. The old docstring incorrectly inferred full faithfulness of the
unlocalized functor from a Hom localization calculation. Clean compilation of a theorem
containing `sorry` cannot validate that inference.

The original target's mathematical statement is retained. Its plan is now separated into
its genuine degree-zero lattice case and the cone/shift closure step. Searches of Mathlib
and both Lean roots found no existing applicable integral-model theorem. Mathlib's
triangulated essential-image instance requires a full functor, so it cannot close the
image obligation; the correct substitute is denominator clearing. The upstream library's
`DerivedCategory.prop_of_bounded` does provide the complete final bounded induction and
is used directly, without restating it as a new lemma.

## New nodes

`lem-weil-pbc-continuous-constructible-integral-single`, in
`lean/Sheaf/Paper/ContinuousConstructibleIntegralSingle.lean`, records only the construction
for a constructible sheaf placed in degree zero. Its proof follows Lemmas 6.8.12--6.8.13
and the sheaf case of Proposition 6.8.14(2), using a finite open--closed filtration.

`lem-weil-pbc-continuous-constructible-integral-image`, in
`lean/Sheaf/Paper/ContinuousConstructibleIntegralImage.lean`, records only the triangulated
closure of the image, by integral Serre closure and localization of Hom. Both nodes carry
self-contained statements, proof steps, sources, three recorded kinds of Mathlib search,
matching Lean statements, and the item's chapter and unit. LeanSearch was attempted but
returned an internal server error; its unavailability is recorded without a verdict. There are no change records
because no existing statement or definition changes.

## Second reading by A2

1. Compared the original and final item with `diff`: the sole existing declaration's
   signature and docstring are byte-for-byte unchanged. Changes are proof-only imports
   and its proof. The two other modules are new. No external module or definition changed.
   Verdict: pass.
2. Compiled every delivered file through `lcompile.py --all`, then checked every delivered
   declaration with `#print axioms` in a scratch module. No forbidden declaration form or
   data hole occurs. Only the two explicitly listed named theorem holes remain. The
   resulting target still depends on `sorryAx`, as reported. Verdict: valid decomposition.
3. Read the two remaining obligations, their nodes and proof descriptions against
   Bhatt--Scholze, particularly Lemmas 6.8.12--6.8.13 and Proposition 6.8.14(2). Tested the
   zero module, empty scheme and torsion behavior: existence and closure handle zero;
   image closure asserts no faithfulness and so allows torsion to vanish. Neither new
   statement is the original arbitrary-bounded-complex assertion. Searched Mathlib by
   LeanFinder, Loogle and grep, and searched both project Lean roots using lattice,
   integral, single, essential-image, rationalization and triangulated terminology.
   Verdict: true, strictly partial obligations, no applicable duplicate found.
4. Replaced the incorrect stronger equivalence with the shorter existing bounded
   dévissage theorem plus its two mathematical inputs. Imports are limited to statement
   definitions and actual proof dependencies. The no-longer-needed section accounts for
   every original `proof_deps` entry. Read `dag/units/sk-thm-properbasechange.json`:
   its `realized` statement and three steps remain unchanged, and this below-unit
   coefficient argument bypasses none of them. Verdict: pass.
5. Checked the target node's proof against the Lean term, and both new nodes against
   their declarations, docstring plans and source. Their `proof_deps` are the unions of
   their proof-step uses; statements, Lean records, provenance and search records agree.
   Existing node edits are confined to `proof`, `proof_deps`, and `proof_origin`.
   Verdict: pass.

Second reading changed: removed the false unpublished unrationalized equivalence;
implemented bounded truncation dévissage using the existing library theorem; introduced
separate degree-zero and image-closure obligations; corrected dependency metadata and
progress accounting. This does not claim a sorry-free proof of the target.
