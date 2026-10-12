## What changed

Completed `AlgebraicGeometry.CurveCoefficientPair.finite_pushforward_data`, the sole
remaining sorry of the original module. The chosen middle term is the actual inverse
image of the direct image, and the second term is the kernel of its counit. The finite
stalk formula gives the product projection; the counit-stalk identity makes its stalk
map epic. Naturality of the explicitly universe-lifted stalk isomorphism transports
this to the conservative algebraic-closure family, which reflects epimorphisms.
Stalk preservation of finite limits gives an injective kernel-stalk map. Pulling a
positive annihilator back through that injection proves kernel torsion. The canonical
kernel sequence is then short exact.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf`
and `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback`. The latter matches
constructibility of the underlying set sheaf with genuinely finite stalks; the source
library's finitely-generated abelian-stalk constructibility would not suffice.
No signatures, definitions or public imports changed. Corrected the misleading
helper docstring and wrote the complete implemented proof into the data docstring.
Updated both existing DAG nodes' proof, proof_deps and proof_origin to the implemented
route. No new nodes or statements were introduced.

The supplied earlier sandbox attempt failed compilation because the universe of
`uliftSheafFiberIso` was unresolved, then used `epi_of_epi_fac` on the wrong side of
its naturality equation. Both are repaired. Its local finite-limit-preservation sorry
is replaced by AB5 universe shrinking and the existing Mathlib instance.

## Proved and sorry left

`AlgebraicGeometry.CurveCoefficientPair.finite_pushforward_data`
(node `lem-weil-pbc-finite-pushforward-data`) is proved from existing declarations.
The original `constructible_of_short_exact` and
`isConstructible_of_finite_pushforward` proofs are preserved, with docstrings updated.
There are no sorries left in the item and none added elsewhere. One of one original
sorries is closed; zero split off.

The proof still depends on existing stated results, particularly
`AlgebraicGeometry.Scheme.isConstructibleEtaleSheafOfSets_upperStar`
(node `lem-weil-pbc-constructible-etale-set-pullback`), exactly as stage 3 permits.
This is a reduction from the finite-image counit and kernel argument to existing
pullback constructibility, not a renamed copy of the item.

## No longer needed

Removed these original proof imports:

- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.Paper.InverseImageStalkGerm`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`

The earlier sandbox's added `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
import was also unnecessary and is removed.

The descent node now depends directly only on `lem-weil-pbc-finite-pushforward-data`
and `lem-weil-pbc-curve-constructible-sub-quotient`. The data node records the actual
stalk, torsion and finite-stalk pullback dependencies. The prior separate
`lem-weil-pbc-geometric-stalks-detect-mono` route through a cokernel is unnecessary:
the conservative family reflects epimorphisms directly.

The hand-written pullback-stratification route is replaced by the existing
`lem-weil-pbc-constructible-etale-set-pullback` theorem. Thus
`lemma-constructible-pullback-stratification`,
`lem-weil-pbc-inverse-image-composition`,
`lemma-constructible-pullback-locally-constant`,
`lemma-constructible-iso-invariance`, and `lemma-openclosed-stalk-upperstar`
are no longer direct dependencies of this item's nodes. They may still be needed
inside the existing pullback theorem or other library modules; this report does not
claim they are globally unreachable. The same applies to the inverse-image stalk
comparison: the implemented counit identity already packages its isomorphism, so
`Sheaf.Paper.InverseImageStalkGerm` is not needed directly.
Definitions previously listed as proof dependencies remain available through the
unchanged statement imports and need no separate proof edges.


Complete removed-edge inventory for the descent node (the original data node had
no proof edges):

- `def-constructible-locally-constant`
- `def-constructible-stratification`
- `def-weil-constructible-subset`
- `def-weil-geometric-point`
- `def-weil-pbc-abelian-etale-sheaves`
- `def-weil-pbc-constructible-torsion`
- `def-weil-pbc-curve-setting`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-counit-stalk-germ-restriction`
- `lem-weil-pbc-finite-stalk-formula-restriction`
- `lem-weil-pbc-geometric-stalks-detect-mono`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-torsion-sheaf-characterizations`
- `lemma-constructible-iso-invariance`
- `lemma-constructible-pullback-locally-constant`
- `lemma-constructible-pullback-stratification`
- `lemma-openclosed-stalk-upperstar`
- `lemma-weil-pbc-finite-stalk-formula`
- `prop-weil-pbc-geometric-stalks-exact`

These are removed direct edges of the descent node, not claims of global pruning.
The counit restriction, finite-stalk formula and its restriction form, torsion
characterization, and stalk exactness are now recorded under the data node.
The definitions stay available through the unchanged statement imports.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left two anonymous sorries inside `finite_pushforward_data`;
these are both closed using existing declarations and instances. No new missing
statement is necessary. The original data node had empty proof_deps despite its
non-elementary two-step proof; this delivery records the dependencies used in Lean.
The original docstring for `constructible_of_short_exact` described the finite
pushforward theorem rather than its actual quotient statement; it now describes the
helper accurately.

The existing pullback theorem in the smooth-purity chapter is used as a general tool,
not as a replacement of the proper-base-change unit's route. Neither of this item's
nodes realizes a unit statement or unit proof step in `dag/units/sk-thm-p1.json`.
The finite-pushforward/counit/quotient argument is unchanged mathematically.
The Stacks sources 03QP (1), 095G and 09BH (2) were read online because the local
Stacks TeX file is not present. No unreferenced new result was introduced.

Validation recovery (fifth worker, 2026-10-12): the existing pullback dependency is
now available in the compiled library. The retained delivery module compiles cleanly
through `lcompile.py` in 4.2 seconds, with no errors or warnings. Checked all three
existing theorem signatures against the repository verbatim modulo whitespace;
none changed. There are no sorries or forbidden declarations, all lines have at
most 100 characters, and both node copies change only proof, proof_deps and
proof_origin, with proof_deps exactly the union of step uses. The added pullback
import passes `import_direction.py may`. Neither modified node realizes a unit
statement or step, so the unit route is preserved. Earlier missing-artifact
failures were infrastructure blockers; no workaround or duplicate theorem was added.

The first recovered dry run rejected the saved global `open CategoryTheory.Limits`
command as a change to what importers see. Removed that addition and qualified
limits names within the proof instead. No change record is needed: the module's
public commands now match the repository. The delivery wrapper explicitly allows
the second-reading section to remain absent for this worker's dry run; the next
worker supplies it. No second-reading section was authored here.

Final validation (2026-10-12): `deliver3.py N2
Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent --no-push`
printed OK. Local compilation, the delivery axiom probe and server compilation
passed. Preflight passed except for the second reading, explicitly allowed by
the wrapper for this worker's dry run. Nothing was pushed. The next worker should
review this proof and both DAG node copies, add the second-reading section, and
deliver according to its brief.

## Second reading by N2

1. Compared the complete delivered module with the read-only repository using diff,
   and separately compared each theorem header through `:= by` byte for byte.
   All three existing signatures are identical. No definitions, public imports,
   namespace/open commands, or target statements changed. Verdict: pass.
2. Compiled the delivered file with `lcompile.py`: exit 0 in 3.3 seconds, no errors
   or warnings. A scratch copy with `#print axioms` for all three declarations
   compiled in 3.1 seconds. Each lists only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter comes from existing imported open
   results, including the finite-locally-constant pullback stratum and the curve
   sub/quotient development; there is no sorry in this delivery. Checked for
   forbidden declarations and hollow definitions: none. Verdict: pass as a
   stage-3 reduction, not yet an axiom-free closure of all dependencies.
3. There are zero split-off statements and zero new declarations or nodes.
   Read the finite-stalk isomorphism, its projection equation, counit equation,
   pullback constructibility signature and torsion characterization. The counit
   is genuinely epic: the selected fiber contains the given upstairs point, even
   without surjectivity of f. Zero sheaves and empty schemes cause no exception;
   torsion of the kernel uses a positive annihilator and injectivity, not a uniform
   exponent. No item-restating helper was added. Verdict: pass.
4. Read the argument from the descent theorem through the data theorem to its
   dependencies. Searched the library for finite-pushforward constructibility
   descent and searched Mathlib with a distinct counit-epimorphism query via
   `msearch.py`; no directly applicable shorter theorem was found. The abstract
   faithful-right-adjoint counit lemma would require a separate faithfulness
   argument here. Every retained proof import supplies a declaration used by
   the proof; all added imports are plain imports. Checked sk-thm-p1's realized
   statement and steps: neither modified node realizes a unit step, and the
   finite-pushforward/counit/quotient route is preserved. The report now lists
   every old proof edge removed from the descent node, distinguishing relocated
   dependencies from global pruning. Verdict: pass after report repair.
5. Compared both JSON files against the repository: only `proof`, `proof_deps`
   and `proof_origin` differ. Each proof_deps is exactly the union of the step
   uses. Read the Lean declarations or Mathlib matches of all dependencies:
   the data node records the torsion pullback, finite set-stalk constructibility,
   finite-stalk projection, counit identity, conservativity, and finite-limit
   preservation used in Lean. The descent node records data and the quotient
   lemma. No new-node fields or change records are needed. Verdict: pass.

Second-reading changes: completed the removed-edge inventory and recorded this
independent review and its axiom limitation. No Lean or DAG repair was necessary.
