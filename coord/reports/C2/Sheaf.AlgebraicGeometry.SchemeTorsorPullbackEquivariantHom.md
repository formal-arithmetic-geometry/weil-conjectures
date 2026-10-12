## What changed

Proved `AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom` without changing its
statement. The proof constructs a natural transformation by base-changing each represented
point and composing with `e.hom`, takes its adjunct, and composes with the torsor isomorphism
provided by `hrepr`. A proved private helper checks the scheme action on open fibres of a
locally constant coefficient by checking both fibre-product projections and applying `hact`.

Added the fully proved module
`Sheaf.AlgebraicGeometry.EtaleConstantSheafPullbackUnitContinuousMap`. Its theorem identifies
the coefficient adjunction unit, followed by the constant-sheaf comparison, with precomposition
of continuous functions by the first fibre-product projection. It proves this through
adjunction uniqueness and the existing presheaf-unit identity for the continuous-map comparison.
It requires no finiteness hypothesis. Updated the item's DAG proof and dependencies to match
this route; added the node for the coefficient formula. The new import is proof-only.

Both modules compile cleanly through `lcompile.py --all`; `deliver3.py --no-push` passed the
compile, axiom probe and static preflight. No delivery was pushed.

## Proved and sorry left

Closed the single existing hole:
`AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom`
(node `lem-weil-pbc-scheme-torsor-pullback-equivariant-hom`).

The new theorem `AlgebraicGeometry.Etale.constant_pullback_unit_continuousMap`
(node `lem-weil-pbc-constant-pullback-unit-continuous-map`) and the private helper
`baseChange_smulHom` are also proved. There are no remaining or added `sorry`s in either module;
this is a proof, not a decomposition. The axiom probe passed.

Edge cases: the coefficient theorem has arbitrary discrete abelian M, including the trivial
group and infinite groups, and arbitrary i and W. Its terminal-object calculation preserves
constant functions even on an empty scheme. The action helper uses a covering by all open
fibres, including empty fibres, so it does not assume the source or a fibre is nonempty.
No object was selected from an unproved existence theorem.

## No longer needed

Removed the following direct proof-only imports from the item:

- `Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`;
- `Sheaf.Paper.SiteSheafificationSectionsLocal`;
- `WeilConjectures.CategoryTheory.Sites.Torsor`;
- `WeilConjectures.ConstructibleSheaf.Defs`.

The first two modules and their nodes `lem-galois-inverse-image-representable` and
`lem-weil-pbc-site-sheafification-sections-local` are not used by this proof. The direct
adjunction construction makes the representable-comparison existence statement unnecessary;
the continuous-map calculation makes local representatives after sheafification unnecessary.
In particular the disputed local-injectivity clause is never used.

The last two removed imports were redundant: the needed torsor and constant-sheaf definitions
remain available through the retained public imports. Their nodes `def-sc-gm-torsor` and
`lemma-constructible-pullback-constant` remain proof dependencies. The item retains its public
imports because its statement needs them. No claim is made that the removed modules are
unreachable through other branches of the project's targets.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG and docstring describe a longer route through
an unspecified representable comparison and local sheafification representatives. The proof
instead constructs the required adjunct explicitly and proves the coefficient calculation
using the existing continuous-map model. The updated DAG records the actual proof. The
existing declaration docstring was retained, and its description is an alternative valid
argument rather than the literal implementation of this delivery.

No unit statement or realized unit step was bypassed: the item and the new coefficient lemma
are below those steps in `sk-thm-p1`.

## New nodes

`lem-weil-pbc-constant-pullback-unit-continuous-map` is a fully proved coefficient formula in
`lean/Sheaf/AlgebraicGeometry/EtaleConstantSheafPullbackUnitContinuousMap.lean`, with declaration
`AlgebraicGeometry.Etale.constant_pullback_unit_continuousMap`. It contains neither a torsor
nor a choice of a sheaf morphism: it computes the existing constant-sheaf comparison on the
existing adjunction unit. It is a strictly separate coefficient calculation, and adds no hole.
The node records the exact Lean signature, the adjunction calculation, and LeanSearch,
LeanFinder, Loogle and source searches (LeanSearch was unavailable). No change record is
required: no existing statement, definition or public import was changed.

## Second reading by C2

1. Compared the delivered item module with the repository version. The theorem signature and all existing declarations are unchanged; only proof-only imports, a private helper, and the proof body changed. The new coefficient theorem is in a separate module and has a matching node.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no errors. The files contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definitions. The proof uses only ordinary definitions and existing theorems.
3. Checked the split-off coefficient statement against its Lean type and edge cases described in its docstring. It is strictly smaller than the target, has no finiteness hypothesis, and its node records the source, proof route, searches, and declaration exactly. No duplicate declaration was found in the library.
4. Verified pruning: the removed imports are unused by the delivered proof, and the item node's `proof_deps` and proof steps match the actual helper, coefficient theorem, torsor comparison, and constant comparison uses. The unit `sk-thm-p1` remains recorded and its route is not bypassed.
5. No statement or definition change was made, so no downstream adaptation or change record is required. The DAG and Lean declarations agree.

Changed nothing during this second reading; the reviewed delivery is ready for `deliver3.py`.
