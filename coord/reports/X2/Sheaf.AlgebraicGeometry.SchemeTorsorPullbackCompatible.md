## What changed

Replaced the single sorry in `AlgebraicGeometry.Etale.scheme_torsor_pullback_compatible`
with a compiling proof combining two strictly separate parts: construction of an equivariant
sheaf morphism and invertibility of a supplied unit-equivariant morphism. The proof obtains
`f` and its action equation, proves `IsIso f`, and returns `asIso f`; its hom is definitionally
`f`. The theorem's signature and existing docstring are unchanged. Added two statement
modules and their nodes and updated the target node's proof route. No definitions or
existing statements were changed, and no data is chosen from a mere existence theorem in
a definition.

Both parts have been checked on the trivial group, empty schemes/site objects, and
nonconnected bases. The invertibility lemma uses local nonemptiness rather than global
sections. Its target torsor is arbitrary: no representative, choice of `e`, or torsor class
is assumed. The morphism-construction lemma does not assert invertibility.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.scheme_torsor_pullback_compatible` (one original hole).
This is a decomposition, not a complete proof without sorry dependencies. Added two holes:

- `AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom`, node
  `lem-weil-pbc-scheme-torsor-pullback-equivariant-hom`.
- `AlgebraicGeometry.Etale.scheme_torsor_pullback_equivariant_hom_isIso`, node
  `lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso`.

No sorry remains in the assigned module. The two new modules contain exactly the named
public theorem with its entire proof left as sorry. All three modules compiled locally in
import order. The first compile exposed a `haveI` style warning, fixed by using `have`.

## No longer needed

Removed proof imports `WeilConjectures.ConstructibleSheaf.Defs`,
`Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable` and
`Sheaf.Paper.ConstantSheafSectionsLocallyConstant` from the assigned module; replaced them
with the two new intermediate statement modules.

The representable comparison node `lem-galois-inverse-image-representable` and its module
are still needed by the construction part, so are not globally pruned. Likewise the
constant-sheaf comparison, torsor definitions and scheme torsor representation remain
needed below the construction/invertibility parts.

The new construction route uses local representation of constant sheaf sections rather
than the global locally constant comparison:
`lem-weil-pbc-constant-sheaf-sections-locally-constant` and
`Sheaf.Paper.ConstantSheafSectionsLocallyConstant` are no longer needed for this proof.
This is pruning of this branch; other target branches may still reach the module.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's representable inverse-image lemma asserts a nonempty natural isomorphism; it
does not state its unit evaluation formula. The original plan therefore needs additional
glue for action compatibility, not merely an application of that declaration. The new
construction statement records this glue as a strictly weaker morphism construction.

The original constant-sections lemma is stated for a coefficient type in universe `u`,
whereas this module uses `M : Type (u + 1)`. Applying it would require a finite-group
universe reduction and compatible transport. Local representation avoids that mismatch.

Tag 03RV is finite locally constant representability, not the assertion that equivariant
torsor morphisms are invertible. The latter appears in Stacks Section 03AG immediately
after the torsor definition, and is already implemented by
`CategoryTheory.Sheaf.Torsor.Iso.ofHom` in the source library. The new source annotations
use 03AG. The original declaration's docstring has been preserved.

The literature tex file is absent on this machine, so the source was read at the official
Stacks pages: https://stacks.math.columbia.edu/tag/03Q1 (parts 2 and 4),
https://stacks.math.columbia.edu/tag/0A5G (proof), and
https://stacks.math.columbia.edu/tag/03AG (definition and equivariant morphisms).

Searches used LeanFinder, Loogle and grep; LeanSearch returned Internal Server Error and
is recorded as unavailable. Direct source search also found
`etale_torsor_h1_functoriality` and `etale_inverse_image_lifting_torsor`. They provide an
unspecified inverse-image torsor and its unit equation, not the required morphism to the
specified `R`. They confirm the generic invertibility argument's starting point, but
extending a unit equation to all destination-site sections remains substantial glue.

## New nodes

`lem-weil-pbc-scheme-torsor-pullback-equivariant-hom`, module
`Sheaf.AlgebraicGeometry.SchemeTorsorPullbackEquivariantHom`, isolates the construction
and equivariance, without requiring an inverse. Its proof words detail representable
comparison, coefficient transport, constant sections and local gluing.

`lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso`, module
`Sheaf.AlgebraicGeometry.SchemeTorsorPullbackEquivariantHomIsIso`, asserts invertibility
for any supplied morphism satisfying the unit equation. It has no representing scheme
hypotheses for `R`. Its proof words explain preservation of torsors, extension of the
unit equation by local section representations, and local bijectivity.

No change record is needed: all existing signatures and definitions are unchanged,
and the assigned module changes only proof imports and its proof.

## Second reading by X2

1. Compared the sole existing delivered module with the repository version using `diff`.
   Restored its original signature whitespace before `:=`; the signature and docstring are
   byte-for-byte unchanged. Only proof imports and its proof body differ. No definitions change.
   Verdict: pass.

2. All three modules compile locally in import order without warnings. The assigned module has
   no sorry; the two named public helper theorems are exactly the two holes listed above.
   There are no definitions, hidden holes, axioms, unsafe/opaque declarations or foreign hooks.
   Scratch-copy `#print axioms` for all three declarations reports only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`. The delivery axiom probe and
   dry-run preflight pass. Verdict: pass.

3. Read both helper signatures, docstring proofs and nodes, and checked trivial coefficients,
   empty base/site objects, identity base change and disconnected bases. Construction supplies
   a morphism without asserting an inverse; invertibility starts with an arbitrary supplied
   morphism and requires no scheme representative for R. The reductions are true and strictly
   simpler, not renamed copies of the target. Fresh LeanFinder, Loogle and grep searches used
   unit-equivariance and inverse-image-map terminology. No exact replacement was found.
   `Torsor.Iso.ofHom` requires full destination-site equivariance; neither that result nor
   `etale_torsor_h1_functoriality` supplies the remaining unit-to-full-equivariance argument.
   Both holes require substantial further work and are retained. Verdict: pass.

4. The proof genuinely eliminates the target hole by constructing f and applying the separate
   invertibility criterion. This is a decomposition with one hole closed and two added (net -1),
   not a sorry-free proof. Reviewed `dag/units/sk-thm-p1.json`: none of the removed dependencies
   realizes a unit statement or step. The old proof dependencies are all accounted for above:
   torsor definitions, scheme representation, representable comparison and constant comparison
   remain below the new construction; only the locally-constant-sections route is pruned.
   Added the previously omitted `WeilConjectures.ConstructibleSheaf.Defs` removed import to the
   report. No global module unreachability is claimed. Verdict: pass.

5. Checked the target node changes are restricted to the allowed proof fields and that each
   new node has its source, searches, complete proof route, blueprint, unit, creation and Lean
   records. The lifting-torsor node named in the invertibility plan applied only to fibre torsors
   of short exact sequences; replaced it by the unit-compatible algebraic-structure comparison
   `lem-weil-pbc-etale-inverse-image-algebraic-structures`, which supplies the required generic
   finite-limit preservation and coefficient comparison. The new nodes describe future proofs;
   their current Lean bodies are exactly sorry. Verdict: pass.

Changes in second reading: signature whitespace, missing removed-import accounting, and the
invertibility node's preservation dependency and explanation. No mathematical statements or
completed Lean proof were rewritten. Source checked independently at
https://stacks.math.columbia.edu/tag/03AG and https://stacks.math.columbia.edu/tag/03Q1.
