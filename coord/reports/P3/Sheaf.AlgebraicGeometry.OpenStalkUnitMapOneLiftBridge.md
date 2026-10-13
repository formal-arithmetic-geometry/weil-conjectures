## What changed

Proved `AlgebraicGeometry.Scheme.exists_open_stalk_hom_of_subscheme_lift` in
`Sheaf.AlgebraicGeometry.OpenStalkUnitMapOneLiftBridge`, preserving its signature and visibility.
Added a proved private helper, `exists_slice_hom_with_subscheme_germ_formula`, in the same module.
It constructs the image open, an equivalence from its slice sheaves to module sheaves on A,
the transported morphism k, and a natural linear stalk comparison a with an explicit germ formula.
The public proof represents a_F(m) by a germ on A using the additive restriction-stalk
isomorphism and applies the supplied hf; cancellation of a_N gives the required equation.

Added the proof-only `import all Sheaf.AlgebraicGeometry.OpenModuleStalkRestrictionComparison`
to use its already proved private `restrictionStalkLinearNatIso`, rather than duplicating its
semilinearity proof. Both applications of that helper and all other transport constructions are
proved. No data is chosen from an unproved existence theorem: k is the preimage under a fully
faithful equivalence, and a is an explicit composition of natural isomorphisms.

Updated the existing node's proof and proof_origin to record this construction and germ argument.
Its proof_deps remain `lem-sc-open-module-stalk-restriction-comparison`. No existing statement,
definition, public import, or other module was changed. No unit-level route is bypassed:
`sk-prop-av-cube.realized` contains no realization by this technical node.

The searches through leanfinder, loogle, msearch grep and local rg found the slice equivalence,
restriction functor composition/congruence, and restriction-stalk germ formulas, but no exact
combined theorem. Read Stacks Project Sheaves Lemma 6.31.1, Tag 00A0 (2)-(3), including its
extension to sheaves of modules. The canonical comparisons are natural on all module sheaves;
no finite freeness, affine condition or hypothesis on the target sheaf is introduced. For A=top
the same equivalences and germ proof apply. An empty A cannot satisfy hxA; zero sheaves and a
zero morphism require no separate case.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.exists_open_stalk_hom_of_subscheme_lift`
(node `new-lem-sc-open-stalk-unit-map-one-lift-bridge`).

The new private helper `AlgebraicGeometry.Scheme.exists_slice_hom_with_subscheme_germ_formula`
is also fully proved. No sorry remains in the delivered module; no holes were added or split off.
The combined file compiled cleanly through lcompile.py in 18.0 seconds. The axiom probe
for the public theorem reported exactly `propext`, `Classical.choice`, and `Quot.sound`
(no `sorryAx`).

## No longer needed

None. No import was removed. The original public import supplies the statement's definitions,
and the new proof-only import supplies the existing proved linear stalk comparison.
The node's sole planned dependency remains used; no planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original comparison dependency's public theorem returns only Nonempty of an unspecified
natural isomorphism. It does not expose a germ formula for that existential comparison, so that
public theorem alone cannot justify the prescribed stalk equation. Its proved private linear
comparison construction is accessible with `import all` and supplies the canonical maps needed
here. The node now records this actual usage and explicitly constructs the scalar compatibility.
No mathematical statement or interface correction was necessary.

## Second reading by P3

1. Compared the complete delivered module with the repository version. The existing
   public theorem's signature, from its name through the type preceding `:= by`,
   is byte-for-byte identical (also checked by a Python assertion). The sole new
   declaration is the proved private germ-formula helper; no definition or public
   import changed. No change record or forced adaptation is needed. Verdict: pass.
2. Compiled the delivered file independently with lcompile.py: clean, 17.7 seconds.
   Compiled a scratch copy with `#print axioms` for both the public theorem and
   private helper: each uses exactly propext, Classical.choice, Quot.sound.
   Searched the delivered Lean for sorry and prohibited declarations: none.
   In the helper, D.preimage is justified by the explicitly constructed equivalences;
   the stalk comparison is built from the proved restrictionStalkLinearNatIso,
   not selected from a theorem with sorry. Verdict: pass.
3. No statements were split off and no holes were added. Read the private helper
   through its germ calculation: hk uses D.map_preimage, hac cancels c, hnk cancels
   b, and the final equality uses naturality of germs under f. It requires neither
   q nor hf, so it is a genuine transport subargument. The public proof uses germ
   surjectivity only to represent a stalk element, then applies exactly hf.
   Checked A=top and zero morphisms/sheaves: all equivalences and equalities still
   apply; A empty is excluded by hxA. Read Stacks Sheaves Lemma 6.31.1, Tag 00A0
   (2)-(3), including its module clause, at https://stacks.math.columbia.edu/tag/00A0.
   The open inclusions and arbitrary module sheaves match that source. Verdict: pass.
4. Searched again with Loogle for Modules.restrictStalkNatIso and with local rg
   for restrictStalkNatIso, overMapCompOverEquiv, and the theorem/helper names.
   Read OpenStalkRestrictionTransport and Modules/RestrictionStalkExtensionIso:
   neither supplies the combined prescribed-germ transport theorem. The existing
   proved private linear comparison is reused rather than copied. The public
   comparison theorem alone only asserts Nonempty, without a germ normalization.
   The original public import is needed by the signature and the added `import all`
   is proof-only and used twice. No old proof dependency became unused, so
   `## No longer needed` is complete. Read sk-prop-av-cube.realized: it has no node
   for this technical transport, and no unit step is bypassed. Verdict: pass.
5. Compared the node with the repository version: only proof and proof_origin
   change. Its retained proof_deps names the linear comparison module actually
   used. Step 1 describes e, D, b, k, the scalar-map equality, a, and the germ
   calculation; step 2 describes the germ representation and application of hf.
   These are the steps in Lean, and the node's unchanged statement still matches
   every input and the conclusion of the public theorem. No new node is needed
   for a fully proved private local proof helper. Verdict: pass.

Changes by the second reader: appended this independent review and recorded the
additional search. No Lean or DAG repair was necessary. One original hole closed,
zero holes added, zero split off; both declarations are independently axiom-checked.
