## What changed

Proved `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine` with its
signature unchanged. The complete Lean proof writes the degree as `(n+1)+1`, obtains a
short exact sequence, uses affine quasi-coherent vanishing in degrees `n+1` and `n+2`,
and applies the existing proved `Sheaf.H.δSucc_surjective`. A surjection from a
subsingleton group gives a subsingleton target via `Function.Surjective.subsingleton`.
Both proof imports are non-public; the original public Kummer import is retained.

Two independently provable inputs remain. `ArtinSchreierSequenceScheme.lean` states
existence of a short exact sequence on an arbitrary scheme with `p=0`; it imposes no
affineness and contains no cohomology assertion. `EtaleAffineQcoherentULift.lean` realizes
the existing affine quasi-coherent acyclicity node with the coefficient universe
`AddCommGrpCat.{u+1}`, for every quasi-coherent module, without any characteristic
assumption. These are strictly different parts of the argument, combined in the main
module by a checked long-exact-sequence proof.

The existing `lem-sc-etale-affine-qcoherent` node is reattached to its lifted-coefficient
realization, with the same mathematical statement and the same affine Čech/Amitsur
proof route. Its old small-coefficient declaration is not edited. The node proof explains
how lifting cocycles and preimages preserves the Amitsur calculation. A node for the
existing assigned declaration is added because no node's `lean` record previously named
that exact general-affine statement. The three nodes together record the actual route.

All three Lean modules compile locally without warnings. The boundary degree is `q=2`,
where the proof uses `H¹(G)=H²(G)=0` and does not assert `H⁰(G)=0`. The statements also
cover the empty affine scheme, the zero quasi-coherent module, and arbitrary prime p.

## Proved and sorry left

Proved (from the two named inputs):
`AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`, node
`lem-sc-affine-artin-schreier-vanishing`. No sorry remains in the assigned module.

Sorries left in this delivery, each with source and full proof in its docstring:

- `AlgebraicGeometry.Scheme.exists_artinSchreier_shortExact`, node
  `lem-sc-artin-schreier-sequence-scheme`, new module
  `Sheaf.AlgebraicGeometry.ArtinSchreierSequenceScheme`.
- `AlgebraicGeometry.Etale.etale_affine_qcoherent_ulift`, existing node
  `lem-sc-etale-affine-qcoherent`, new module
  `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`.

## No longer needed

No original import is removed: `Sites.Kummer` supplies `constantZMod` in the statement.
The new acyclicity module does not import the old `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
module; it imports only the associated sheaf and the category/coefficient infrastructure
its statement needs. The old small-coefficient theorem is not needed on this proof branch.

The assigned proof does not need `lem-sc-ga-cohomology`,
`lem-sc-etale-zariski-qcoh-comparison`, their modules
`Sheaf.AlgebraicGeometry.EtaleZariskiCohomology` and
`Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`, nor the curve-only
`Sheaf.AlgebraicGeometry.ArtinSchreierSequence` declaration `artinSchreier_shortExact`
(node `lem-sc-as-sequence`). None is imported. This is branch-local pruning; other targets
may still need these modules. The affine Čech/Amitsur proof of acyclicity remains required.
No proper-curve compactification, finiteness, or Lang–Steinberg input is used in the affine
argument. No chapter or unit route is changed.

Second reading removed the redundant public import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` from
`ArtinSchreierSequenceScheme.lean`; all three delivery modules still compile.
No old `proof_deps` edge of an attached item node was removed: the assigned source
declaration had no exact node attachment, and the acyclicity node retains every
planned dependency. The other modules named above are unused candidate routes,
not newly removed dependency edges.

## Where the brief, the DAG or earlier work was wrong

The modules returned by searching for this assigned module in node JSON were references
in notes, not exact attachments of its declaration. The assigned theorem is more general
than `lem-sc-affine-constant-second` (arbitrary affine schemes and all degrees at least two).
It also cannot use the curve-only `artinSchreier_shortExact`: the assigned hypotheses give
neither a ground field nor a curve structure. The new general-scheme input supplies the
missing scope, following Stacks 0A3J.

The existing quasi-coherent acyclicity declaration uses `AddCommGrpCat.{u}` while
`constantZMod` uses `AddCommGrpCat.{u+1}`. These are distinct Lean categories, so direct
application does not typecheck. The lifted realization is attached to the same existing
mathematical node instead of duplicating the acyclicity statement in a new DAG node.
Its proof uses the recorded affine Čech route, without an unsupported assertion that
universe lift preserves injective sheaves.

`lem-sc-etale-affine-qcoherent` is used as a generic affine-acyclicity tool in the affine
part of `lem-sc-artin-schreier-dimension`; the existing closed source long-exact Ext lemmas
are generic tools too. There is no bypass of a unit's own proof. The acyclicity node's
planned dependencies are retained for its next worker.

The local literature files referenced by the old nodes are absent on this machine.
Checked the primary Stacks pages directly: https://stacks.math.columbia.edu/tag/0A3J,
https://stacks.math.columbia.edu/tag/03P2 and https://stacks.math.columbia.edu/tag/03F9.
The new node records give primary URLs. LeanSearch returned HTTP 500; its queries are
recorded as unavailable, not as failed matches. LeanFinder, Loogle, repository searches,
and Mathlib grep supplied no matching existing theorem.

## New nodes

`lem-sc-artin-schreier-sequence-scheme` states existence of the characteristic-p short
exact sequence for any scheme, with the middle sheaf fixed as the lifted associated
structure-module sheaf. Its proof constructs Frobenius-minus-identity, proves local
surjectivity by the monic polynomial with derivative -1, identifies the kernel on
geometric stalks, and applies conservativity. The maps' sectionwise descriptions are
forgotten only after construction; the cohomological application needs just exactness.

`lem-sc-affine-artin-schreier-vanishing` attaches the existing source declaration's exact
general-affine statement. Its two proof steps match the compiled proof: obtain the short
exact sequence, then combine the two adjacent acyclicity groups with the connecting map.
Both new nodes are in `sec-curve-estimates`, within the affine-case paragraph of
`lem-sc-artin-schreier-dimension`. No change record is needed: no existing definition,
statement, or public interface is changed.


## Second reading by N1

1. **Visible declarations unchanged — pass.** Read the repository and sandbox files
   with `diff -u`: the assigned theorem's signature is byte for byte unchanged; the
   only edits there are two non-public imports and its proof body. The existing
   Kummer public import, definitions, attributes, and docstrings are unchanged.
   The two added modules contain only new named theorems, no new definitions.
   The old small-coefficient acyclicity declaration is not edited. No change record
   is required, since no existing statement or definition changes.

2. **Proof and axioms — pass with the two reported open inputs.** Compiled all three
   modules with `lcompile.py --all` in import order, without warnings or errors.
   Checked scratch copies with explicit `#print axioms` for all three declarations:
   each lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The assigned theorem has no `sorry`; the only two delivery sorries are exactly
   `exists_artinSchreier_shortExact` and `etale_affine_qcoherent_ulift` listed above.
   No forbidden declaration, axiom escape, or hollow definition occurs. Read
   `Sheaf.H.δSucc_surjective` in the source: it uses vanishing of the middle term
   at degree n+2; the separate n+1 vanishing supplies the subsingleton source.
   Thus the proof really combines exactness and two adjacent acyclicity degrees.
   It is a reduction from open inputs, not an axiom-free completed target.

3. **Split statements and sources — pass.** Read Stacks
   [0A3J](https://stacks.math.columbia.edu/tag/0A3J),
   [0A3K](https://stacks.math.columbia.edu/tag/0A3K),
   [03P2](https://stacks.math.columbia.edu/tag/03P2), and
   [03F9](https://stacks.math.columbia.edu/tag/03F9).
   Exactness in 0A3J requires only a prime and characteristic p, matching the
   scheme-level input: global p=0 restricts to every section ring. There is no
   hidden field, reducedness, connectedness, dimension, or affine assumption.
   For a disconnected F_p-algebra, the kernel consists of locally constant
   prime-field values, not just a single global constant; the docstring's
   comaximal-factor decomposition handles this. On the empty scheme both
   constant and structure sheaves are zero, so exactness still holds. The cover
   polynomial has degree p>0 and derivative -1 even for p=2 and nonreduced rings.
   Read every cited dependency statement of the sequence node: pullback of the
   structure module identifies its sections; local surjectivity proves epi;
   exact stalks, the local-ring kernel result, and conservative stalks identify
   its kernel. None of these dependencies assumes a curve or a ground field.
   The lifted acyclicity input assumes precisely affineness, quasi-coherence,
   and positive degree. Its proof verifies all three 03F9 hypotheses using
   finite affine refinements and Amitsur exactness; lifting a cocycle and a
   chosen preimage preserves exactness. Checked the zero module, empty affine,
   q=1 for acyclicity, and q=2 for the assigned reduction. Neither input restates
   the assigned theorem: one has no cohomology or affineness assertion, the other
   has no characteristic or constant-coefficient assertion. Both have complete
   proof docstrings and nodes. Independent searches used new wording in
   LeanFinder (Frobenius-minus-identity exactness; higher cohomology of lifted
   quasi-coherent sheaves), Loogle (ulift and H), and logged Mathlib grep
   (frobenius/sheaf and ulift/cohomology). No matching result was returned.
   Repository and upstream searches confirm the existing sequence is curve-only
   and the small-coefficient affine acyclicity theorem is still sorry. These
   inputs require substantial sheaf constructions and cannot be closed by a
   short existing lemma application.

4. **Route and pruning — pass after import cleanup.** Read the small-coefficient
   acyclicity statement, associated-sheaf definition, existing curve sequence,
   and the source long-exact-sequence lemma. The assigned proof takes the direct
   Artin–Schreier plus affine-acyclicity route. Removed the redundant public
   Quasicoherent import from the new sequence module; the remaining imports
   supply its signature. In scratch tests, removing HasExt, the sheaf
   Grothendieck infrastructure, or ConcreteCoefficients from the acyclicity
   module prevents its signature's Ext instance from synthesizing, so these
   are statement infrastructure and appropriately public. Both theorem inputs
   remain non-public imports of the assigned module. The No longer needed
   section now distinguishes unused candidate routes from genuinely removed
   old edges. Read sk-prop-cd's statement, steps, and realized record and the
   affine paragraph of lem-sc-artin-schreier-dimension: their Artin–Schreier
   route is retained. No unit record is edited, and the original affine
   acyclicity node's Čech/Amitsur dependencies all remain.

5. **DAG agrees with Lean — pass after textual repair.** The new attached item
   node records exactly the sequence witness followed by the two vanishings,
   δSucc surjectivity, and subsingleton transfer used in Lean. The sequence
   node records the section construction, étale covering, kernel, and exactness.
   The acyclicity node keeps its original mathematical statement and dependencies
   and explains the coefficient lift in its Amitsur step. Verified for every
   delivered node that proof_deps equals the union of proof-step uses. Compared
   the existing node JSON with the repository: only lean, proof, and proof_origin
   change; all other fields agree. New nodes carry their source, blueprint
   ancestor and place, chapter/unit, search records, creation record, and exact
   Lean declarations. Corrected `Xover` to `Cover` and `Xonclusion` to
   `Conclusion` in the new sequence node's proof text.

Second-reading changes: removed the redundant Quasicoherent public import,
corrected the two node-proof typos, clarified actual versus candidate pruning,
and added this review. The assigned Lean proof and every statement are unchanged.
