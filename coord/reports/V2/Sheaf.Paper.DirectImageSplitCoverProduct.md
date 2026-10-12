## What changed

Proved `AlgebraicGeometry.directImage_splitCover_product` with its statement unchanged.
The proof constructs the specified restriction morphisms, proves their naturality by
pullback extensionality, reflects sectionwise limits to sheaf limits, and uses the
product universal property to obtain the isomorphism and component formula.
Added `Sheaf.Paper.SplitCoverSectionsLimit` for the remaining fixed-object geometric
and gluing calculation (original steps 1–2). Updated the parent DAG proof accordingly.
Both modules compile locally without warnings.

## Proved and sorry left

Proved the original module's sole sorry: `AlgebraicGeometry.directImage_splitCover_product`.
One new sorry remains: `AlgebraicGeometry.splitCoverSectionsLimit`, node
`lem-weil-pbc-split-cover-sections-limit`. It asserts a limiting fan of modules for a
fixed étale object, with no naturality or sheaf isomorphism conclusion. The proof of
those further conclusions is complete in the original module. This is a reduction,
not a claim that the resulting theorem is independent of sorry.

Checked the new statement on the empty family (the pullback is empty and the fan is
terminal by the empty cover), a singleton family (restriction along an isomorphism),
and a zero coefficient ring (all section modules are zero).

## No longer needed

Removed the redundant explicit proof import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already exported through the
required public restriction definitions). Removed the earlier attempt's unused
`Sheaf.AlgebraicGeometry.Sites.FiniteEtaleCoproductSections` and
`Mathlib.CategoryTheory.Sites.Whiskering` imports. Neither was in the repository base.
The Type-valued coproduct node `lem-exc-finite-galois-sheaf-sections-coproduct` is not
needed by this delivery.

No longer needed as explicit proof dependencies of the parent or the new node:
`lem-weil-pbc-etale-inverse-image-restriction` (restriction is already a sheaf by the
existing definition), `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`
(linearity is built into ModuleCat morphisms), `def-weil-pbc-abelian-etale-sheaves`
(the sheaf condition is used directly in modules), and
`def-weil-pbc-sites-and-cohomology` (no cohomology calculation here).
The comparison declarations are unused; their module
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` stays publicly
imported because the original statement uses `localizationRestriction`.
The geometry dependencies of the old steps 1–2 remain needed by the new gluing node;
they are not pruned. Public imports needed by the original statement are retained.
The parent also removes `def-weil-open-immersion`,
`lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-etale-composition-cancellation`,
and `def-weil-sheaf-of-modules-category` from its direct `proof_deps`: these now
belong to the new sectionwise node, so they are retained transitively.
The second reading additionally removes
`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`: its sets-only statement is not
used in the ModuleCat proof, which uses the generic Mathlib reflection tools directly.
No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped at the Type/ModuleCat mismatch without delivering a
reduction. A pointwise limiting-fan statement isolates that issue and allows the
naturality and categorical assembly to be proved now. The existing Type-valued
coproduct theorem is a potential tool for proving the new node, but requires
additional geometric and empty-section hypotheses and is not directly applicable.
No existing statement was changed and no false statement was found.

## New nodes

`lem-weil-pbc-split-cover-sections-limit`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-split-cover-sections-limit.json`,
records the fixed-object section fan theorem in
`lean/Sheaf/Paper/SplitCoverSectionsLimit.lean`. Its source, full gluing proof,
searches, and Lean statement are recorded. No change records are needed.


## Second reading by V2

1. **Visible declarations — pass.** Compared the complete diff of
   `DirectImageSplitCoverProduct.lean` with the repository module. The only
   changes are the private proof import and the body of
   `AlgebraicGeometry.directImage_splitCover_product`; its entire signature and
   original docstring are byte-for-byte unchanged. No existing definitions or
   other modules are changed, and no statement-change record is required.
2. **Proof and trust — pass as a reduction.** Both modules compile locally in
   import order without warnings. Read the naturality proof: functoriality
   reduces it to equality over Y, and the two pullback projections establish
   that equality. The sheaf-to-presheaf reflection, joint evaluation reflection,
   fan comparison, and `Pi.lift_π` finish the asserted isomorphism with exactly
   its specified legs. Scanned both modules: the sole remaining `sorry` is the
   named `splitCoverSectionsLimit`; no forbidden declarations or hollow
   definitions occur. A scratch `#print axioms` for each theorem reports exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The original
   theorem is therefore reduced, not yet axiom-closed.
3. **New statement — pass.** Read the fixed-W fan statement against the source
   proof of Stacks 095B (`lemma-pushforward-locally-constant`, in the local
   etale-cohomology.tex copy, lines 9982–9991), and the equalizer and empty-cover
   clauses of sites.tex Definition 00VM. The colimit cofan gives the disjoint
   covering sheets; both inverse equations identify each pullback sheet with W.
   Thus the displayed restrictions are the product legs for the sheaf condition.
   Empty J forces Y and its pullback empty, with terminal sections; singleton J
   gives restriction along an isomorphism; empty X forces every V_j empty; for
   the zero ring all section modules are zero. No case is excluded. This lemma
   isolates geometry and gluing at one W, while the parent genuinely proves
   naturality and the sheaf-product assembly; it is not a renamed sheaf
   isomorphism statement. Repeated LeanFinder and Mathlib grep with different
   terms, and searched both local Lean roots and the upstream checkout.
   `Scheme.Etale.isIso_piLift_of_disjoint` is a useful existing categorical
   gluing tool for the eventual proof, but requires the covering sieve and
   disjoint ranges of the displayed lifts. Those geometric hypotheses are not
   provided automatically by it. The Type-valued coproduct theorem likewise
   does not directly supply this statement. The new node records this finding.
4. **Route and pruning — pass after repair.** Checked the full old dependency
   list against the parent and new node together. The geometry dependencies
   remain transitively used; the six obsolete dependencies are listed above,
   including the sets-only limit statement removed on second reading. Both
   public parent imports are used by its signature (module-sheaf products and
   literal restriction); the new lemma is imported privately. The new module's
   public imports provide exactly the schemes, site and module-fan statement.
   Read `dag/units/sk-thm-p1.json`, including every `realized` entry: neither
   this helper nor its parent is a realized unit statement or step. The original
   decomposition-and-gluing route is retained below that level.
5. **DAG agreement — pass after repair.** The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`. Its three steps describe the actual
   fixed-object input, naturality proof and categorical assembly. The new node
   has the required source, full proof, searches, creation and blueprint data,
   chapter/unit, and verbatim Lean signature. Added the missing citation to
   `lem-weil-pbc-scheme-coproduct-family` for the disjoint-cover consequence of
   `hcolim`. Removed the parent citation to the sets-only limit node; the proof
   uses Mathlib's generic categorical declarations. Corrected the recorded grep
   query to the query actually present in searches.jsonl, marked the failed
   LeanSearch unavailable, and recorded the additional independent search.

Second-reading changes: no Lean proof or signature changes; completed the new
module's source/blueprint header, repaired the DAG citations and search records,
and completed the pruning explanation. The sectionwise geometric lemma remains
open and has its complete natural-language proof and node.
