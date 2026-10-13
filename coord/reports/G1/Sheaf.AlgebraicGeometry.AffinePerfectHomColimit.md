## What changed

Replaced the single `sorry` in
`Sheaf.AlgebraicGeometry.AffinePerfectHomColimit` with a complete proof, preserving
its signature and all existing public imports. Added proof-only imports of
`Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Mathlib.CategoryTheory.Limits.Types.Filtered`, and the two new descent modules.

Three fully proved private helpers show that scalar extension preserves
K-projectivity, every derived map from such a source has a chain-map representative,
and equality of representatives is equivalent to existence of a homotopy. The
injectivity proof represents two colimit elements at one common stage, uses
`hcanonical` to detect the derived equality at the limit, descends its homotopy,
and uses `htransition` and Mathlib's filtered-colimit equality criterion.
Surjectivity descends a chain representative and applies `hcanonical`.

Updated the item's DAG proof, proof dependencies, and proof origin to this route.
Added two intermediate modules and nodes. Compilation of all three modules is
clean. The first-worker delivery dry run passed; the independent second reading is recorded below.

## Proved and sorry left

Closed: `CochainComplex.affine_perfect_hom_colimit`
(node `lem-pc-affine-perfect-hom-colimit`). No `sorry` remains in the item's module.

Added and left:
- `CochainComplex.affine_perfect_chainMap_descent`, in
  `Sheaf.Algebra.Homology.AffinePerfectChainMapDescent`,
  node `lem-pc-affine-perfect-chain-map-descent`.
- `CochainComplex.affine_perfect_homotopy_descent`, in
  `Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent`,
  node `lem-pc-affine-perfect-homotopy-descent`.

This is a decomposition: one upper hole closed and two strictly smaller holes
added, giving net minus one by the hole ledger before effects of pruning.
Neither intermediate mentions `H`, `ident`, `c`, `e`, the derived category, or the
colimit comparison's bijectivity. The chain-map result concerns existence of a
representative; the homotopy result concerns equality at a later stage.

## No longer needed

Removed these direct proof imports:
- `Sheaf.Paper.AffineProjectiveComplexDerivedHom`, node
  `lem-sc-affine-projective-complex-derived-hom`.
- `Sheaf.Algebra.Homology.RhomGlobalSections`, node
  `lem-pur-rhom-global-sections`.
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`, node
  `lem-pc-module-bounded-flat-kflat`.
- `Sheaf.Algebra.FinitePresentationColimit`, node
  `lem-pc-fp-module-map-descent-affine`.

The first three modules/nodes are no longer needed on this proof branch. The
finite-presentation module/node remains needed through both new intermediate
modules, so removal of its direct import does not claim to prune it from the closure.
The new route uses the existing Mathlib leaf `lem-pc-ring-derived-map-representative`
instead of either one-point sheaf derived-Hom statement. No unit realization is
bypassed: `dag/units/sk-thm-picard-semicon.json` realizes neither these tool lemmas
nor this auxiliary affine calculation as a fixed unit statement or proof step.
Other targets may still need these pruned modules; no global closure count is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's derived-internal-Hom and one-point sheaf detour was unnecessary for the
already fixed termwise complexes in this statement. Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective` supplies chain representatives and
homotopy detection directly. Projectivity after scalar extension follows from the
extension/restriction adjunction; boundedness follows by preservation of zero terms.

The existing finite-presentation descent theorem assumes a `PartialOrder`, whereas
the item assumes a `Preorder`. The new statements retain the item's full generality.
Their proofs explain the reduction by the posetal reflection of the index preorder,
transporting the ring diagram and colimit across the equivalence, or using the same
finite-presentation matrix proof with the general filtered-ring elementwise criterion.
No existing statement or definition was changed.

The local literature copy is absent; the source read was the official Stacks page
https://stacks.math.columbia.edu/tag/09RE, affine case (1), especially its rewrite as
homotopy classes and its finite-presentation calculation. The new proofs expand this
calculation into descent of finite component maps and finite equations. LeanSearch
and the requested Homotopy Loogle query were unavailable; successful LeanFinder and
Mathlib source searches found no chain-map or homotopy descent theorem. The whole
blueprint was searched with `blueprint_refs.py search homotopy` and `search 'chain map'`;
no matching descent statement was found.

## New nodes

`lem-pc-affine-perfect-chain-map-descent` states descent of a chain map itself,
without derived-category localization. Its proof first descends finitely many
components, then detects the finitely many chain equations at a later stage.

`lem-pc-affine-perfect-homotopy-descent` states eventual homotopy of two stage maps,
without any arbitrary diagram or cocone. Its proof descends finitely many
components of a degree-minus-one homotopy, then detects its finitely many equations.
Both have source and full proof docstrings, exact Lean signatures in their node
records, and the searches actually performed. No change record is needed.

Edge cases checked mathematically before finalizing the statements: a zero source
or target gives the zero map and zero homotopy; an empty support interval gives a
zero source; a constant one-stage system gives the original representatives;
zero rings cause no nontriviality requirement; mutually comparable distinct
indices give ring isomorphisms and are handled by the preorder transport. Bounds
are used only for finite support, so no additional lower/upper inequalities or
nonempty support assumptions are needed.


## Second reading by G1

1. **Public interfaces unchanged — pass.** Read the repository/sandbox diff of
   `AffinePerfectHomColimit.lean` in full and compared the bytes from its existing
   theorem name through the conclusion before `:= by`: identical. All seven
   existing public imports are identical. Changes are proof-only imports, three
   private proved helpers, the proof, and its explanatory docstring. No existing
   definition or other module is adapted; no change record is required. The two
   added declarations are in their own new modules.

2. **Kernel checks and holes — pass as a decomposition.** Compiled all three
   modules in import order with `lcompile.py --all`: clean, approximately 2, 2,
   and 3.4 seconds. A temporary scratch copy with `#print axioms` checked all three
   private helpers, the existing theorem, and both new theorems. Each helper uses
   only `propext`, `Classical.choice`, and `Quot.sound`. The existing theorem and
   the two split statements additionally use `sorryAx`, as reported; this is not
   an axiom-free completion of the original item. The only two textual holes are
   the public named descent theorems. No definition, arbitrary data witness,
   axiom declaration, unsafe/opaque implementation, or kernel bypass was added.
   Removed the scratch copy after checking it.

3. **Split statements, source, and search — pass.** Read Stacks Tags
   [09RE](https://stacks.math.columbia.edu/tag/09RE), affine case (1), and
   [05N7](https://stacks.math.columbia.edu/tag/05N7), clauses (2) and (3), alongside
   both complete Lean statements, their proof docstrings and JSON nodes.
   Chain-map descent uses finitely many maps from the finite support of E₀,
   followed by equality detection for the chain equations. Homotopy descent uses
   finitely many degree-minus-one maps, followed by equality detection for the
   homotopy equations. Scalar extension preserves finite presentation of stage
   terms, so equality detection applies after every enlargement. Neither statement
   contains derived categories or the arbitrary H/ident/c/e presentation, and
   neither restates the original bijectivity. Tested zero source/target, empty
   support (a > b), one-stage constant systems, zero rings, and preorders with
   distinct mutually comparable indices. A zero source makes all relevant maps
   and equations zero, including equations adjacent to the support boundary.
   The specified i₀ ensures nonemptiness. Mutual comparability gives inverse ring
   isomorphisms, so passage to the posetal reflection justifies the use of the
   partial-order finite-presentation statement without silently adding antisymmetry.
   Repeated searches with different wording: LeanFinder query “Morphisms of finite
   complexes of finitely presented modules and null homotopies spread out along
   directed colimits of commutative rings” returned localization and K-projective
   null-homotopy lemmas, none giving descent; Loogle `Homotopy, ModuleCat` returned
   zero hits. The grep query for spreading/descent/colimits with homotopy/chain/
   complex returned no matching algebraic descent theorem. Read the related
   `AffinePerfectColimitDescent` and `AffineDifferentialColimitDescent`: they descend
   objects and differentials, respectively, and supply neither maps between the
   fixed base changes nor homotopies. Searches in both Lean roots and the upstream
   checkout found no replacement. Neither split theorem can be closed in a few
   minutes with the available component-descent API; both remain explicitly open.

4. **Top-down proof, imports, pruning and unit route — pass.** Read Mathlib's
   `IsKProjective.Qh_map_bijective` and categorical/module projectivity instances.
   The extension/restriction adjunction supplies projective extended terms, and
   preservation of zero objects supplies the same upper bound. The two quotient
   helpers genuinely construct representatives and detect homotopy; neither
   assumes a derived full-faithfulness result for the ring colimit. Injectivity
   puts the two colimit elements at one common stage, uses hcanonical to obtain
   equality of extended representatives, descends its homotopy, and uses
   htransition to obtain equality in H at a later stage. Surjectivity descends
   an actual chain representative and uses hcanonical. New proof imports are
   private; Homotopy is public in the new homotopy module because its statement
   needs it. FinitePresentationColimit is kept privately in the two open modules
   for their stated dependency. `No longer needed` lists all four removed old
   proof dependencies, accurately distinguishing direct-import removal from
   closure pruning. Read `dag/units/sk-thm-picard-semicon.json`: its realized
   statement and sole realized proof step are empty lists, so this auxiliary
   route bypasses no fixed unit realization. No shorter available proof was found.

5. **DAG agrees with Lean — pass.** Parsed the existing node comparison: only
   proof, proof_deps and proof_origin change (JSON key reordering is immaterial).
   The Mathlib leaf `lem-pc-ring-derived-map-representative` states the bounded
   projective localization bijection actually used. Its two new dependencies
   correspond exactly to the two calls in the Lean proof. Both new nodes have
   the correct chapter/unit, source, self-contained statement, exact flattened
   Lean signature, proof steps/dependency union, creation metadata, blueprint
   origin and recorded searches (including honestly unavailable services).
   The new proof steps use the map/equality clauses of the existing
   finite-presentation node, not undocumented data from its proof.

Second-reading changes: added the missing blueprint node reference to each new
module docstring; clarified the obsolete pending-review sentence in this report;
added this independent review. No proof or statement repair was needed. Accounting
remains one original hole closed and two lower holes added, a decomposition with
net minus one before pruning, not a completed proof of the original theorem.
