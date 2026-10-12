## What changed

Proved `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections` without changing its signature or visibility. The proof applies the existing abelian criterion to the underlying abelian sheaf, cancels the canonical global-section factors, and uses `isIso_moduleAbelianInverseImageComparison` to identify the forgotten module unit with the abelian unit followed by an isomorphism. Reflection of isomorphisms then gives the module unit and the required global-section map.

Added proof-only imports of `Sheaf.AlgebraicGeometry.EtaleAbelianH0FiniteConnectedCriterion` and `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`. Updated the item's node proof, proof dependencies and origin. No definitions, existing signatures, public imports, or other modules were changed. The final module has no private helpers and no new declarations.

The existing abelian criterion retains the spectral-restriction and Gabber route; the unit's degree-zero route is preserved. Its node and the canonical comparison node belong to `sk-thm-p1`, and are used as tools here in `sk-thm-iff`: both apply to arbitrary coefficient rings and schemes in exactly the universes of this theorem. No alternative degree-zero geometric argument replaces the unit route. The maintainer may record these tool uses.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_of_finite_connected_closed_intersections` (node `lem-weil-pbc-etale-module-h0-finite-connected-criterion`). One original hole closed; zero new holes. No `sorry` remains in the delivered module and none was split off. Both imported comparison/criterion declarations already have complete Lean proofs in the current library; their transitive foundations are unchanged.

The final proof compiled cleanly through `lcompile.py` (8.7 seconds), with the statement unchanged. It covers empty schemes and zero rings using the same adjunction identities, and imposes no finite or torsion condition on the coefficient ring.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion`
- `Sheaf.Topology.SpectralClosedRestriction`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The module's direct proof no longer needs nodes `lem-weil-pbc-qcqs-scheme-spectral`, `lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-fibre-product-points`, `lem-weil-pbc-h0-spectral-closed-restriction`, `lem-weil-pbc-gabber-h0-etale-criterion`, `lem-weil-pbc-etale-inverse-image-algebraic-structures`, or `def-weil-pbc-scheme-conventions` as proof dependencies. The scheme conventions remain a statement dependency. The abelian criterion still reaches its own geometric, spectral and set/abelian comparison dependencies; removing their direct imports here does not claim they disappear from the targets' transitive closure. The definitions of inverse image and the global-section map remain available through the unchanged public import of GlobalSections. No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan suggested extending the set/abelian algebraic-structures comparison to module scalar operations. That extension is unnecessary: the library already supplies the canonical module-to-abelian comparison, including the precise mate determined by the module unit. Merely using the existence of an arbitrary inverse-image isomorphism would not suffice to identify restriction maps; the proof uses the canonical mate and the adjunction identity explicitly.

Searches were run through msearch (LeanFinder, Loogle and grep) and local rg. LeanFinder returned related SheafOfModules results; Loogle without the CategoryTheory prefix reported an unknown identifier; grep located the Kan-extension and sheafification factorization lemmas. Subsequent library/node searches found the exact existing canonical comparison and abelian criterion, so no new node or holed intermediate statement was needed. Source reading: Stacks `etale-cohomology.tex`, `lemma-gabber-h0` and `lemma-h0-topological`, from the locally available literature mirror.

## Second reading by E3

1. Interface preservation: PASS. Read the complete module and its diff against the repository. The existing theorem signature is byte for byte unchanged, including all universes, hypotheses, conclusion and visibility. The original docstrings and public imports are unchanged. There are no other delivered Lean modules, new declarations, definitions or change records.

2. Proof and trust: PASS, relative to the existing open foundations. Independently compiled the delivered module with lcompile.py: exit code 0, no warnings (4.1 seconds). A scratch copy with `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` and transitive `sorryAx` for the item and the existing abelian criterion. The canonical module/abelian comparison uses only the three permitted foundational axioms. Thus this closes the item's own hole, but is not yet an axiom-clean proof of its import closure. There is no `sorry` or forbidden declaration mechanism in the delivered module, and no data is chosen from an unproved existence theorem. Read the cancellation of the global-section factors, the hom-equivalence unit identity, terminal evaluation and reflection of isomorphisms; each proves the displayed canonical map.

3. Split statements: PASS (none). No hole, statement or node was added. The two imported theorems already exist in the library, with exactly the coefficient and scheme universes required here. Checked the empty scheme and zero coefficient ring: the proof uses only identities of adjunctions and reflection of isomorphisms, and makes no nonemptiness or nonzero-ring inference. Independent rg searches found the existing comparison uses in NormalGenericConstant and PrimeCoefficientConstructibilityTransfer; an msearch grep query using reflection, hom-equivalence units and cancellation confirmed the available Mathlib tools. No redundant new intermediate statement is introduced.

4. Route and pruning: PASS. Read both imported proofs, GlobalSections, the original proof dependency list and the realized fields of sk-thm-iff and sk-thm-p1. The abelian criterion retains the spectral restriction and Gabber steps. Reusing this coefficient-independent tool does not bypass either unit's realized statement or steps. The item's two proof-only imports are both used; public imports supply its unchanged interface. The report lists all seven original proof dependencies dropped from the direct proof and all four removed direct imports. No transitive or global module pruning is claimed.

5. DAG agreement: PASS. Compared the delivered node with its repository version: only proof, proof_deps and proof_origin differ. The three proof steps match abelian unit evaluation, canonical comparison and its adjunction identity, then reflection and composition. The union of their uses equals proof_deps, and the Lean record and mathematical statement remain unchanged.

Second-reading changes: added this independent review and explicitly recorded the transitive `sorryAx` found by the axiom check. No Lean or DAG repair was necessary; no additional holes were closed or added.
