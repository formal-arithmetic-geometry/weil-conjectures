## What changed

Proved AlgebraicGeometry.koszulChain_restriction_formula without changing its signature or
existing docstrings. Added proof imports of
Sheaf.AlgebraicGeometry.KoszulOpenHomChainEvaluation and
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive.
The existing chain-evaluation theorem supplies the fraction comparison and naturality.
A proved private helper upgrades its natural equivalences to additive equivalences via
binary biproducts. The proof then identifies the adjunction transpose with g using hs,
identifies the cycle class using hz, transports along eF, and uses naturality of the
inverse localization/homology comparison twice. Updated the existing DAG proof route.
The unit record has no realized statement or step assigned to this node; no unit route changes.

## Proved and sorry left

Closed the sole original hole: AlgebraicGeometry.koszulChain_restriction_formula
(node lem-sc-koszul-chain-restriction-formula). No sorry remains in the delivered module;
no holes were added or split off. The imported existing theorem
AlgebraicGeometry.koszulOpenHom_chain_evaluation
(node lem-sc-koszul-open-hom-chain-evaluation) remains a dependency with sorry in its
existing module; it supplies the geometric evaluation comparison. The private helper
naturalEquiv_add is fully proved. This delivery proves the assigned theorem from existing
statements, rather than closing the whole transitive proof dependency tree.

## No longer needed

Removed direct proof imports:
- Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology
  (lem-pc-derived-structure-sheaf-hom-hypercohomology).
- Sheaf.Paper.AffinePerfectKoszulPrincipalUnitIso
  (lem-sc-affine-perfect-koszul-principal-unit-iso).

These two nodes are no longer direct proof dependencies of this item. The structure-sheaf
hypercohomology result is still imported transitively by chain evaluation, so this is not
an assertion that it is globally unreachable. The principal-unit-iso theorem is not
used by this proof. KoszulCechComparisonConstruction and KoszulOpenSystem remain needed
for the statement and its constructions. KoszulOpenHomChainRepresentatives supplies the
explicit transpose and stage-class definitions, but its chain-representability theorem
is not used. No extra imports remain unused.

## Where the brief, the DAG or earlier work was wrong

The original plan did not point to the existing
AlgebraicGeometry.koszulOpenHom_chain_evaluation theorem, which already packages the
geometric fraction comparison. Its equivalences are ordinary equivalences, whereas the
assigned conclusion requires additive equivalences. Naturality and additivity of the
functors imply additivity by a binary-biproduct argument; no interface repair is necessary.
LeanFinder returned generic comparison results, Loogle confirmed adjunction tools, and
local searches found the existing chain-evaluation theorem. The import-direction check
accepts its use. No definitions, public signatures, or other modules were changed.

## Second reading by D2

1. **Visible interface: pass.** Read the complete delivered module and compared it with
   the repository module using diff and the declaration parser. The full signature of
   AlgebraicGeometry.koszulChain_restriction_formula, from `theorem` through its final
   conclusion, is byte-for-byte identical. Existing docstrings and the sole public import
   are unchanged. The only added declaration is the fully proved private naturalEquiv_add;
   there are no changed definitions, new public signatures, or change records needed.

2. **Proof and axioms: pass relative to existing open dependencies.** Compiled the delivered
   file cleanly through lcompile.py (46.8 seconds). A scratch copy with explicit
   `#print axioms` compiled in 54.0 seconds: naturalEquiv_add uses only propext,
   Classical.choice and Quot.sound; koszulChain_restriction_formula uses those three and
   sorryAx from existing open dependencies, including koszulOpenHom_chain_evaluation.
   Scanned the source: no sorry, axiom, unsafe, opaque, implemented_by, extern or manually
   written sorryAx. There are no new definitions or arbitrary existential data witnesses
   stored in definitions. Every Lean line meets the 100-character limit.

3. **Split statements: pass, none introduced.** No new public statement, node, or hole is
   split off. Read the private helper: the paired morphism into R(E biproduct E) projects
   to psi and psi'; naturality for fst, snd and their sum proves the required addition
   law, using exactly the declared additive functor and biproduct hypotheses. It needs
   neither faithfulness nor a nonzero object. The zero morphism/object cases obey the
   same identities. The target proof adds no nonempty-cover or nonzero-ring hypothesis:
   r=0, the zero ring, F=0 and g=0 remain covered by the unchanged statement and the
   existing chain-evaluation premise. Loogle search for NatTrans and Functor.Additive
   returned zero hits; alternate local searches for preadditive Yoneda, naturality and
   additive equivalences, plus searches in Sheaf and the upstream checkout, found no
   shorter exact replacement for this helper or the target. No new geometric assertion
   has been hidden in the helper.

4. **Route and pruning: pass.** Read koszulOpenHom_chain_evaluation in full: its naturality
   clause applies to eF.hom, and its chain clause applies to t=T.map g followed by s.hom.
   The adjunction-counit identity uses precisely hs to recover g. Injectivity of iCycles
   uses precisely hz to recover its homology class. The two inverse-homology naturality
   equations apply to the stage iso inverse and the colimit leg, giving the displayed
   beta without changing its order or normalization. The existing comparison-square
   theorem instead needs chain representability and supplies only ordinary equivalences;
   it is not a shorter route here. The old two unused direct dependency imports and their
   node IDs are both listed in No longer needed; no globally unreachable module is
   claimed. The public construction import serves the original signature; chain
   evaluation is invoked in the proof. Tested removing the Additive import in a scratch
   copy: compilation fails at b' because (G composed with H).Additive cannot be inferred,
   confirming that proof import is needed. Read dag/units/sk-thm-picard-duality.json:
   realized.statement and its only realized step are empty, so this route bypasses no
   assigned unit statement or step.

5. **DAG agreement: pass after clarification.** The node's unchanged statement matches
   all ring, derived-category, quasi-coherence, counit, cycle and augmentation hypotheses
   of Lean and its additive conclusion. Only proof, proof_deps and proof_origin differ
   from the original node. proof_deps is exactly the union of the step citations. The
   chain-representatives citation concerns the concrete definitions koszulHomChainClass,
   koszulOpenHomTranspose and koszulOpenHomStageClass in that node's module; its open
   theorem koszulOpenHom_chain_representatives is not used. The retained open-system and
   comparison-construction nodes supply the constructions actually appearing in Lean.
   The two removed old proof-dependency nodes are reported completely.

Changed only the second DAG proof step to make its definition-only use of the
chain-representatives node explicit, and appended this independent review. No Lean
proof repair was required. Net assigned holes closed: one; holes added: zero.
