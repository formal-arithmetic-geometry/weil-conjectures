## What changed

Completed `AlgebraicGeometry.ProEtale.profinite_point_pullback_module_comparison` in
`Sheaf.Paper.ProfinitePointPullback`. Exactness uses the existing instances. The identity and
composition equations follow from the scalar-extension unit equation and uniqueness of adjunction
mates after forgetting module actions. All supporting lemmas are private and proved in this module;
two existing underlying-map helpers were moved earlier so the new proof can use them.

The inherited attempt had moved public definitions into a support module and introduced two
unproved interface modules. Both interfaces are now proved, their arguments are incorporated as
private helpers, and those three unlanded modules and their three unlanded nodes are removed from
the delivery. Original public statements, definitions, visibility and docstrings are retained.
Four existing derived-category helper calls are qualified with `CategoryTheory.Functor`.
The original DAG node records the completed proof route; its proof dependencies are unchanged.
Second reading also removed three redundant direct public imports already re-exported by the
retained `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.profinite_point_pullback_module_comparison`
(node `lem-weil-pbc-profinite-point-pullback`).

One original hole closed; zero holes added; no `sorry` remains in the item module or delivery.
The inherited identity and composition split-offs have complete proofs and are now private helpers,
`moduleIdentity_forget` and `moduleComposition_forget`; they are not new public obligations.

## No longer needed

Removed the unused proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
The existing tensor-product statement dependency `def-pur-sheaf-tensor-product` is retained.
No original node or proof dependency is pruned. Second reading additionally removed these
redundant direct imports, all still public through `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`, and
`Sheaf.CategoryTheory.RingedSiteModules`.
The remaining six direct imports supply statement/definition data or explicitly used proof lemmas.
Change record: `coord/changes/ProfinitePointPullback-import-pruning-D2.md`.

Removed these unlanded modules from the inherited sandbox:
`Sheaf.Paper.ProfinitePointPullbackBase`,
`Sheaf.Paper.ProfinitePointModuleIdentityComparison`, and
`Sheaf.Paper.ProfinitePointModuleCompositionComparison`.
Their unlanded nodes ending in `module-direct-image-identity-underlying`,
`module-identity-comparison`, and `module-composition-comparison` are unnecessary.

## Where the brief, the DAG or earlier work was wrong

The previous attempt left both compatibility equations open and unnecessarily relocated public
constructions to support the split. The current proof closes both equations without that relocation.
The node's previous proof text said this compatibility remained open; its module step now describes
the completed proof. Four unqualified derived-category helper calls required namespace qualification
in the current compile environment. No mathematical statement or definition was corrected.

A direct concrete rewrite in the composition calculation spent most of Lean's heartbeat budget
unfolding module pullback presentations. An abstract raw-morphism lemma, `comparisonFromUnits`,
proves the same diagram by the adjunction hom equivalence without unfolding these presentations.
No compile limit was raised and no file was split for compilation.


## Second reading by D2

1. **Interface: pass.** Compared the entire delivered module with the shared repository using
   `diff` and the project declaration parser. All 64 existing declaration signatures match byte
   for byte; definition bodies and docstrings also match. Visibility is unchanged. The six added
   lemmas are private and proved. The only public-import edits remove three redundant imports
   already publicly exported by the retained `ProEtaleInverseImage`; the change record documents
   every downstream user. No other module is delivered or adapted.
2. **Proof and axioms: pass.** The original sandbox compiled cleanly with `lcompile.py` in 47.5 s.
   A scratch copy of the cleaned module, with `#print axioms` for all 28 public declarations,
   compiled cleanly in 52.4 s. Every axiom list contains only `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. No `sorry`, axiom declaration, unsafe definition, opaque
   declaration or foreign implementation occurs in the delivered module. The chosen module
   direct-image identity is determined uniquely by its underlying map; no arbitrary unproved
   witness supplies data.
3. **Split statements: pass, none.** One existing hole is closed and no holes or public statements
   are added. Read all six new private lemmas. The unit comparison is exactly the scalar-extension
   `leftAdjointUniq` unit equation; identity and composition then follow by injectivity of the
   abelian adjunction hom equivalence. The raw comparison lemma requires only the stated
   retraction and unit equations; it does not assume an unstated invertibility or cancellation.
   The argument includes identity morphisms and zero modules/coefficients, with no extra
   nonzero, finiteness or nonempty hypotheses. Repeated searches using Loogle for
   `unit_conjugateEquiv`, LeanFinder for uniqueness from unit equations, and grep of adjunction
   and module-object APIs confirm the standard lemmas already used; no shorter complete
   module comparison was found. No new nodes are needed for these elementary private steps.
4. **Route and pruning: pass after import cleanup.** The proof opens the sole remaining hole,
   uses the existing exactness instances and Mathlib adjunction uniqueness, and leaves no lower
   obligation. Read the unit `sk-thm-properbasechange` and its `realized` fields: this coefficient
   comparison does not replace any of its three steps. Every original `proof_deps` remains used
   by the full module's site, tensor/module, mate or derived-coherence argument. The unused
   `TensorProductOfUniverses` proof import and three redundant direct public imports are all
   recorded under `No longer needed`. No unit-route node or module is bypassed.
5. **Nodes: pass.** The sole delivered node retains its statement, statement dependencies,
   Lean interface record, chapter and unit. Only its module-comparison proof paragraph and
   `proof_origin` differ from the repository. The paragraph accurately describes scalar-extension
   unit normalization, mate equations and hom-equivalence injectivity. Its `proof_deps` is exactly
   the union of the steps' `uses`. There are no new nodes or unreported split-offs.

Second-reading changes: removed the three redundant direct public imports, removed an extra blank
line before the completed theorem, documented import pruning in the change record and report,
and added this independent review. The mathematical proofs needed no repair.
