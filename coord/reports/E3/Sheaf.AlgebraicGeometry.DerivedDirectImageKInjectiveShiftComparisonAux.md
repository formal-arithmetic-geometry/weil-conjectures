## What changed

Proved `AlgebraicGeometry.RingedSpace.derivedModuleDirectImageKInjectiveIso_shift_aux`
in `Sheaf.AlgebraicGeometry.DerivedDirectImageKInjectiveShiftComparisonAux`, with its
original signature and visibility. All three imports remain necessary.

The proof uses four private, fully proved helpers. `unit_commShift` expresses the
restricted right-derived unit using the K-injective equivalence unit and the
comparison used to transport shifts. Naturality and the equivalence triangle
identity prove that expression equals the restricted unit. `unit_commShift_all`
extends compatibility using K-injective resolutions and
`NatTrans.CommShift.of_whiskerLeft`. `comparison` constructs the complex-level
comparison, including associators to align the intermediate shift structures;
`comparison_app` identifies its K-injective component with the inverse comparison
isomorphism. The public theorem applies shift compatibility and cancels the
comparison and localized shift isomorphisms.

The node's existing proof route is retained: transport the right-derived unit
through the K-injective equivalence, then use its shift compatibility. The unit
record `sk-thm-picard-semicon` has no realized nodes that this proof bypasses.
No definitions or statements outside the item were changed.

Source read: Stacks Project Tag 079V, construction of unbounded right-derived
functors and their computation by K-injectives, at
https://stacks.math.columbia.edu/tag/079V (the literature TeX checkout is absent
on this machine). The concrete transport and cancellation argument is checked
against the definitions in the imported Lean modules.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.RingedSpace.derivedModuleDirectImageKInjectiveIso_shift_aux`
(node `lem-pc-direct-image-kinjective-comparison-shift-aux`).

No sorry remains in the item. No holes were added or split off. The private
helpers have complete proofs, and the private comparison is a concrete
composition of existing natural transformations, with no chosen witnesses.
Existing dependency holes remain outside this delivery.

## No longer needed

`def-pc-derived-mayer-vietoris-canonical-data`, the only old `proof_deps` entry,
is not used by this proof and is removed from the node's proof dependencies.
Its module was not directly imported by this item, so no Lean import or
whole module is pruned. `DerivedDirectImageSplitTriangle` supplies the two comparison definitions;
`RightDerivedFunctor.Triangulated` supplies the transported shift structure and
K-injective equivalence; `HomotopyCategory.Shift` supplies the shift-compatibility
API, including `NatTrans.CommShift.of_whiskerLeft`. No imports or whole modules
were pruned; the unused canonical-data proof-dependency edge was removed. No new proof-dependency imports were added.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error found. The old node cited Mayer--Vietoris
canonical data although no declaration from it is used; its proof metadata is
corrected to name the right-derived triangulated construction, ringed-space
direct-image construction, and comparison definitions in the termwise-split
triangle module. The DAG's phrase about unit naturality needs
the shift compatibility of the unit for the *transported* shift structure; this
compatibility is proved here rather than assumed. Explicit associators are
needed because the shift structures on differently parenthesized composite
functors are not definitionally equal, even though their underlying functors are.

## Second reading by E3

1. Compared the delivered module with the repository using `diff -u` and
   checked the public theorem signature byte for byte, through `:= by`.
   It retains the universes u and w, both derived-category instances, arbitrary
   ringed-space morphism g, arbitrary K-injective K, and exactly the inverse-Q
   shift/comparison equality. Imports, visibility, and existing definitions are
   unchanged. The four additions are private helpers; none changes public data.
   Verdict: pass.
2. Compiled the item locally with `lcompile.py`: clean, 25.5 seconds.
   Compiled a scratch copy with `#print axioms` for all four helpers and the
   public theorem: each uses only `propext`, `Classical.choice`, `Quot.sound`;
   even `sorryAx` is absent. No forbidden declaration or sorry occurs in the
   delivered file. `comparison` is the explicit composition of whiskerings and
   associators, not a selected existence witness. Resolution witnesses are used
   only in a proposition, from the proved resolution API. Verdict: pass.
3. No statements were split off and no public statements were added. Checked
   the helper transport equation against the definition of
   `rightDerivedFunctorIsoKInjectives`: its counit cancels the mapped equivalence
   unit by `functor_unitIso_comp`. Checked `of_whiskerLeft`'s exact requirement:
   only the target functor must invert the chosen resolution map, which follows
   from localization and preservation of isomorphisms. Thus no preservation of
   quasi-isomorphisms by the original additive functor is assumed. The argument
   also applies to the zero complex and identity morphism, with no nonzero or
   boundedness condition. Verdict: pass.
4. Read Stacks Tag 079V online, especially the construction preceding 20.28.1,
   and the imported comparison definitions and transported shift instances.
   The component cancellation has the correct inverse orientations. Searched
   using `msearch.py ... loogle CategoryTheory.Functor.rightDerivedFunctorUnit`
   (no indexed result), and `rg` for unit/shift compatibility in Sheaf and the
   upstream derived-functor sources. Similar general proofs in
   `PinnedDerivedAdjunctionShifts`, `RestrictedDerivedSectionsShiftTransport`,
   and the parent shift-comparison module are private; the parent imports this
   item. The upstream public adjunction lemma requires an exact left adjoint
   and compatibility of a selected derived adjunction, unavailable from this
   item's signature. No shorter reusable public proof was found. The plain
   HomotopyCategory.Shift import supplies compatibility of the homotopy
   factorization; the Triangulated public import supplies the actual derived
   shift instance appearing in the statement; SplitTriangle supplies both
   comparison definitions. All imports are needed. Read the unit record:
   `realized.statement` and its sole `realized.steps` entry are empty. No unit
   realization is bypassed. The only obsolete old proof dependency is listed
   above; no whole module is claimed pruned. Verdict: pass after metadata repair.
5. The old node's canonical Mayer--Vietoris data dependency did not describe
   this Lean proof. Replaced its proof steps, proof dependencies, and proof
   origin with the actual restricted-unit transport, resolution detection,
   complex-level comparison and cancellation argument. The comparison
   definitions are carried by the termwise-split triangle node; its triangle
   theorem is not invoked. No statement, statement dependency, Lean signature,
   source, unit, or maintainer field was changed. No new nodes are needed.
   Verdict: pass after repair.

Second reading changed only the node's proof metadata and this report, including
its obsolete-dependency accounting. The Lean proof was left unchanged.
