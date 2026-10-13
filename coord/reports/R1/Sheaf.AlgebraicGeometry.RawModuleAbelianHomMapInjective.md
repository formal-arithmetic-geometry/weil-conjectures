## What changed

Replaced the sole sorry in `AlgebraicGeometry.Etale.rawModuleAbelianHomMap_injective`
with a resolution-comparison reduction followed by cancellation of the explicit
coefficient isomorphism. The original signature, public imports, and docstring are unchanged.
The three added proof imports expose no new interface to importers.

The reduction isolates the underived map on free-source Hom and a general comparison
of derived Hom along an exact functor whose images of injectives are acyclic for
the chosen source. These are different parts of the original argument, rather than
copies of the original injectivity assertion. The underived assertion concerns all
coefficient sheaves and no derived category. The general assertion assumes both
termwise Hom bijectivity and source acyclicity, and is independent of schemes,
rings, inverse image, and free represented sheaves.

The third new module, `Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic`, is proved.
Its private constructions explicitly identify additive Hom with evaluation by
adjunctions. Applying rightDerived to the two inverse natural transformations
transports the existing evaluation-acyclicity result to the required source.
It reuses proved private constructions through proof-only `import all` of
`RawRestrictedHomotopySectionsIso` and `ModuleAbelianDerivedDirectImageComparison`.
No object is chosen from an unproved existence theorem.

Sources read: Stacks https://stacks.math.columbia.edu/tag/03FD (both proof paragraphs),
https://stacks.math.columbia.edu/tag/015E (the canonical acyclic-complex comparison),
and Tags 03D3 and 03D7. The relevant library signatures and implementations were read.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle and direct rg
found the injective-resolution, free-source and acyclic-resolution infrastructure,
but no theorem identifying this explicit scalar comparison.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.rawModuleAbelianHomMap_injective`
(node `lem-sbc-raw-module-abelian-hom-map-injective`). Its module has no remaining sorry.

Proved the new theorem `AlgebraicGeometry.Etale.rawModuleFreeSource_acyclic`
(node `lem-sbc-raw-module-free-source-acyclic`). It contains no direct sorry.

Added exactly two remaining holes:

- `AlgebraicGeometry.Etale.rawModuleFreeSourceHom_bijective`
  (`lem-sbc-raw-module-free-source-hom-bijective`). The remaining work is to verify
  the canonical pullback unit factorization and free-generator evaluation under
  the two underived adjunctions.
- `CategoryTheory.derivedSourceComparison_injective`
  (`lem-sbc-derived-source-comparison-injective`). The remaining work is to formalize
  the augmentation-compatible acyclic-resolution computation and its cocycle
  formula for this general exact-functor source comparison.

This is a decomposition, not a sorry-free proof of the original theorem: one old
hole closed and two new holes added, for net minus one direct hole before any
closure/pruning effects. All pre-existing lower holes remain with their holders.
The existing private evaluation-acyclicity helper is recorded by a new node, with
no new Lean declaration or hole.

Edge cases checked mathematically: degree zero uses the same injective-resolution
computation, with no negative boundaries; zero coefficients and empty represented
pullbacks give zero section groups. The generic comparison is valid for zero
objects and arbitrary exact additive functors meeting the two stated conditions.
No injectivity of a forgotten module sheaf is assumed. No flatness, properness,
separation, compactness, torsion or nonzero-ring assumption was added.

## No longer needed

No original import was removed: the public import of `RawModuleAbelianHomMap` is
needed by the unchanged statement, and all added imports occur in the proof.
No unused transitive module is claimed globally pruned.

The old direct proof dependency `lem-weil-pbc-injective-module-abelian-acyclic`
(`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`) is replaced on this node
by the source-Hom, source-acyclicity and general-resolution statements. Its recorded
Lean signature only handles rings in Type u (lifted to u+1), whereas this item
permits arbitrary rings in Type (u+1). The already proved evaluation helper supplies
the required universe-correct result. This is a change to this node's proof route;
other users may still need the old module.

## Where the brief, the DAG or earlier work was wrong

The planned acyclicity dependency cannot be applied directly to every coefficient
ring allowed by this item's statement: its Lean declaration takes R : Type u and
ULift R. This is not a counterexample to the mathematical statement. The existing
`moduleAbelianForget_injective_evaluation_acyclic` already handles arbitrary
Λ : Type (u+1), via the universe-correct presheaf cocycle lifting argument.
A new node records that existing helper rather than duplicating its proof or
changing an interface. The common-universe generic ringed-site acyclicity theorem
likewise cannot be instantiated directly here.

The unit record `sk-lem-failure-field` has no realized nodes in its statement or
steps. The delivery retains the specified free-source/acyclic-resolution route.
No target statement, existing definition, or dependency module was adapted.

## New nodes

`lem-sbc-derived-source-comparison-injective` records the general exact-functor
resolution comparison in `Sheaf.CategoryTheory.DerivedSourceComparisonInjective`.
It is one of the two remaining proof items.

`lem-sbc-raw-module-free-source-hom-bijective` records the precise underived
free-generator map in `Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective`.
It is the other remaining proof item.

`lem-sbc-raw-module-free-source-acyclic` records the proved source-acyclicity theorem
in `Sheaf.AlgebraicGeometry.RawModuleFreeSourceAcyclic`, including its explicit
natural Hom/evaluation comparison and derived transport.

`lem-sbc-injective-module-forget-evaluation-acyclic` records the existing private
proved helper in `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`.
Its source file is unchanged; its exact declaration is used through `import all`.
Recording it makes the DAG cite the actual acyclicity statement being used,
rather than the final derived-direct-image theorem whose proof contains it.

No change records are needed because no existing interface changed.

## Second reading by R1

1. Compared the sole existing delivered module with the repository using diff.
   The signature of `rawModuleAbelianHomMap_injective`, its visibility, docstring,
   and existing public import are byte-for-byte unchanged. Only its proof and
   three plain proof imports changed. The other three Lean files and four node
   files are new; no existing definition or dependency module is adapted.
   Verdict: no accidental interface change and no change record required.

2. Compiled all four delivered modules in import order through lcompile.py;
   all compiled without errors or warnings. Inspected every declaration for
   forbidden constructs and data holes. The only direct sorries are the two
   public named theorems reported above, each with a complete prose proof and
   matching node. A scratch copy with four `#print axioms` commands shows only
   propext, Classical.choice and Quot.sound for `rawModuleFreeSource_acyclic`;
   the original theorem and the two open lemmas additionally use sorryAx.
   In particular the new acyclicity proof is fully closed, including its
   existing private helper, rather than merely hiding a lower hole.
   Verdict: valid decomposition; one original hole closed, two holes added.

3. Read Stacks Tags [03FD](https://stacks.math.columbia.edu/tag/03FD),
   [015E](https://stacks.math.columbia.edu/tag/015E),
   [03D3](https://stacks.math.columbia.edu/tag/03D3), and
   [03D7](https://stacks.math.columbia.edu/tag/03D7), and the actual definitions
   of freeMap and pullbackIso. The underived lemma's map is the specified
   generator map, not an arbitrary Hom equivalence. Both Hom sets identify
   with sections by the two pullback adjunctions and the free represented
   adjunctions; compatibility of the Kan/sheafification units is the remaining
   concrete obligation. The generic lemma assumes exactness, Hom bijectivity
   on injectives and Hom(B,-)-acyclicity, so an injective resolution in C maps
   to an acyclic resolution in D. Its termwise comparison is additive and
   commutes with differentials. Tag 015E and augmentation compatibility then
   identify its cohomology map with the displayed derived morphism. Neither
   lemma restates the item's hypotheses and conclusion. Checked q=0 (no
   negative boundaries), zero objects, the zero ring, and empty represented
   objects; no excluded case or missing injectivity-preservation hypothesis.
   Independent LeanFinder search for an acyclic-resolution exact-functor Ext
   comparison found mapExactFunctor and extMk_hom, not this theorem; Loogle
   and rg over Mathlib and the library found no direct replacement. Existing
   moduleAbelianUpperStarComparison only gives its adjunction mate and does
   not identify that mate with this fixed Kan/sheafification comparison.
   Verdict: both remaining statements are true, needed, and proper parts of
   the reduction; neither can be closed by applying a found theorem alone.

4. Read the raw bundled map and checked its factorization c ≫ (D+(V)(x) ≫ b).
   The proof applies the general comparison to the exact forgetful functor,
   verifies hhom with the underived lemma and hac with the closed acyclicity
   lemma, then cancels the invertible coefficient comparison b. Read
   representedEquiv, representedEquiv_apply and the evaluation-acyclicity
   helper: the new acyclicity module reuses actual constructions, proves
   additivity and naturality, and transports zero along the derived iso.
   All three added item imports are used and private helpers are accessed
   through plain import all; the new public imports provide statement notions.
   No original import is redundant. The old direct acyclicity node is fully
   listed under No longer needed, without claiming its module is globally
   pruned. Read sk-lem-failure-field.realized (empty statement and step lists);
   the free-source/acyclic-resolution route is preserved. Verdict: route and
   pruning report agree with the proof.

5. Compared every new node's Lean statement with its declaration and checked
   source, created, blueprint, chapter, unit, search, and lean fields. The
   existing node's changed proof_deps are exactly the three lemmas applied by
   the new proof; its final cancellation is elementary. The generic node uses
   the Ext/injective-resolution and Leray-acyclicity statements; the existing
   private evaluation helper is separately recorded with existing=true and
   adds no Lean declaration. Checked those cited statements against their
   actual resolution and Cech-vanishing uses. Verdict: the nodes match the
   delivered argument, after the small prose correction below.

Changed in this reading: clarified the generic node's source and target Hom
categories as D⁺(C) and D⁺(D), and added Tag 015E to the generic module and
lemma source citations. No Lean statement or proof was changed. The scratch
axiom-check copy was removed before delivery.
