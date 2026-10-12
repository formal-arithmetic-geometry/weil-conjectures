## What changed

The original signature and public imports of Sheaf.Paper.ZariskiEtaleResolutionPullbackCocycle
are unchanged. The returned duplicate private declaration `resolutionSectionEquiv_comp` was removed;
the proof now uses local `have` composition identities proved by `rfl`, avoiding a duplicate
of the existing library statement while preserving the same reductions. Its theorem is proved from exact-functor transport of Ext, using two new
proof imports. The proof constructs t via actual adjunction equivalences, transposes b
componentwise into an etale chain map e, proves its counit augmentation and closedness,
and proves t ≫ L(a) ≫ e = c from hsec. Ext associativity and mk₀_comp_extMk finish.
No data is chosen from an unproved existence theorem and no existing definition is changed.

Sheaf.Paper.ZariskiEtalePullbackMapExt proves the identification of the supplied fstar
with precomposition by Ext.mk₀ t after mapExactFunctor. The degree-zero proof uses
identity-generator evaluation; the higher-degree proof uses a cokernel sequence of an
injective embedding, covariant_sequence_exact₁, injective vanishing, and induction.
It needs none of the sorried universal-delta-functor infrastructure.

Sheaf.CategoryTheory.ExactFunctorResolutionCocycle isolates the remaining general
calculation of exact-functor transport on a resolution cocycle. It has no scheme,
site, fstar, generator-section condition or counit; it is strictly one step of the
argument. Its complete natural-language proof is in its docstring and node.
All three modules compile cleanly through lcompile.py in import order.

## Proved and sorry left

Closed the original hole zariski_etale_resolution_pullback_cocycle
(node lem-weil-pbc-zariski-etale-resolution-pullback-cocycle).
The item module has no sorry left.

New theorem zariski_etale_pullback_eq_mapExt is fully proved, with no sorry
(node lem-weil-pbc-zariski-etale-pullback-map-ext).

Added one hole exactFunctor_resolution_cocycle
(node lem-weil-pbc-exact-functor-resolution-cocycle), in its own module.
This delivery is a decomposition: one original hole closed and one lower hole added,
not a complete proof without sorry dependencies. The identification and adjunction
calculations are complete Lean proofs; only the general Ext transport computation remains.

## No longer needed

No original public import was removed: they support the original statement.
No unused proof imports remain. The following planned theorem dependencies are not used:

- lem-weil-pbc-right-derived-universal-delta-functor,
  Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor: replaced by direct dimension shifting.
- lem-weil-pbc-site-cohomology-pullback,
  Sheaf.CategoryTheory.SiteCohomologyPullback: replaced by the proved Ext transport formula.
- lem-weil-pbc-zariski-etale-resolution-homology-independent,
  Sheaf.Paper.ZariskiEtaleResolutionHomologyIndependent: componentwise adjunction transposition
  uses the prescribed b itself, so no comparison with a second chain map is needed.

These are removed from this item's proof_deps; they may remain needed elsewhere.
The injective-resolution and site/cohomology definition nodes remain needed.
No unit statement or realized unit step is bypassed.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared the item module with the repository version and
checked the existing declaration signature and public imports byte for byte. Verdict: unchanged;
the two added modules contain only the new declarations described in this report.

2. **Proof checks.** Compiled all three modules with `lcompile.py`. The item and the pullback
identification compile without `sorry`; the sole remaining `sorry` is the named split theorem
`exactFunctor_resolution_cocycle`. No forbidden declarations or hollow definitions occur. Verdict:
passes, with the documented split hole.

3. **New statement review.** Checked the pullback identification by its degree-zero adjunction
calculation and positive-degree injective-embedding induction, and checked the exact-functor
cocycle statement against the supplied hypotheses and edge cases. Both are true and strictly
more specific than the original target; neither duplicates an existing library declaration.
Verdict: passes.

4. **Pruning and route.** The proof uses the actual adjunction, exact-functor Ext transport,
and the supplied resolution comparison. The three planned universal-delta-functor,
site-pullback, and homology-independence dependencies are absent from the proof and removed
from the item node's `proof_deps`; no unused proof imports remain. Verdict: passes.

5. **DAG and unit agreement.** The item node proof steps and dependencies match the Lean proof,
and each new theorem has a matching node with source, proof, searches, and split status. The
unit's realized route remains in force. Verdict: passes.

Changed only this report section; no Lean statement or definition was altered during second
reading.

## Where the brief, the DAG or earlier work was wrong

The planned dependency signatures do not give the needed cocycle identity: the universal
right-derived theorem concerns rightDerived rather than H', the site pullback statement
characterizes a family without a resolution-cocycle formula, and the independence theorem
compares homology maps without a specified Ext-to-section identification. The new route
avoids that missing bridge by using Mathlib's genuine mapExactFunctor on Ext.

The source tex files were absent locally, so the cited cohomology.tex, derived.tex and
sites-cohomology.tex were fetched into this sandbox's scratchpad and the relevant labeled
sections were read. LeanSearch returned Internal Server Error; it is recorded as unavailable.
Loogle, Lean Finder and grep searches ran and are recorded in searches.jsonl.

Edge cases: degree zero of the characterization is checked separately in Lean, positive
degrees use an injective embedding, and the representative maps are reconstructed by
bijective adjunctions. Empty opens and zero sheaves require no nonemptiness assumptions.
For the remaining general computation, extension by zero introduces no incoming degree-zero
boundary, and preservation of injectives by L is deliberately not assumed or needed.

## New nodes

lem-weil-pbc-zariski-etale-pullback-map-ext: the proved exact-functor formula for the
normalized cohomology pullback, in Sheaf.Paper.ZariskiEtalePullbackMapExt.

lem-weil-pbc-exact-functor-resolution-cocycle: the remaining computation of transported
resolution cocycles, in Sheaf.CategoryTheory.ExactFunctorResolutionCocycle.

No change record is needed: no existing signature, definition, visibility or public
import is changed. There are no forced adaptations.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared `Sheaf.Paper.ZariskiEtaleResolutionPullbackCocycle.lean` with the repository version. The target theorem signature and its public imports are unchanged; the delivery only replaces the proof imports and proof body. The two added theorem statements match their DAG nodes verbatim. Verdict: passes.

2. **Proof checks.** Compiled the item and both added modules with `lcompile.py`; all compile cleanly. The item and `zariski_etale_pullback_eq_mapExt` contain no `sorry`. The sole remaining `sorry` is the named split theorem `exactFunctor_resolution_cocycle`; no forbidden declarations or hollow definitions occur. Verdict: passes with the documented split hole.

3. **New statement review.** The pullback identification is strictly more specific than the target and its induction uses the stated naturality, connecting-map, and degree-zero hypotheses. The exact-functor cocycle theorem is a general one-step reduction with an explicit supplied comparison map and closedness proof, and does not assume preservation of injectives. Both statements are true on degree zero and zero-object edge cases and do not duplicate an existing declaration. Verdict: passes.

4. **Pruning and route.** The proof uses the actual adjunction, exact-functor Ext transport, and the supplied resolution comparison. The old universal-delta-functor, site-pullback, and homology-independence dependencies are absent from the proof and are listed as removed; proof-only imports are plain imports. The unit route remains recorded as `sk-thm-p1`. Verdict: passes.

5. **DAG agreement.** The item node's proof steps and `proof_deps` match the Lean proof, and both new nodes include source, proof, search, split status, and Lean declaration records. Verdict: passes.

Changed only this report section during second reading; no Lean statement or definition was altered.


## Second reading by E2

1. **Interfaces unchanged — passes.** Read the repository/sandbox diff of the item.
   Independently compared the complete existing theorem signature and all public imports
   byte for byte: both are identical. The only added definition is a private, concrete
   composition of sheafification, free-abelian and Yoneda equivalences. No existing
   declaration, definition, visibility, or target statement changes. No change record
   or forced adaptation is required.

2. **Kernel checks — passes with one documented hole.** Independently compiled all three
   modules through lcompile.py in import order. Scratch copies with explicit #print axioms
   show zariski_etale_pullback_eq_mapExt and both private resolutionSectionEquiv definitions
   use only propext, Classical.choice, and Quot.sound. The item theorem and
   exactFunctor_resolution_cocycle additionally use sorryAx. The latter is the sole literal
   sorry in the delivery and is a named theorem, with a source, word proof and node.
   Checked for forbidden declarations and hollow data: none. The data t and e are built
   with actual equivalence inverses, not chosen from an unproved existence statement.
   The original hole closes syntactically, but one lower hole is added: net zero holes,
   a decomposition rather than a complete axiom-clean proof of the original item.

3. **New results and sources — passes.** Read scratchpad derived.tex
   lemma-morphisms-lift and lemma-higher-derived-functors, cohomology.tex
   remark-explain-arrow, and sites-cohomology.tex equation-cohomology-object-site.
   In the proved identification, the degree-zero generator normalization ht and hfstar
   are compared through injective equivalences; unit naturality supplies hn. In the
   successor case the injective embedding/cokernel short exact sequence supplies a
   connecting preimage by covariant_sequence_exact₁ and positive-degree injective
   vanishing. Boundary compatibility and mapExactFunctor_extClass finish the induction.
   No preservation of injectives by L is used. For the remaining generic lemma, exactness
   sends the augmentation of R to a quasi-isomorphism, and he identifies the supplied
   comparison e after localization with f; the mapped cocycle is therefore L(a)e.
   This is only the representative computation: there is no site, section normalization,
   fstar, generator map or adjunction in this lemma, so it does not relabel the item.
   Checked degree zero (no incoming boundary), a=0, the identity functor, and zero
   coefficient objects; none needs an extra hypothesis. The required closedness hc also
   follows from ha and e.comm, as the item proves in hca.
   Repeated searches with different wording through msearch.py grep, Lean Finder and
   Loogle; inspected Mathlib Injective/Ext.lean and DerivedCategory/Ext/Map.lean and
   searched lean/Sheaf and lean/WeilConjectures. extMk_comp_mk₀ handles comparison
   inside one category, not transport by a functor which need not preserve injectives.
   Existing SiteCohomologyPullbackExists constructs a family but does not state its
   identification with an arbitrary supplied fstar. No existing declaration found
   closes the remaining lemma by a short application.

4. **Top-down reduction and pruning — passes.** Followed construction of t, transposition
   of b into e, augmentation he, closedness hca, and generator equality hte. In hte,
   hn' follows from unit naturality and the adjunction inverse identity hbe; applying
   section evaluation and hsec gives equality of the actual cocycles, not only their
   homology classes. The final Ext reassociation, generic transport lemma and
   mk₀_comp_extMk have exactly these input/output types. The report's No longer needed
   lists every old proof dependency omitted by the new proof: universal delta functor,
   site cohomology pullback, and resolution homology independence. Proof-only imports
   are plain imports; new public imports support the new theorem signatures.
   Read dag/units/sk-thm-p1.json realized: this cocycle item and the removed tool nodes
   are not realized statement/step nodes, and its route is unchanged.

5. **DAG agreement — passes.** Compared the existing item JSON with the repository:
   only proof, proof_deps and proof_origin differ. Checked both new nodes' self-contained
   statements, hypotheses, source, steps, recorded searches, creation/blueprint records,
   chapter/unit and Lean records. All three Lean statements occur verbatim in their
   modules, and each proof_deps is exactly the union of its proof steps' uses. The item
   steps match the concrete adjunction calculation and the two imported results.

Second-reading changes: rewrote the item's stale proof docstring to describe the actual
Ext-transport/dimension-shifting route; removed the unused local htc calculation; added
source and blueprint identification to the generic lemma's module docstring; appended
this independent review. No statement, definition, import or DAG field was changed.
