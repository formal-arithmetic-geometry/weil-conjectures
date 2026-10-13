## What changed

Proved `AlgebraicGeometry.exists_leray_spectralSequence` in
`Sheaf.AlgebraicGeometry.LeraySpectralSequence`, preserving its signature, universes,
quasi-coherence hypothesis, visibility, public imports, and existing docstring.

Use `CategoryTheory.Functor.exists_grothendieckSpectralSequence` from the source library
for module direct image followed by module-valued global sections and scalar forgetting.
This existing theorem directly supplies the required natural-number sequence and abutment;
the stronger Cartan–Eilenberg-model interface is unnecessary here. The new DAG attachment
`src-grothendieck-spectral-sequence-nat` records this existing declaration, with no new Lean
module or unproved statement.

The private proved helper `AlgebraicGeometry.derived_forget_iso` computes both derived
functors using one injective resolution. `ShortComplex.mapHomologyIso` commutes the exact
module-to-abelian-group forgetful functor with homology. Use it to convert the existing
injective-pushforward acyclicity theorem at the top open, and to identify each second-page
term. The composite global-sections functors are definitionally equal after forgetting
scalars; derive their identity isomorphism and transport the abutment. Finite-limit
preservation comes from Mathlib instances for pushforward and evaluation.

Updated `pqf-lem-leray`'s proof, proof dependencies and proof origin to this route. Its unit
record has no realized statement or proof steps assigned to this node; its finiteness
statement and proper/quasi-finite step are unaffected.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.exists_leray_spectralSequence`
(node `pqf-lem-leray`). The module now contains no `sorry`. Added zero holes and split off
zero holes. The private helper `AlgebraicGeometry.derived_forget_iso` is fully proved.

This is a proof from the existing generic spectral-sequence and injective-pushforward
acyclicity declarations. It does not claim their entire dependency closures are sorry-free.
The new node attaches a declaration already present in the source library and adds no hole.

Validation: the final pruned module compiles locally through `lcompile.py`, with no errors
or warnings. All Lean lines are at most 100 characters. The source-library import passes
`tools/import_direction.py may`. The dry-run delivery performs the further checks.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`: its Scheme.Modules-to-Ab interface
  is not needed; Mathlib evaluation limits instances handle the actual functor.
- `Sheaf.AlgebraicGeometry.TensorPullback`: the direct-image definition is already
  provided by the retained public cohomology import; tensor pullback is not used.
- `Sheaf.CategoryTheory.GrothendieckComposablePair`: the source theorem directly accepts
  `Functor.IsAcyclicComposablePair`; no bundled pair is constructed.
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`: no Cartan–Eilenberg model,
  integer-indexed sequence comparison or edge-map result is needed.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`: no direct invocation is needed.
  Ringed-space Grothendieck instances remain available through the public cohomology
  definitions, so this does not remove their underlying resolution dependency globally.

Corresponding old direct proof edges removed from `pqf-lem-leray`:
`lem-sc-global-sections-left-exact`, `def-pc-module-pullback`,
`def-sp-composite-acyclicity`, `thm-sp-grothendieck`,
`prop-pur-kinjective-resolutions-exist`, and
`lem-weil-pbc-ring-modules-grothendieck-abelian`.
The source generic theorem still uses the acyclic-pair notion; its attachment records that
indirect dependency. No assertion that any of these nodes is globally unreachable is made.

No Cartan–Eilenberg construction below `thm-sp-grothendieck` is imported for this proof;
other users may still need those modules. The abelian-group target category need only be
abelian for the source generic theorem, so its separate Grothendieck proof is unnecessary.
The existing Mathlib resolution comparison (`lem-sp-derived-well-defined`) remains used.

## Where the brief, the DAG or earlier work was wrong

The planned Grothendieck node currently attaches a substantially stronger theorem requiring
Cartan–Eilenberg construction, functoriality and edge data. The source library already has
the exact objectwise natural-number existence interface required for Leray. Below this
unit's fixed route, using that interface avoids the extra construction. No mathematical
statement or definition needed correction.

The original global-sections lemma concerns `Scheme.Modules.globalSectionsFunctor` into
abelian groups, while this statement defines module cohomology via ringed-space,
module-valued evaluation. The proof explicitly supplies the exact scalar-forgetting
comparison rather than silently equating those derived functors.

Searches: LeanFinder returned sheaf-cohomology and Mayer–Vietoris primitives, Loogle returned
no hit for `Functor.rightDerived`, and LeanSearch was unavailable (Internal Server Error).
Local `rg` found and inspected the source generic theorem, its page and abutment proofs,
Mathlib `InjectiveResolution.isoRightDerivedObj`, `NatTrans.rightDerived`, and
`ShortComplex.mapHomologyIso`. Service unavailability is not treated as an absence result.

## New nodes

`src-grothendieck-spectral-sequence-nat` attaches the existing source-library
`CategoryTheory.Functor.exists_grothendieckSpectralSequence`; no Lean source is duplicated
and no new sorry is introduced. Its hypotheses include arbitrary abelian C, and it requires
only objectwise page and finite-abutment data. The supplied source proof forms the
truncation spectral object, computes its interval cohomology, and identifies its abutment
using acyclicity. Natural-number index zero is included, and no positivity restriction is
added to the object or total degree. In the actual application only the acyclicity proof
uses positivity, as required by the existing theorem.


## Second reading by Y3

1. **Visible declarations: pass.** Read the complete repository/sandbox diff. The
   existing `exists_leray_spectralSequence` signature is byte-for-byte unchanged from
   `theorem` through the text preceding `:= by`, including universe `v`, arbitrary
   scheme morphism, module type, quasi-coherence instance, every natural-number page
   index, and the entire abutment. All three public imports and public-section visibility
   stay unchanged. The only new declaration is a private, proved comparison theorem;
   no definition or existing statement changes and no change record is needed.

2. **Proof and axioms: pass.** Independently compiled the delivered module with
   `lcompile.py` (12.1 seconds, no errors or warnings). Compiled a scratch copy with
   `#print axioms` for both `AlgebraicGeometry.derived_forget_iso` and
   `AlgebraicGeometry.exists_leray_spectralSequence` (10.1 seconds): each lists exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. There is no
   `sorry`, forbidden declaration, or data definition in the delivered module.
   The helper uses Mathlib `InjectiveResolution.isoRightDerivedObj` twice and the exact
   forgetful functor's `ShortComplex.mapHomologyIso` between them, with the correct
   orientation. The acyclicity proof applies the pushforward theorem's second clause
   at the whole open; its successor-degree reindexing is justified precisely by `hq`.
   The abutment comparison uses an actual definitionally equal composite (`Iso.refl`),
   then functorial right derivation and the proved scalar-forgetting comparison.
   No arbitrary data is extracted from an unproved existence theorem.

3. **Split statements and attachment: pass.** There are no split-off holes. Read the
   new attachment against the source module's category assumptions and
   `Functor.exists_grothendieckSpectralSequence` at lines 774–785, as well as its page
   and abutment proofs at lines 182–243. It attaches this existing declaration rather
   than duplicating it or restating the Leray item as an unproved theorem. Both source
   categories are Grothendieck abelian; the target need only be abelian. Additivity,
   finite-limit preservation and injective acyclicity are supplied in the application.
   Checked degree zero, zero modules, and the identity morphism: no positive-degree
   restriction is imposed on the page or abutment, and the construction still applies.
   An independent Loogle search for `ShortComplex.mapHomologyIso` reported an unknown
   identifier (not evidence of absence); direct Mathlib reading found that isomorphism
   and its exact resolution-comparison interface. Local searches with
   `forget.*rightDerived`, `rightDerived.*forget`, and composite-isomorphism names found
   no shorter comparison for exact postcomposition. Read
   `Sheaf.CategoryTheory.RightDerivedExactComposite`: it instead concerns exact
   precomposition and is not the needed statement. A DAG search for the attached
   source declaration found no existing attachment.

4. **Route and pruning: pass.** The proof proceeds directly from the generic source
   theorem, the existing pushforward acyclicity theorem, and Mathlib homology; there
   is no unnecessary Cartan–Eilenberg construction. The three public imports provide
   the cohomology/direct-image definitions, quasi-coherence predicate, and spectral
   sequence/abutment types in the unchanged statement. Both plain imports are used
   by the proof. Compared the old `proof_deps` with the new list: all six removed
   edges are explicitly listed under `No longer needed`, together with the five
   removed imports. Read `dag/units/sk-prop-av-pqf-finite.json`: its fixed statement is
   proper plus quasi-finite implies finite, its sole step invokes Tag 02OG, and its
   realized statement/step lists are empty. This Leray proof changes neither of those
   unit requirements; it only replaces the generic theorem interface below them.

5. **DAG consistency: pass.** Compared both node files with the code. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`; its statement, statement
   dependencies, Lean attachment and all other fields remain unchanged. Its three
   steps match acyclicity, generic existence/page transport, and composite-abutment
   transport respectively. In both nodes, `proof_deps` is exactly the union of step
   `uses`. The new node has the required source, search records, creation/blueprint
   provenance, matching chapter/unit and existing-declaration Lean record. Its
   generic statement matches the source theorem's hypotheses and objectwise page and
   finite-filtration conclusion; it adds no Lean file or hole.

Second reading changed only this report: recorded the independent signature comparison,
compilation, clean axiom results, edge-case checks, dependency review and pruning verdict.
The proof and node records required no repair. One original hole is closed, zero holes
are added, and zero are split off; this is a proof, not a decomposition.
