## What changed

Proved AlgebraicGeometry.affineQCohDerivedAdjunction_construction with its signature unchanged.
Added proof-only imports for the unbounded derived adjunction and restriction of adjunctions.
The former also exports the exact-functor homology comparison used in the proof.
Tilde preserves monomorphisms by pointwise injectivity of localized module maps;
its adjunction supplies cokernel preservation. These give exactness. Lift its derived
functor to QCoh using the homology comparison, then restrict the derived adjunction.
Both comparison isomorphisms are supplied by construction. Local compilation is clean.
Updated the existing node's proof route; no new definitions or statements.
Resumed validation after the recorded tool failure: deliver3.py --no-push now prints
OK; compilation and preflight pass, with review class CODEX for the node-file change.
Nothing pushed. The earlier failure recorded below is historical and no longer blocks
the dry run; no delivery tool or repository file was edited by this worker.

## Proved and sorry left

Closed the sole hole: AlgebraicGeometry.affineQCohDerivedAdjunction_construction
(new-affine-qcoh-derived-adjunction-construction). No sorry remains in the item;
no holes added. The source library's exact-left-adjoint derived adjunction and homology comparison use only
standard axioms. The item still depends on existing open resolution results through
RingedSpace.moduleGrothendieckAbelian; #print axioms reports sorryAx for this dependency.

## No longer needed

Removed redundant provisional proof imports Mathlib.CategoryTheory.Abelian.Exact,
Mathlib.Algebra.Homology.ShortComplex.ExactFunctor, and
Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono, and
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: all are already
available through the necessary imports. No original import removed. No planned dependency pruned: the sole planned dependency,
lem-weil-pbc-affine-tilde-gamma-adjunction (Mathlib.AlgebraicGeometry.Modules.Tilde),
is used. No new intermediate modules are delivered.

## Where the brief, the DAG or earlier work was wrong

The existing plan cites only the ordinary adjunction while its step also requires exactness,
derived descent and restriction. Those are now actual Lean constructions. No statement error.
The local literature files named in the node are absent; read Stacks Tags 06Z0 and 079W online.
Zero ring and empty spectrum cause no exception: the monomorphism proof is pointwise,
and all constructions are valid for arbitrary commutative rings and unbounded complexes.
No unit realization is bypassed (the unit's realized lists are empty for this auxiliary node).
LeanFinder returned generic Adjunction.derived; Loogle found restrictFullyFaithful;
LeanSearch was unavailable. Repository/Mathlib grep found the exact-left-adjoint derived
adjunction and homology comparison, and localized-map injectivity completed exactness.


## Earlier second reading (a previous round; superseded)

1. Interface: compared the delivered file with the repository using diff and checked
   the theorem signature byte for byte. The sole existing declaration, its docstring,
   and all original public imports are unchanged. No definitions or statements added.
   Found literal Unicode escape strings in the node's statement and lean.statement;
   restored statement and the complete lean record from the repository. The node now
   differs only in proof, proof_deps and proof_origin. Verdict: passes after repair.
2. Proof: local compilation is clean. A scratch copy with #print axioms for
   AlgebraicGeometry.affineQCohDerivedAdjunction_construction reports propext,
   Classical.choice, Quot.sound and sorryAx. Separate checks show the ordinary tilde
   adjunction, exact-left-adjoint derived adjunction and homology comparison use only
   standard axioms; moduleGrothendieckAbelian still uses sorryAx from existing resolution
   dependencies. No sorry or forbidden construct occurs in the delivered module, and
   no arbitrary witness is selected from an unproved existence statement. F is the
   ObjectProperty lift of mapDerivedCategory; G is inclusion followed by the existing
   right derived functor. Verdict: one local hole closed, no holes added, dependent
   resolution holes remain.
3. Split statements: none. Independently searched Mathlib with msearch grep for
   tilde preservation/monomorphism and with Loogle for "tilde", "mono" (zero hits),
   and searched both library roots for affine adjunction and tilde exactness. No shorter
   existing affine construction found. The pointwise injectivity argument works also
   for the zero ring/empty spectrum (there are no points to check), zero modules, and
   arbitrary opens; the derived argument imposes no boundedness assumption. Verdict: passes.
4. Route and pruning: read Stacks Tags [06Z0](https://stacks.math.columbia.edu/tag/06Z0)
   and [079W](https://stacks.math.columbia.edu/tag/079W), the source derived-adjunction
   implementation, its homology comparison, Mathlib tilde.map and restrictFullyFaithful.
   Localization injectivity plus left-adjoint cokernel preservation gives exactness;
   the homology isomorphism carries tilde quasi-coherence to the derived image.
   Restriction along identity and the fully faithful QCoh inclusion supplies F ⊣ G;
   the two comparisons are mapDerivedCategoryFactors and Iso.refl. Removed the redundant
   direct proof import of the source ExactFunctor module, exported by the needed
   derived-adjunction module; the resulting proof still compiles. Original public imports
   retained because they supply the signature and its existing interface. Every old
   proof dependency remains used. Read sk-thm-picard-f-representable.realized: its
   statement and step lists are empty, so no realized unit route is bypassed. Verdict: passes.
5. DAG: checked the ordinary affine-adjunction, localization-exactness and generic
   derived-adjunction nodes. The first is used directly; the second is used in its
   injectivity special case via IsLocalizedModule.map_injective; the third through
   mapDerivedCategoryRightDerivedAdjunction, whose implementation applies Adjunction.derived.
   The union of uses equals proof_deps. The two recorded steps follow exactness,
   derived descent, quasi-coherence and restriction in the Lean proof; proof_origin
   names the matching Stacks construction. No new nodes. Verdict: passes.

Changed in this reading: restored unchanged node statement metadata, removed one
redundant proof-only import, corrected the report's description of residual axiom
dependencies, and recorded this independent review. The proof body needed no repair.

Delivery tool failure: two authorized deliver3.py --no-push runs both compiled and
then failed preflight with the sole reason `(a) uncommitted changes in the working tree`.
The second reader ran no git command and changed no repository files. No push attempted.
The reviewed and repaired delivery remains in this sandbox; the launcher must repair
its delivery working-tree handling before this item can be delivered.


## Second reading by N1

1. Interface — PASS. Independently diffed the sole delivered module against the
   read-only repository and compared the entire existing theorem signature byte for
   byte. The signature, original docstring, universes, hypotheses and five public
   imports are unchanged. Only the proof and two private-to-the-module proof imports
   were added. There are no change records, new statements or definitions. Parsed
   the node diff: only proof, proof_deps and proof_origin differ; its statement and
   entire lean record remain identical.
2. Proof — PASS with existing upstream holes. Compiled the actual delivered module
   using lcompile.py without errors or warnings. A fresh scratch copy,
   scratchpad/SecondReaderAxioms.lean, prints propext, Classical.choice, Quot.sound
   and sorryAx for affineQCohDerivedAdjunction_construction. Independent prints for
   tilde.adjunction, mapDerivedCategoryRightDerivedAdjunction and
   mapDerivedCategoryHomologyFunctorIso contain only the three standard axioms;
   moduleGrothendieckAbelian contains sorryAx. Read its implementation: it takes the
   Grothendieck property from the existing small-site resolution theorem. The new
   proof constructs F by ObjectProperty.lift and G by inclusion followed by the
   existing rightDerivedFunctor; it selects no arbitrary witness from an unproved
   existence theorem. Scanned the delivered module: no sorry, axiom, unsafe, opaque,
   implemented_by, extern or kernel-check bypass. Closed one local hole, added zero;
   this does not claim that the target's import closure is axiom-free.
3. Split statements — PASS (none). No split-off statements or new nodes are present.
   Independently searched both Lean source roots for affine derived adjunction and
   tilde exactness, and used msearch grep for tilde preservation/exactness and Loogle
   for tilde with PreservesMonomorphisms (zero hits). Read Mathlib tilde.map and
   IsLocalizedModule.map_injective: localization injectivity is applied to each
   section value, with the original monomorphism supplying injectivity. The zero
   ring/empty spectrum and empty open are vacuous pointwise cases; zero modules
   impose no extra assumption. The rest applies in every integer degree, with
   no boundedness restriction or additional ring hypothesis.
4. Route and pruning — PASS. Read Stacks Tags
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0) (elucidation and exactness) and
   [079W](https://stacks.math.columbia.edu/tag/079W) (unbounded derived adjunction).
   Read the source exact-left-adjoint construction and its homology comparison,
   and Mathlib restrictFullyFaithful. Finite colimits follow from tilde.adjunction;
   pointwise localization injectivity supplies monomorphisms, hence exactness.
   The homology comparison has source tilde of module homology and target homology
   of the derived image, so prop_of_iso transfers quasi-coherence in the required
   direction. Restriction uses identity on D(A) and the full QCoh inclusion; its
   two commuting isomorphisms have the right orientations. mapDerivedCategoryFactors
   gives the first requested comparison, and Iso.refl gives the second. The two
   added imports are proof-only and each supplies an essential construction.
   No original proof dependency is unused; No longer needed correctly says no
   original import or dependency is pruned. The unit record
   sk-thm-picard-f-representable has empty realized statement and step lists, so
   this auxiliary construction bypasses no realized unit route.
5. DAG — PASS. Read the item and all three recorded dependency nodes. The affine
   tilde/Gamma node supplies adjunction and quasi-coherence; localization exactness
   is used through its injectivity special case IsLocalizedModule.map_injective;
   the generic derived-adjunction node is used through the source wrapper, whose
   body applies Adjunction.derived after constructing the derived comparisons.
   The union of uses in the two proof steps is exactly proof_deps. The steps
   describe the actual exactness, homology lift, restriction and comparison
   constructions. proof_origin matches the Stacks elucidation. No new-node
   metadata or statement-change record is needed.

Changed in this reading: added this current, independently verified second-reading
section, repairing the dry run's missing-section failure. No Lean proof, import,
statement, definition or node repair was needed. The earlier working-tree failure
above is historical; the current first dry run failed only because this section
was missing. The delivery counts one of one local holes closed, zero split off,
and no original dependency pruned.
