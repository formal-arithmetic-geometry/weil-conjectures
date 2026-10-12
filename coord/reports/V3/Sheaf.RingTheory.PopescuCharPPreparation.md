## What changed
Repair of return X-f8f75 (B9 and H9): corrected both new nodes’ blueprint ancestry to
`thm-weil-pbc-finite-etale-lifting`, with the requested step-7 place and six-node via chain.
Transferred all thirteen reviewer-listed construction imports into the core as plain imports.
These preserve its unfinished construction plan in the import-based queue.

Repaired both returned intermediate interfaces in the sandbox. The core now supplies the
actual auxiliary thickening: a positive maximal-ideal power bound, ideals I and K with
I⊆JQ, K⊆JL, IL⊆K, and a commuting factorization through a Q/I-algebra D essentially
smooth over Q/I. It constructs neither the final E over the eighth-power quotient nor
the dimension/minimality alternative. The quotient theorem descends these witnesses.
The main declaration's signature is unchanged; its proof unpacks and passes the new data.
Both intermediate docstrings now contain complete proofs under their actual hypotheses.
Their nodes state all objects and conditions, include definition dependencies, and list
explicit proof steps and their union of dependencies. The main node records the delivered
composition. The reviewer-required dispute sentence is wrapped immediately before the corrected quotient
declaration docstring to meet the 100-character rule and preserve docstring attachment.
Every Lean line has length at most 100; no linter option is disabled.

## Proved and sorry left
Closed: `Algebra.exists_popescu_char_p_preparation` (one original hole), by composition.
Added/remaining: `Algebra.exists_popescu_char_p_preparation_core`
(node `popescu-char-p-preparation-core`) and
`Algebra.popescu_char_p_preparation_quotient`
(node `popescu-char-p-preparation-quotient`), each with proof exactly `by sorry`.
This is a decomposition into two construction/descent steps, not a sorry-free proof of
Popescu preparation; net holes closed minus added is -1. No data definition or axiom was added.

## No longer needed
Every removed import and its disposition follows:

- `Mathlib.RingTheory.FiniteStability`: removed; not needed by the unchanged public signature or the composition proof.
- `Mathlib.RingTheory.Localization.Submodule`: removed; not needed by the unchanged public signature or the composition proof.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`: removed; not needed by the unchanged public signature or the composition proof.
- `Sheaf.AlgebraicGeometry.Ogoma`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-ogoma).
- `Sheaf.RingTheory.EssentiallySmoothComp`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-essentially-smooth-composition).
- `Sheaf.RingTheory.ImprovePresentation`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-improve-presentation).
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-popescu-enlarge-solution-modulo).
- `Sheaf.RingTheory.PopescuSolutionModulo`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-popescu-solution-modulo).
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-regular-local-generators-regular-sequence).
- `Sheaf.RingTheory.RegularRingSmoothAscent`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-regular-ring-smooth-ascent).
- `Sheaf.RingTheory.RegularSequencePolynomialVariables`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-regular-sequence-polynomial-variables).
- `Sheaf.RingTheory.RegularSequencePowers`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-regular-sequence-powers).
- `Sheaf.RingTheory.SingularIdealLocalizationSmooth`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-singular-ideal-localization-smooth).
- `Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-smooth-free-differentials-strictly-standard-power).
- `Sheaf.RingTheory.StrictlyStandardBaseChange`: removed from main; transferred to the core as a plain import; construction remains needed in its proof node (lem-weil-pbc-strictly-standard-base-change).
- `Sheaf.RingTheory.SingularIdeal`: removed from main and transferred to the core as a plain import; definitions remain available through public PopescuResolution.

`Sheaf.RingTheory.GRing` is also removed from the new quotient module: its corrected
interface uses no geometric-regularity hypothesis. Its G-ring definition dependency is
removed from that node; the core still uses geometric regularity.

No construction node has been pruned: the original lower proof dependencies are still
needed by the strengthened core or quotient nodes. Their direct edges from the main node
are replaced by the two intermediate edges. The detailed modules are no longer direct
imports of the main module; they remain proof obligations within the intermediate nodes. The thirteen construction
imports requested in H9 are now present in the core; they are not globally pruned.
No module is claimed globally unreachable without checking the full target import closure.

Every old main-node proof dependency is retained in the core's construction plan (none
is claimed globally pruned). The removed direct edges are:

- `def-weil-pbc-singular-ideal`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-popescu-resolution`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-localization-at-prime`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-localization-noetherian`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-fg-ideal-radical-power`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-finite-type-algebra-noetherian`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-singular-ideal-localization-smooth`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-smooth-ring-map-base-change-composition`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-polynomial-ring-smooth`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-smooth-ring-map-principal-localization`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-smooth-ring-map-local-on-cover`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-improve-presentation`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-smooth-free-differentials-strictly-standard-power`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-strictly-standard-element`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-popescu-solution-modulo`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-essentially-smooth-ring-map`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-flat-local-hom-faithfully-flat`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-faithfully-flat-ideal-contraction`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-field-regular-ring`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-regular-ring-smooth-ascent`: retained in `popescu-char-p-preparation-core`.
- `def-weil-regular-scheme`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-flat-height-formula`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-regular-local-generators-regular-sequence`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-regular-sequence`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-regular-sequence-polynomial-variables`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-regular-sequence-powers`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-ogoma`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-essentially-smooth-composition`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-popescu-enlarge-solution-modulo`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-finite-presentation-base-change-composition`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-strictly-standard-base-change`: retained in `popescu-char-p-preparation-core`.
- `lem-weil-pbc-localization-base-change`: retained in `popescu-char-p-preparation-core`.
- `def-weil-pbc-finitely-presented-algebra`: retained in `popescu-char-p-preparation-core`.

## Where the brief, the DAG or earlier work was wrong
B9: the previous new-node ancestry incorrectly named a non-blueprint node as its ancestor;
both ancestry records now match the reviewer’s exact replacement.
H9: the previous delivery removed construction imports from the main without transferring
them to the unfinished core. All thirteen listed imports are now transferred to the core.

STATEMENT-DISPUTED: Zero parameters satisfy hparam but need not cut the target localization
to dimension zero. The previous quotient theorem is false for k=F₅, m=0,
A=C=k[ε]/(ε²), Λ=k[t], α=γ evaluation ε↦0, β=id, q=(t), r=1, π₀=0.
The old hypotheses hold while J=0 and dim Λ_q=1. Merely adding geometric regularity
would not exclude this example. The repaired theorem explicitly requires a positive power
of m_L to lie in JL and retains the earlier thickening factorization for descent.
The previous proof sketches and statement placeholders did not specify these data; the
old main-node dependency list did not describe the delivered composition. These are repaired.

## New nodes
`popescu-char-p-preparation-core`: the polynomial and standardized algebra construction
with auxiliary thickening witnesses; module `Sheaf.RingTheory.PopescuCharPPreparationCore`.
`popescu-char-p-preparation-quotient`: canonical quotient/localization descent from the
power bound and the earlier factorization; module `Sheaf.RingTheory.PopescuCharPPreparationQuotient`.
Changed node `lem-weil-pbc-popescu-char-p-preparation`: composition of those two steps.
Change records: `coord/changes/popescu-char-p-preparation-core.md`,
`coord/changes/popescu-char-p-preparation-quotient.md`, and
`coord/changes/popescu-char-p-preparation-imports.md`.

## Earlier second reading (a previous round; superseded)
Repair check (not a claim of a new independent-reader session): the unchanged main signature
is reconstructed by the composition proof. The two intermediate statements now distinguish
construction of D over Q/I at an earlier thickening from construction of E over the final
quotient base P. The quotient proof uses I⊆JQ for its base map, K⊆JL for its target map,
the factorization equation for commutativity, and the positive power bound for dimension.
The zero-parameter counterexample cannot satisfy m_L^n⊆JL with n>0: JL=0 in
F₅[t]_(t) and every positive power of (t) is nonzero. When the original localized target
has dimension zero, zero padding is valid because its maximal ideal is already zero
(geometric regularity makes that localization regular), and the power bound still holds.
The nilpotent quotient maximal ideal gives a nonzero Artinian local ring, hence dimension
zero; the localization prime correspondence gives minimality over any contained singular
ideal. The factorization descends through E=P⊗_(Q/I)D, and essential smoothness survives
this base change by the smooth-localization presentation. Thus the correction has substantive
geometric hypotheses, rather than a check only at the type level. The source construction's
units, parameters, power bound and earlier D′[t] factorization provide exactly these data.
The original unit route is retained; no blueprint step is bypassed.
All three delivered modules compile without errors or warnings. The original source of
`Sheaf.RingTheory.PopescuResolveCharP` also compiles unchanged against the sandbox overlay;
its status is unclaimed in this checkout. No forced adaptation is needed.

## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-12. Verdicts for the five review points:

1. Compared every delivered Lean module with the repository. Only the main module already
   exists there; its entire declaration signature is byte-for-byte unchanged. The two new
   interfaces and the removal of three public imports are covered by the supplied change
   records. No definition, target or downstream signature changed.
2. Compiled all three files with lcompile.py in import order, without errors or warnings.
   Scratch copies with #print axioms for all three declarations report exactly propext,
   Classical.choice, Quot.sound and sorryAx. There are exactly two explicit holes, both
   named theorems listed above with proof `by sorry`; no data definition or forbidden
   declaration form is present. The main proof actually unpacks core data, restores the
   algebra instances, applies descent and reconstructs the unchanged existential statement.
3. Read both split statements, their proof docstrings and nodes against Stacks 07FJ, using
   the local smoothing.tex copy at /home/ubuntu/c1-stacks-review. The core constructs an
   earlier thickening factorization; the quotient lemma descends it to the final base.
   Neither merely renames the original target. For d=0, regularity forces the localized
   maximal ideal to vanish, so zero padding satisfies the power bound. For zero parameters
   in positive dimension, the old dual-number/F₅[t] example fails the new power bound.
   In descent, JΛ⊆q ensures a nonzero local quotient, the bound makes its maximal ideal
   nilpotent, and prime correspondence gives minimality. I⊆JQ and K⊆JL define the two
   quotient maps; tensor base change gives the required E and commuting factorization.
   Checked n=N+de against d(e-1)+1; it works also for d=0 and N≥1. Repeated searches with
   different Loogle and LeanFinder queries plus rg on the upstream library and Mathlib.
   Found smooth base change, quotient localization and the nilpotent-maximal-ideal
   Artinian criterion, but no complete construction/descent theorem to replace either
   hole in a few minutes. Recorded those results in both nodes.
4. Read from the main theorem down through the two interfaces. Public imports supply
   signature notions; the two new proof dependencies are plain imports. Also compiled a
   scratch copy of the unchanged PopescuResolveCharP caller against the delivered modules;
   it succeeds without errors or warnings despite the removed public imports. No easier complete
   route was found. The old dependency edges now occur in the core plan, rather than
   being claimed globally pruned. Read sk-thm-p1.json: this item is not one of its realized
   unit statements/steps, and none of those routes or records changes.
5. All three node Lean statements exactly match their declaration signatures. Each
   proof_deps list equals the union of its proof steps' uses; the main node records exactly
   the two applications in Lean. New nodes have the required source, searches, creation,
   blueprint, chapter, unit and Lean records. The main node changes only proof,
   proof_deps and proof_origin. Checked the new nodes' statements clause by clause against
   the power/ideal witnesses and commuting equation in Lean.

Changes made by this reader: expanded core step 7 into the actual base change, β and γ
construction instead of referring to an absent original step; explained how finite
presentations shrink the essentially smooth auxiliary rings to the required universe;
updated matching node steps; made the quotient dispute comment explicitly historical;
recorded the independent searches and this review. No Lean proof or signature changed.
This remains a decomposition: one original hole closed and two lower holes added, net -1.

## Second reading by V3

Independent current second reader, 2026-10-12; the earlier readings above are historical.

1. PASS. Diffed all three delivered modules against the repository. The only existing
   declaration is Algebra.exists_popescu_char_p_preparation; its signature is byte for byte
   unchanged (also checked with the project declaration parser). No definitions are added or
   changed. The two new interfaces and the public-import removals have change records.
2. PASS as a decomposition. Compiled all three modules in import order using lcompile.py.
   Scratch copies with #print axioms for all three declarations show only propext,
   Classical.choice, Quot.sound and sorryAx. The only explicit holes are the two named
   split theorems listed in Proved and sorry left; no forbidden declarations or hollow
   definitions occur. The main proof unpacks actual core witnesses and applies quotient
   descent, rather than renaming the original statement.
3. PASS. Read the complete two split statements, docstring proofs and nodes against the
   local Stacks smoothing.tex proof of 07FJ, including the actual earlier thickening
   factorization. Tested the zero-dimensional case: regularity gives m_L=0, so zero
   padding and the positive power bound coexist. In positive dimension zero parameters
   fail the power bound, excluding the historical counterexample. Checked n=N+de against
   d(e-1)+1, including d=0, N>=1. In descent, JΛ⊆q prevents a zero local quotient;
   m_L^n⊆JL supplies dimension zero and minimality, while I⊆JQ, K⊆JL and the supplied
   composite equality supply the tensor factorization. Both statements are strict parts
   of the original construction/descent argument. New Loogle and LeanFinder searches and
   rg across Mathlib, upstream WeilConjectures and lean/Sheaf found individual smooth
   base-change, nilpotent-maximal-ideal and quotient-localization tools, but no complete
   replacement. Neither full split proof can be closed in a few minutes.
4. PASS. Read the main proof downward through both boundaries; no shorter complete route
   was found. Public imports serve the signatures, and construction-only Sheaf imports
   remain plain imports in the unfinished core. The quotient's remaining dependencies
   outside its public imports are Mathlib matches, not omitted unfinished Sheaf modules.
   Compiled the unchanged PopescuResolveCharP caller against the sandbox overlay: clean.
   Checked every old main proof dependency against No longer needed and the core plan:
   none is claimed globally pruned. Read sk-thm-p1.json realized: no realized unit statement
   or step is replaced, and its route is unchanged.
5. PASS. All three node Lean signatures match the files verbatim; proof_deps equals the
   union of proof-step uses in each node. The main node changes only proof, proof_deps
   and proof_origin and describes the two actual applications. Both new nodes have the
   required source, statement dependencies, searches, status, creation, ancestry, chapter,
   unit and Lean records. Their prose conditions agree with the Lean witnesses.

Changed in this reading: repaired a broken gamma symbol in the core proof docstring,
recorded the independent searches in both new nodes, and appended this review. No proof,
signature, definition or import changed. One original hole is closed by composition and
two lower holes remain: decomposition, net -1; no globally pruned construction module.
