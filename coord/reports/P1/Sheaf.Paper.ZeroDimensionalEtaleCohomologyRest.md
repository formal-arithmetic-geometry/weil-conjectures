## What changed
`Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest` proves its unchanged conjunction.
Positive-degree vanishing is a real exact-functor reduction: install finite-colimit
preservation of global sections, identify RΓ(F[0]) with Γ(F)[0] using the existing
`Functor.singleFunctorCompRightDerivedFunctorIso`, transport single-complex homology
vanishing, and convert IsZero to Subsingleton. The degree-zero comparison applies
`zero_dimensional_etale_cohomology_iso` to exactly the original chosen points.

The proof-only imports are `Sheaf.Paper.ZeroDimensionalGlobalSectionsExact`,
`Sheaf.Paper.ZeroDimensionalEtaleCohomologyIso`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
and `Mathlib.Algebra.Category.Grp.Zero`. No existing signatures, definitions or public
imports changed. Two new statement modules contain the remaining geometric obligations.

Repair of return X-8478c: both new proof plans and Lean docstrings now cite
`lem-weil-pbc-strictly-henselian-sections-stalk` (Stacks Tag 03QO). The exactness
plan replaces geometric-point cohomology with this natural germ isomorphism and
`prop-weil-pbc-geometric-stalks-exact`; the degree-zero plan explicitly compares
the canonical and specified germs through sections. No Lean signature or proof
term changed in this repair.

The strictly henselian germ lemma is used as a generic tool: specialize its
ring R to the algebraically closed field k on each reduced point summand. Its
statement gives an isomorphism natural in every abelian sheaf, at every chosen
algebraically closed geometric field lying over the closed point. It is not an
invocation of the proper-base-change unit's theorem or its route. The existing
finite reduction and coproduct route of sk-prop-cd stays intact.

## Proved and sorry left
The existing declaration `AlgebraicGeometry.zero_dimensional_etale_cohomology_rest`
is proved relative to the two split obligations. This is 1 of 1 original declarations
with a local sorry closed, not a claim of axiom-free target completion.

The two remaining named sorries are:
- `AlgebraicGeometry.zero_dimensional_global_sections_preservesFiniteColimits`, node
  `zero-dimensional-global-sections-exact`, module
  `Sheaf.Paper.ZeroDimensionalGlobalSectionsExact`;
- `AlgebraicGeometry.zero_dimensional_etale_cohomology_iso`, node
  `zero-dimensional-etale-cohomology-iso`, module
  `Sheaf.Paper.ZeroDimensionalEtaleCohomologyIso`.

Both have source citations and full natural-language proofs in their docstrings.
The parent depends on sorryAx through these obligations; no new axiom is introduced.

## No longer needed
No old import or old proof dependency is pruned from the target closure. Each of the
old eight proof dependencies remains in the degree-zero obligation's plan:
`lem-weil-pbc-finite-type-dim-zero-artinian`,
`lem-weil-pbc-closed-point-residue-field-base`,
`lem-weil-pbc-reduction-universal-homeomorphism`,
`lem-weil-pbc-finite-discrete-scheme-affine`,
`lem-weil-pbc-scheme-coproduct-family`,
`lem-weil-pbc-finite-geometric-point-coproduct-cohomology`,
`thm-weil-pbc-universal-homeomorphism-invariance`, and
`lem-weil-pbc-inverse-image-stalk-germ`.
The parent's direct proof_deps are now the exactness and degree-zero nodes.
The first reader's new unresolved vanishing module and node were removed from the
sandbox before delivery. The duplicate PlusCompatibility public import was removed
from the new degree-zero module; LowerShriek already publicly provides it.
The new exactness module uses only statement imports and avoids derived machinery.
The exactness plan no longer needs `lem-weil-pbc-geometric-point-cohomology`
(module `Sheaf.AlgebraicGeometry.GeometricPointCohomology`) for its summand step;
this is a local plan change, not a claim that this module leaves the target closure.

## Where the brief, the DAG or earlier work was wrong
The first worker's two new nodes incorrectly depended on the parent theorem whose
proof called them; this did not describe independent proofs and would create a cycle
if the parent metadata were brought into agreement. Their natural-language statements
were merely labels, their docstrings omitted source citations and proof details,
and the parent node was not updated to match the submitted conjunction proof.
The second reading repairs all of these faults and replaces the unresolved vanishing
conjunct with an exactness reduction using existing derived-category declarations.
The returned version then incorrectly cited geometric-point cohomology as an
exact-evaluation result, although its declaration supplies cohomology vanishing
and an H⁰/stalk comparison. It also extended the canonical coproduct germs to
arbitrary points using tags without a cited DAG result. Both gaps are repaired
by the actual natural germ statement of the strictly henselian sections lemma;
finite-colimit preservation additionally uses the geometric-stalk exactness node.

## New nodes
`zero-dimensional-global-sections-exact` records finite-colimit preservation of global
sections, without a chosen sheaf, geometric points, or any cohomology conclusion.
Its proof is finite reduction, natural strictly henselian germ isomorphisms on
algebraically closed point summands, geometric stalk exactness, finite biproduct
assembly, and transport across the reduction sheaf equivalence.

`zero-dimensional-etale-cohomology-iso` records only the specified canonical degree-zero
map, with the original hypotheses. Its plan independently retains the original finite
reduction, finite coproduct calculation and inverse-image germ compatibility; it does
not apply the parent theorem. No change records are needed.

## Earlier second reading (a previous round; superseded)
1. Compared the delivered parent module with the repository version by diff and by
   extracting the original signature up to `:= by`: byte-for-byte unchanged. Existing
   definitions and public imports are unchanged. New modules contain only new named
   theorems. Verdict: pass.
2. Compiled the initial three modules, then compiled the repaired set in import order
   through lcompile.py. The parent has no local sorry; the only two remaining sorries
   are the listed named theorems. No axiom, unsafe, opaque, implemented_by, extern,
   sorry in a definition, or bypass of kernel checking occurs. Scratch #print axioms
   checks show exactly propext, Classical.choice, Quot.sound and sorryAx for all three
   declarations; deliver3.py also probes the final set. Verdict: pass subject to
   the explicitly recorded open geometric obligations.
3. Checked the new statements on the empty scheme (zero global sections and empty
   stalk product), Spec k, finite unions of points, and nonreduced Artinian points.
   Reduction invariance accounts for nilpotents. Arbitrary algebraically closed Ω(x)
   needs no algebraicity assumption: the actual declaration
   `Scheme.strictlyHenselianSections_geometricStalk_isIso` accepts an arbitrary
   algebraically closed Ω and a point over the closed point of Spec R. At R = k,
   its first conjunct makes both canonical and specified germs invertible; its
   second gives naturality in the sheaf. The stalk comparison is the inverse
   canonical germ followed by the specified germ, so it respects the stated map.
   Exactness makes no cohomology claim; the other split is only the canonical H⁰
   identification. Neither is the parent conjunction under another name.
   LeanSearch was attempted but unavailable (Internal Server Error), recorded
   honestly in both nodes. Independent leanfinder, loogle and grep searches found no theorem for these
   statements; library rg searches found only strictly henselian special cases.
   Full source/proof docstrings replace the inadequate first-worker summaries.
   Repair recheck: read the actual strictly henselian Lean statement and the
   `prop-weil-pbc-geometric-stalks-exact` Mathlib match. The former identifies
   terminal-object sections, not derived cohomology, with the stalk naturally.
   Restriction Γ to that terminal object is a natural isomorphism. The latter
   cites the sheafFiber left-adjoint instance in Point/Skyscraper.lean, which
   preserves finite colimits. Thus these statements support the exactness step.
   Both new docstrings and step-source citations include Tag 03QO. This recheck
   supersedes the earlier tags-only evaluation justification. Verdict: pass.
4. Replaced the bare conjunction split by the shorter existing exact-derived-functor
   route for positive degrees. Proof imports are plain imports. Retained all old
   public imports of the parent; removed redundant imports from the new module and
   avoided derived machinery in the exactness signature module. No old DAG dependency
   is lost from the target closure. `dag/units/sk-prop-cd.json` has empty realized
   statement/step lists; no realized node is bypassed or changed. Both geometric
   obligations follow the existing reduction-to-points unit route. Verdict: pass.
5. Updated the parent proof, proof_deps and proof_origin to the actual Lean reduction.
   New node statements are self-contained and their lean.statement is verbatim;
   proof_deps equal the union of step uses. Removed references to the parent from
   both new-node proof plans and recorded fresh independent searches. Checked all
   required source, creation, blueprint, chapter, unit and Lean fields. Verdict: pass.

Changes by the second reader: replaced the vanishing split with finite-colimit
preservation and a compiled exact-functor proof; removed its old module/node; supplied
complete source/proof docstrings and self-contained new-node statements; repaired
parent and new-node proof metadata; minimized the new statement imports; rewrote
this report to describe the final delivery and its remaining obligations honestly.

Preflight repair: added the required LeanSearch service attempt (unavailable), and
corrected the exactness node signature extraction to start at the actual declaration
rather than the word "theorem" in its docstring. No Lean statement changed.

Return repair X-8478c: replaced the exactness step's incorrect dependency with
strictly henselian germs and geometric stalk exactness; added strictly henselian
germs to the degree-zero step; recomputed proof_deps as the union of uses;
updated both proof origins, source citations and Lean proof docstrings. The
second-reading checks above now address these actual cited statements. The
repair was performed in-thread; no new independent second reader was launched.

## Second reading by P1

1. Compared the delivered parent module against the repository version. The theorem
   signature and existing public imports are unchanged; the added imports are proof
   imports. The two new modules contain only the explicitly split named statements.
   Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds. The
   parent has no local `sorry`; the only remaining sorries are the two named split
   obligations, with no axiom, unsafe, opaque, extern, implemented_by, or sorry in a
   definition. Verdict: pass.
3. Checked both split statements for truth and strength on empty schemes, spectra of
   algebraically closed fields, finite unions of points, and nonreduced schemes.
   Their docstrings cite the source and give independent reductions; neither restates
   the parent theorem, and searches found no existing declaration. Verdict: pass.
4. The parent uses finite-colimit preservation plus the existing derived single-complex
   comparison for positive degrees, and the independent canonical degree-zero
   comparison theorem. Proof-only imports are plain imports and no old dependency is
   pruned; the unit route through finite reduction and coproducts remains recorded.
   Verdict: pass.
5. DAG node statements and Lean signatures match byte-for-byte, and each proof,
   proof_deps, proof_origin, source, blueprint, unit, and creation field matches the
   implemented route. Verdict: pass.

Changes made during this second reading: added this explicit review section; no Lean
proof or statement changes were necessary.
