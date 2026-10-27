## Compile companion for the published-build transition

The extraction above is committed correctly, but the current published Postnikov
artifact still contains the moved definitions. A main-item-only deliver2 dry run
therefore reported a duplicate fixedPairShift import. Restored the Postnikov module
and its node as byte-for-byte copies of current sheaf-dag solely as compiler input.
They introduce no Git delta and no dependency-field change. Retain these two exact
compile companions until the published build contains the extraction. The definition
node/module remain on the base; do not recreate their old sandbox versions.

This is an authorized same-packet compilation against current sources through the
existing wrapper. It does not change source-selection tools or published artifacts.
The active packet now has two modules and two node files, but its intended delivery
delta is still only the item's node, item module and report.

## Maintenance resolved the delivery blocker (2026-10-25)

Server sheaf-dag commit 98b5ab386fc2a8c0f193bf06273ddfff16fbd3db installs the
shared definition extraction and Postnikov dependency citation as maintenance data.
The four definitions have the same names, signatures and bodies, and the complete
retained Postnikov theorem proof is unchanged. Interface landing:
20261024T221548-L-1239662. tools/lean_file.sh compiled the definition and Postnikov
modules separately (1.5 s and 5.4 s, standard 60-second limit); definition metadata,
incremental DAG and import checks passed.

The old deliver2.py:141 blocker is resolved by the current base. Postnikov now
already cites def-zl-fixed-pair-truncation-cohomology-functors. Its dependency
stmt_deps no longer needs to change in this delivery. The four shared extraction
copies were backed up with .maint-Q26-fixed-pair-1792879058.bak suffixes and removed
from the active sandbox packet. Keep only this item's node, its module, and this
report. Keep its direct definition citation and the direct IsTExact heart-membership
proof. The subsequent return below restores the original proof_deps exactly.

Continue with the normal deliver2.py dry-run and delivery for independent review.
Do not recreate the old copies or report BLOCKED merely because the wrapper still
contains its dependency-field guard. That guard no longer drops a requested delta.
The reviewer return remains the record for reviewing this item's repaired statement.
No launcher, review, preflight, landing tool or concurrency setting was changed.

## Worker report

Item: lem-zl-texact-fixed-pair-heart-cohomology. The new module is
Sheaf.CategoryTheory.Triangulated.TExactFixedPairHeartCohomology. It contains three
statements with `sorry` (main statement, composition/identity coherence, natural-isomorphism
coherence) and seven concrete helper definitions/abbreviations belonging to the same
fixed-pair-heart construction. No data is postponed. All ten declarations are recorded in
`lean.declarations`. The node's statement and twelve-step proof are unchanged.

Sources read: the node and all its statement and proof dependencies; BBD 1.3.3,
1.3.4–1.3.6, and 1.3.16–1.3.17 (local PDF, PDF pages 30–42, printed pp. 29–41);
the current blueprint at literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-prop-wgen-relative-line/lem-zl-morphism-open-closed-reduction.proof.md, especially
Restriction and Part 2 sheaf form. The source proof has moved to a different unit directory
since the node's original source record. Its cited cohomology and exactness assertions remain.
The node is an auxiliary fixed-pair assembly, as its source and proof_origin explicitly say,
not a claim that BBD states this assembly verbatim.

Hypotheses, individually:

- Arbitrary triangulated C,D: independent object/morphism universes uC,vC,uD,vD,
  `Category`, `Preadditive`, `HasZeroObject`, integer `HasShift`, additive shifts,
  `Pretriangulated`, and `IsTriangulated`. These are precisely the recorded
  def-weil-triangulated-category Mathlib encoding; no completeness assumption.
- Bounded t-structures: `tC : TStructure C`, `tD : TStructure D`, and
  `_hC : tC.bounded = ⊤`, `_hD : tD.bounded = ⊤`, as specified by
  def-weil-t-structure.mathlib_match. Their hearts are the full heart subcategories
  with the upstream abelianHeartFullSubcategory instance, not additional hypotheses.
- Exact autoequivalences: `P : C ≌ C`, `Q : D ≌ D`, their `functor.CommShift ℤ`
  and `functor.IsTriangulated` instances. Equivalences supply actual quasi-inverses.
- Both halves preserved by P, inverse P, Q, inverse Q: the four `IsTExact`
  instances in the statement. This expresses every integer translate; preservation
  at zero and coherent shifts imply precisely these instances, so it adds no
  mathematical restriction to the node's preservation hypothesis.
- F exact and preserving both halves, with its shift comparison: `F : C ⥤ D`,
  `[F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD]`.
- Intertwiner QF ≅ FP: `α : F ⋙ Q.functor ≅ P.functor ⋙ F`, since Lean's
  functor composition is left to right. Shift compatibility is `[α.hom.CommShift ℤ]`.
- Equivariant arrows use the recorded `IsoAlgebra` category; its algebra hom condition
  is `P.map u ≫ θ' = θ ≫ u`, exactly the node's uθ = θ'P(u).

Conclusions, individually:

1. The lift is the existing `IsoAlgebra.mapOfNatIso α`. The first two conjuncts
   specify its structure `α.app K.carrier ≪≫ F.mapIso K.str` and its map
   `F.map u.hom.f`. Thus it is the specified rule, already a genuine functor.
2. The `∀ m, ∃ e` truncLE and truncGE conjuncts give natural isomorphisms between
   the lifted functor followed by the target truncation and the source truncation
   followed by the lifted functor. Their carriers are exactly the inverses of
   `F.eTruncLTIso ... (m+1)` and `F.eTruncGEIso ... m`, not arbitrary isomorphisms.
   The truncation lifts themselves are the landed `fixedPairTruncLE/GE`.
3. The `∀ a, ∃ e` cohomology conjunct gives the requested natural isomorphism
   F-tilde followed by target H^a ≅ source H^a followed by F-tilde. The two final
   membership conjuncts put all these cohomology objects in their respective hearts.
   `fixedPairCohomology` is the already recorded `(τ≥a τ≤a K)[a]` construction.
4. Its carrier is exactly `(fixedPairCohomologyCarrierComparison ...).inv`.
   That helper abbreviates `(truncationCohomologyComparison tC tD F a).app K`,
   owned by def-per-truncation-cohomology-comparison. Its explicit canonical composite
   commutes F with the shift, applies the lower comparison at the upper truncation,
   and applies the lower truncation to the upper comparison. Its inverse is precisely
   proof step 2's e_F inverse; no second construction of this comparison remains.
5. Intertwining the α,θ structures is part of the type of each component of e:
   it is an `IsoAlgebra` arrow, whose hom condition is the equivariance square.
   Naturality in every equivariant arrow is part of `e` being a natural isomorphism,
   and therefore holds simultaneously, not as unrelated objectwise choices.
6. `texact_fixedPair_cohomology_composition` gives the lifted composite comparison
   with identity carrier and states e_GF = G(e_F);e_G for the canonical comparisons,
   plus the identity equation. The composite intertwiner explicitly inserts functor
   associators and has carrier β_FK followed by G(α_K). A third triangulated category
   has its own independent object/morphism universes, bounded t-structure, and the
   same exactness/preservation hypotheses for its autoequivalence and G. These are
   the node's “such functors” quantified explicitly. Faithful forgetting transfers
   the displayed carrier equation to the lifted cohomology comparisons and inverses.
7. `texact_fixedPair_cohomology_natIso` quantifies another such F', α' and a
   shift-compatible `η : F ≅ F'`. The equation `_hη` is exactly compatibility with
   the intertwiners. It asserts a lifted natural isomorphism with carrier η and the
   square η_H;e_F' = e_F;H(η) for the canonical comparisons. Inverting gives the
   corresponding square in the main comparison's direction. Faithfulness makes
   the carrier square an equality of arrows of fixed pairs.
8. `fixedPairHeart t P` is only an abbreviation for the full subcategory of
   `IsoAlgebra P` cut out by `t.heart.inverseImage (IsoAlgebra.forget P)`.
   Thus A^P and B^Q are literally the node's full subcategories. The two `Nonempty
   (Abelian ...)` conjuncts assert their abelian structures, with their inherited
   category structures. No arbitrary abelian structure is chosen as data by a def.
9. `fixedPairHeartForget` forgets to the actual full ordinary heart. For every
   arrow, the main theorem asserts `CreatesLimit (parallelPair u 0)` and
   `CreatesColimit (parallelPair u 0)` for each forgetful functor. These are the
   universal creation assertions for kernels and cokernels, including equivariant
   unique factorization, rather than merely existence of carrier objects.
10. For each ordinary heart kernel fork c and its IsLimit, the next clauses assert
    a unique isomorphism κ with κ.hom;c.ι = P(c.ι);θ_A and inverse equation
    κ.inv;P(c.ι) = c.ι;θ_A.inv, for P and for Q separately. These identify the
    induced structure and its inverse under kernel preservation, on every choice
    of ordinary kernel. The equations and monicity identify them with the created
    kernel structures. The carrier is c.pt.obj, not an arbitrary replacement.
11. The dual clauses quantify every ordinary cokernel cofork and IsColimit,
    with unique γ satisfying P(c.π);γ.hom = θ_B;c.π and
    c.π;γ.inv = θ_B.inv;P(c.π). They give the analogous projection equation
    and inverse induced from θ_B.inv, separately for both hearts.
12. `fixedPairHeartMap` is a real full-subcategory lift of the same existing
    `mapOfNatIso α`, not a newly chosen functor. Its preservation of finite limits
    and colimits gives preservation of both kernel and cokernel maps and exactness
    on these abelian hearts. Since its underlying map of every arrow is F.map and
    its structure is F(θ)α, this includes the specified transported kernel/cokernel
    structures: uniqueness in clauses 10–11 identifies them. Preservation is stated
    for the restricted functor itself, not merely for a composite forgetting structure.
13. There is no `Pretriangulated` or `IsTriangulated` assumption/conclusion on
    either IsoAlgebra category, and no assertion of triangles in those categories.

Dependency declarations read and used:

- Mathlib.CategoryTheory.Triangulated.Pretriangulated / .Triangulated / .Functor:
  `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`,
  `Functor.IsTriangulated`, and the exact-functor additive instance.
- Mathlib.CategoryTheory.Triangulated.TStructure.Basic / .Heart / .TruncLTGE:
  `TStructure`, `bounded`, `heart`, `truncLT`, `truncGE`, their unit/counit maps.
- WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra:
  recorded `Endofunctor.IsoAlgebra`, `IsoAlgebra.forget`, `carrier`, `str`,
  `mapOfNatIso`, its object/structure/map formulas and `mapOfNatIsoHom`.
- Mathlib.CategoryTheory.Abelian.Basic: `CategoryTheory.Abelian`.
- WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology (the recorded
  heart-short-exact-triangles module, importing ShortExact): `homology₀`,
  `abelianHeartFullSubcategory`, `shortExact_iff_exists_distTriang`, the kernel and
  cokernel fork theorems, and the recorded isHomological_homology₀ signature/docstring.
- Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison:
  `texact_truncation_comparison`, with its entire normalization/uniqueness/naturality/
  composition signature. Its upstream construction is in
  WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject:
  `Functor.IsTExact`, `eTruncLTIso`, `eTruncGEIso`, `eTruncGELTIsoApp`.
- Sheaf.CategoryTheory.Triangulated.FixedPairPostnikovIdentifications:
  `fixedPair_postnikov_identifications` (complete signature/docstring); DAG proof dependency.
  Its four formerly bundled definitions have been extracted without changing their bodies.
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology:
  `Functor.preservesHomologyOfExact`, `PreservesHomology.preservesKernel` and
  `.preservesCokernel`, the recorded exact-abelian-functor dependency. Proof-only import.
- The fixedPairHeartMap membership proof directly applies Functor.IsTExact.isLE_obj
  and isGE_obj to the carrier's two heart properties. It does not import or use
  TExactCohomologyBoundaryComparison or texactHeartRestriction.
- Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting:
  `truncationCohomologyComparison`, owned by def-per-truncation-cohomology-comparison,
  supplies the canonical component through the helper abbreviation.
- Sheaf.CategoryTheory.Triangulated.FixedPairTruncationCohomologyFunctors now owns
  fixedPairShift, fixedPairTruncLE, fixedPairTruncGE and fixedPairCohomology. The item
  cites def-zl-fixed-pair-truncation-cohomology-functors instead of either theorem node.
  Postnikov remains an original proof dependency. The boundary comparison node is
  absent from both dependency lists, restoring the base proof_deps exactly.
- WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor: the existing
  additive IsoAlgebra and full-subcategory structures, including the general
  `IsoAlgebra.abelian` instance. Its ordinary abelian-category theorem does not by
  itself state the t-structure/cohomology/coherence assertion of this item.

Edge cases checked before writing: identity P,Q and F give the usual endomorphism
with invertible structure and identity comparison; a = 0 and arbitrary positive/negative
integers use the same truncLT(a+1), truncGE(a), shift(a) formula. Zero functors and
zero objects are admitted: every structure remains the canonical isomorphism of zero
objects. For u=0, the ordinary kernel is A and cokernel B; the displayed equations
force their original structures. For u=id, the zero kernel/cokernel structures are
unique, including their inverses. No infinite limits/colimits or Grothendieck hypotheses
are assumed, so a bounded derived category of finite-dimensional vector spaces is
included. C,D,E have independent object and morphism universes; no size equality is
imposed. No case needs a nonempty index type or a nonzero object.

Searches actually run (recorded by msearch.py in this item's searches.jsonl):

- LeanFinder: “A t-exact triangulated functor commuting with autoequivalences induces
  an exact functor of fixed-pair hearts and commutes with cohomology”: eight hits,
  generic homological/triangulated functor results, no exact statement of this node.
- LeanSearch: “t-exact functor on a triangulated category induces an exact functor
  on its heart”: eight hits, exactFunctor and generic homological/triangulated functors,
  no fixed-pair cohomology/coherence theorem.
- Loogle: “Functor.IsTExact, Endofunctor.IsoAlgebra, Functor.CommShift”: no hits,
  diagnostic unknown identifier Functor.IsTExact (upstream, not in Mathlib's index).
  Follow-up “CategoryTheory.Endofunctor.Algebra”: twelve exact algebra API hits;
  these permit arbitrary structure maps and do not state the present theorem.
- msearch grep “IsoAlgebra|eHomology|mapHeart”, CategoryTheory: two irrelevant
  resolution import matches. Follow-up “t-exact|t-structure|preservesHomologyOfExact”,
  CategoryTheory/Triangulated: t-structure core/truncation results, no fixed-pair theorem.
- rg on lean/WeilConjectures and lean/Sheaf for IsoAlgebra, eHomology, mapHeart,
  fixedPairHeart and related heart-fixed-pair patterns: existing algebra transport,
  generic abelian IsoAlgebra, landed Postnikov lifts and boundary comparison module.
  These are reused; none states all this item's conclusions. Searching this item id
  under lean/WeilConjectures returned no declaration.
- rg on Mathlib, lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for all newly introduced name stems found no existing declaration with those names.

No statement fault or STATEMENT-DISPUTED claim. The returned delivery now includes
one extracted definition node and one dependency-module repair as detailed below. All helper data is composition, full-subcategory restriction,
or canonical existing comparison data; there is no Nonempty choice of a construction.
The only local instances are real t-exactness proofs inside the composite and identity
definition bodies; they introduce no file-local statement notation or instance.

Validation: prescribed scompile.py, on the server, compiled both the sandbox and
actual library module names cleanly. Initial expanded compile found an identity-functor
instance elaboration issue; repaired it by passing the source `IsLE`/`IsGE` instances
explicitly. The final compile took 2.3 s and 2.2 s respectively and had no warnings/errors.
Only three whole-theorem `sorry` proofs remain. Every variable/universe is bound,
autoImplicit is explicitly false, and every Lean line is at most 100 characters.

## Second reading by Q26

This is a second pass by the same assigned worker, not a claim of an independent
agent review; the dispatch brief forbids starting other agents and assigns independent
review to the maintainer after delivery. I reopened the node and full module, checking
each hypothesis and conclusion against the correspondences above.

The first draft was missing the explicit kernel/cokernel inverse equations and the
composition/natural-isomorphism coherence clauses. These were added before delivery.
The comparison direction is H^a(FK) → F(H^aK); its carrier is e_F.inv, while the
composition and naturality equations are written for e_F.hom and hence imply the inverse
equations. In Lean composition order the kernel equation is κ;k = P(k);θ_A and the
cokernel equation is P(q);γ = θ_B;q; both match the node. The inverse equations also
have the required domains, not just isomorphism inverse identities. Both P and Q have
all four creation/structure clauses, and F's preservation is on its actual heart lift.

I checked that the full-heart predicate uses the carrier of the recorded IsoAlgebra,
that all a are integers, that third-category universes remain independent, and that
composition uses the canonical comparisons of the composite (not a definition setting
that comparison equal to the desired composite). Its only extra construction data is
the induced proof that the composite is t-exact. No hypothesis excluding incomplete
hearts was introduced. Existing generic abelian IsoAlgebra and heart restriction
constructions are reused. The module does not assert a triangulation on fixed pairs.
No further mathematical mismatch found in this reading.

## Return repair: H2 on immutable head b7231942c778

The only mandatory return point concerns definition ownership. Compared the retained
sandbox with the unchanged live item (no landed Lean record) and read the current server
Postnikov source through scompile.py --source. The live Postnikov source still contains
all four definitions; no later extraction is present.

1. Extracted fixedPairShift, fixedPairTruncLE, fixedPairTruncGE and fixedPairCohomology,
   preserving their full names, binders, types and bodies, into a new definition module.
   Its owner is def-zl-fixed-pair-truncation-cohomology-functors. The new definition
   node cites the three existing ambient definition nodes, not a theorem for plain data.
2. The main item publicly imports that definition module and directly cites its node.
   Removed lem-pod-fixed-pair-postnikov-identifications and
   lem-zl-texact-cohomology-boundary-comparison from stmt_deps. The first H2 repair
   added the latter to proof_deps; return 47a288ca4b66 below reverses that addition
   and restores the base proof_deps exactly. Neither theorem module is now imported.
3. Replaced texactHeartRestriction in the membership proof of fixedPairHeartMap by
   two direct applications of F.IsTExact to the source carrier's IsLE/IsGE instances.
   This is the property proof inside a full-subcategory lift, not a duplicate functor
   or an additional postponed theorem. No mathematical statement changed.
4. Included the Postnikov dependency module with a public import of the new definition
   module and no local copies of those definitions. Its theorem signature and proof
   docstring are unchanged. Its lean.declarations now names only its theorem, with
   lean.note recording the extraction and the new owning definition node. Added the
   definition node to its stmt_deps in the sandbox, as the return explicitly requests.

The advisory concerning Nonempty Abelian was not a mandatory correction, and the
reviewer expressly found the other hypotheses/conclusions sound. These statements
are preserved exactly, including all inverse and coherence equations. The only new
mathematical node is a definition with real functor data and no sorry.

## New nodes

def-zl-fixed-pair-truncation-cohomology-functors: owns the canonical lifted shift,
upper/lower truncation, and their shifted double-truncation cohomology composite.
Source: BBD Proposition 1.3.3 and paragraphs 1.3.4–1.3.5, printed pp. 29–31, transported
through the existing IsoAlgebra.mapOfNatIso construction. The statement introduces C,t,P,
the coherent shift comparison and canonical truncation comparisons, and gives the object
and arrow formulas of all four functors. The module contains exactly the four existing
abbreviations extracted unchanged; no statement of Postnikov identifications is included.

New searches run for this repair: LeanSearch query “Lift truncation and shifted cohomology
functors to pairs with an invertible endofunctor structure using t-exact truncation
comparisons” returned eight results about ordinary truncation/complexes, with no fixed-pair
construction. LeanFinder query “Canonical shift truncation and cohomology functors on the
category of fixed pairs for a t-exact endofunctor” returned eight results about homological
functors and ordinary truncations, with no fixed-pair construction. msearch grep query
“fixedPairShift|fixedPairTruncLE|fixedPairTruncGE|fixedPairCohomology” in CategoryTheory
returned zero Mathlib hits. rg of WeilConjectures and Sheaf found exactly the four
existing declarations in the Postnikov module; these are moved, never redefined in parallel.
The node mathlib_searches entries preserve the actual logged queries, hits and UTC dates.

Searched the entire DAG for those declaration names and fixed-pair functor notions; no
definition node owns them. blueprint_refs.py search “fixed pair” found five geometric
Weil-category/mixedness/Fourier nodes, none defining these abstract functors.
blueprint_refs.py ancestor identifies lem-zl-morphism-open-closed-reduction as the nearest
blueprint ancestor; the new node's from.place and via record its restriction/cohomology use.
The new definition lies in the assigned item's chapter, using its zl prefix and unit.

Clause matching for the definition: fixedPairShift supplies (K[r], θ[r]s) and u[r];
fixedPairTruncLE uses mapOfNatIso of eTruncLTIso at m+1 and supplies τ≤m(θ)c⁻ and τ≤m(u);
fixedPairTruncGE similarly uses eTruncGEIso at m; fixedPairCohomology is their literal
composite with shift i, supplying (τ≥iτ≤i K)[i] and the same composite on arrows.
The exact/t-exact assumptions are precisely those in the existing abbreviations.
No boundedness or autoequivalence assumption is added to their general construction.
All four expose their real data and use upstream transport functor laws.

Edge checks for the extracted definitions: m,i,r range over all integers, including zero
and negative degrees; identity P and zero objects are permitted. P need not be an
equivalence and t need not be bounded. The object/morphism universes u,v remain independent.
No triangulated structure on IsoAlgebra is introduced. The new module imports only the
upstream algebra and t-exact comparison constructions, never either repaired consumer.

## Dependency modules

lem-pod-fixed-pair-postnikov-identifications: the prior module bundled four plain
functor definitions with its theorem and its lean record named those definitions without
a definition node owning them. Per the explicit return, those definitions now belong
to def-zl-fixed-pair-truncation-cohomology-functors. The repaired existing module imports
their owner and keeps exactly the same Postnikov theorem and its full proof docstring.
The theorem still includes shifts, underlying-map identities, cohomology membership and
structure formula, both absorption isomorphisms and both double-truncation identifications.
No hypotheses or conclusions changed. The only module changes are extraction, import
visibility, and explanatory ownership text. Its lean.note explains the previous problem.

## Second reading by Q26: returned H2 repair

Same assigned worker's second pass; no additional agent was started. Checked every
return instruction against the three module files and three node records. The four
functor bodies were moved unchanged, their original declarations removed, and both
consumers import the single owning module. The main statement's full signature is
unchanged. fixedPairHeartMap's property proof takes K.property.1/.2 to build source
IsLE/IsGE instances and invokes F.IsTExact at degree zero, retaining the original
object and morphism formulas. The item cites the definition node in stmt_deps and
keeps Postnikov among the original proof dependencies (the later return removes
the added boundary-comparison proof dependency). The Postnikov signature uses
the imported four functors and its record names only its theorem. All original
edge-case and universe checks continue to hold. There are no new theorem sorries.

Repair validation: scompile.py compiled every delivered module separately in dependency
order, against the live published server build. All six sandbox/library passes were
clean: definition module, Postnikov module, main consumer module. The live Postnikov
consumer compiled in the private overlay with the extracted definition owner, validating
that the moved declarations remain usable under their original full names. No duplicate
name diagnostic or other warning occurred. The main statement signature remains verbatim
identical to the returned head, and no target or source mathematical statement changed.

Dry-run record repair: the preflight extracts signatures beginning at the keyword
`abbrev` (excluding `noncomputable`); the new definition's lean.statement now follows
that exact parser format. This metadata correction does not change Lean source.

## Maintenance resolution and final validation

Maintenance landed def-zl-fixed-pair-truncation-cohomology-functors and the
Postnikov dependency repair upstream, including its required stmt_deps citation.
The four definition bodies retain their original names and data. The completed
upstream Postnikov proof and its helpers are preserved. The maintainer removed
these already-landed files from this sandbox's active delivery set, retaining
backups; the item now imports their published modules.

The earlier module and new-node descriptions document the H2 repair now owned
upstream. This delivery supplies the main item module and its node record: it
cites the definition owner, removes both theorem nodes from statement dependencies,
restores the base proof dependencies in the subsequent return repair below, and
proves fixedPairHeartMap's heart membership
directly from F.IsTExact. No mathematical theorem statement changed.

The dry run at 8616e996e07 first passed without a field-discard warning.
After maintenance removed the already-landed modules from the sandbox, the
standalone compile exposed the older compiled Postnikov module's duplicate
fixedPairShift declaration. Removed the unused Postnikov proof import from the
item; retained its DAG proof dependency as required. Its theorem is not used by
the statement or current proof bodies. The main module imports the published
owning definition module and compiles cleanly in both sandbox and library passes.
The wrapper blocker is resolved by upstream maintenance. Launcher files were
never modified or bypassed by this worker.


## Repair of return 47a288ca4b66

1. H7/H2(b): restored proof_deps verbatim from the current base node, including its
   order (seven entries). Removed the unapproved addition
   lem-zl-texact-cohomology-boundary-comparison and its unused Lean import. The
   mathematical statement, proof text, and proof_origin remain unchanged; no
   statement_change is needed or introduced.
2. H4: read the complete signature and docstring of the landed
   CategoryTheory.Triangulated.TStructure.truncationCohomologyComparison in
   Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting, together with its
   owning definition node def-per-truncation-cohomology-comparison. Added that node
   to stmt_deps and publicly imported the module. The helper
   fixedPairCohomologyCarrierComparison is now a noncomputable abbrev whose entire
   body is `(truncationCohomologyComparison tC tD F a).app K`. Its signature and
   comparison direction are unchanged, and the three theorem signatures remain
   verbatim identical to the returned delivery. The explicit composite now has one
   definition owner. Search: rg for truncationCohomologyComparison in the owning
   module found its definition at line 85; the recorded definition node matches it.

The existing checks of degree zero and negative degrees, identity endofunctors,
zero functor and zero/identity arrows, boundedness and independent universes still
apply. The canonical comparison requires exactly the existing CommShift,
IsTriangulated and IsTExact assumptions; the abbreviation adds no assumptions.


Repair validation (2026-10-24 UTC): scompile.py compiled both active packet files
separately in dependency order, in sandbox and library passes, without errors or
warnings. The Postnikov file and its node are byte-for-byte current-base compile
companions, preserving the upstream completed proof and producing no delivery delta.
The main item node differs from its base outside lean only in stmt_deps (the two
landed definition owners); proof_deps is exactly the original seven-entry array.
The recorded main theorem signature matches the Lean file verbatim.
