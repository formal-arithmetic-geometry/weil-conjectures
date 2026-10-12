## What changed

Replaced the sorry of AlgebraicGeometry.Etale.etale_limit_acyclic_replacement with a
complete proof from two strictly smaller construction/vanishing statements. Its original
signature and public imports are unchanged. Added proof-only imports of
EtaleLimitReplacementExactSystems and EtaleLimitInjectiveColimitAcyclic, and kept
PullbackCohomologyLongExactLadder. Updated the parent node to the actual proof route.

The construction supplies stage short exact sequences and actual limit short complexes,
including canonical morphisms from the pulled-back stage sequences. The vanishing lemma
applies independently to any compatible system whose stage sheaves are injective.
The item defines both boundaries using the existing Sheaf.H.δSucc. The pullback ladder
identifies the first boundary comparison, and Sheaf.H.map_δSucc proves the remaining
square. The displayed hbeta equality is proved elementwise from these two naturality
identities. No cohomology diagram or surjectivity claim is added.

The theorem-local unusedVariables linter setting suppresses warnings on the existing
existential proof binders hidentityR, hcompositionR, hGR and hLR; their binder names,
types and visibility remain unchanged. All three delivered files compile cleanly through
lcompile.py --all. No data definition or existing dependency was changed.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Etale.etale_limit_acyclic_replacement
(lem-weil-pbc-etale-limit-acyclic-replacement), with no sorry in its proof.

Added two holes, each the whole proof of a public theorem in a separate module:

- AlgebraicGeometry.Etale.etale_limit_replacement_exact_systems:
  lem-weil-pbc-etale-limit-replacement-exact-systems, in
  Sheaf.AlgebraicGeometry.EtaleLimitReplacementExactSystems.
- AlgebraicGeometry.Etale.etale_limit_injective_colimit_acyclic:
  lem-weil-pbc-etale-limit-injective-colimit-acyclic, in
  Sheaf.AlgebraicGeometry.EtaleLimitInjectiveColimitAcyclic.

This is a decomposition (one original hole closed, two lower holes added), not a
sorry-free proof of the whole mathematical result. The boundary construction and its
canonical comparison square are proved, without a third naturality hole. No sorry
remains in the item's module. Existing dependency holes are not changed.

## No longer needed

Removed these direct proof imports from the item:

- Sheaf.Paper.ColimitSitesInjectiveSystem
- Sheaf.CategoryTheory.SitePullbackAbelianExact
- Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
- Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
- Sheaf.AlgebraicGeometry.LimitAffineTransition
- Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings
- Sheaf.CategoryTheory.SiteInjectiveCechAcyclic
- Sheaf.CategoryTheory.SiteCechVanishingCriterion
- Sheaf.CategoryTheory.ColimitSiteSections
- WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

The two removed upstream imports are already provided by the retained public
TopologicalInvariance import. The old direct proof dependencies moved to the lower
construction/vanishing nodes (and not globally pruned) are:

- lem-weil-pbc-colimit-of-sites-injective-system
- lem-weil-pbc-inverse-image-composition
- lem-weil-pbc-site-pullback-abelian-exact
- lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact
- lem-weil-pbc-affine-etale-site-colimit
- lem-weil-pbc-affine-etale-site-topos
- lem-weil-pbc-limit-affine-transition
- lem-weil-pbc-etale-qcqs-cofinal-finite-coverings
- lem-weil-pbc-site-injective-cech-acyclic
- lem-weil-pbc-filtered-colimit-abelian-groups-exact
- lem-weil-pbc-site-cech-vanishing-criterion
- lem-weil-pbc-colimit-of-sites-sections
- lem-weil-pbc-filtered-colimits-commute-finite-limits
- lem-weil-pbc-pretopology-sheaf-condition

These modules and their nodes remain needed by the two lower arguments and are imported
by their corresponding new modules. None is claimed globally pruned. No unit statement
or realized unit step is bypassed; the original injective-system/Cech route is retained.
No mathematical node or module is newly unnecessary. The generic
Sheaf.CategoryTheory.ColimitSitesAcyclicReplacement was inspected but is not imported:
its site strictification, sheaf equivalence, and H-prime interfaces do not directly match
the scheme-specific statement.

## Where the brief, the DAG or earlier work was wrong

No original statement is changed or disputed. The generic site construction needs
explicit scheme inverse-image transport, and the stage-cokernel and limit short-complex
maps are not outputs of exists_compatible_injective_system. These are included in the
construction statement rather than silently assuming them. In particular the compatibility
needed by hbeta is supplied as an actual morphism of short complexes with prescribed
first and third components.

The current ColimitSiteSections theorem evaluates a diagram of sheaves already on the
limit site. Its signature alone does not provide the entire original-stage section
formula of 09YN; inverse-image units and the affine-site translations must still be
assembled in the vanishing argument. The new vanishing docstring explicitly includes
this step and eventual equality. No higher-degree continuity is used, preventing a
cycle with the parent continuity theorem.

SiteInjectiveCechAcyclic currently carries a dispute for independent category/value
universes. Here the scheme small etale objects and the coefficients both have the
required u+1 size. Its over-general signature should still be repaired by its holder;
this delivery does not adapt it or claim its disputed independent-universe version.

The ancestry helper returned None for the parent because created.item is a module name.
The new nodes preserve its explicitly recorded blueprint ancestor
lemma-weil-pbc-injective-restriction-acyclicity and extend its recorded via chain.
Blueprint searches for 0EXZ, 09YP and injective/acyclic replacement found no duplicate
blueprint node. No contract/tool files are changed.

Read the Stacks source pages 0EXZ, 09YP, 09YN and 09YQ, and the signatures of the existing
construction, exactness, affine-site, Cech and ladder dependencies. LeanFinder found
only affine-transition structure-sheaf/spreading-out results. Loogle found extension-class
naturality and Ext exactness, used through the already proved Sheaf.H.map_δSucc.
LeanSearch returned Internal Server Error and is recorded as unavailable. Local rg
found no existing scheme replacement or general injective-system colimit vanishing
statement with these interfaces.

Small cases checked mathematically: the zero coefficient system can use zero injectives
and zero cokernels; on an empty scheme all the cohomology groups vanish; for a singleton
index the construction is an ordinary injective embedding and its cokernel, and
vanishing is ordinary injective acyclicity. The n=0 case uses the same genuine degree-one
boundary and does not assert degree-zero vanishing. Nonempty excludes an empty index.

## New nodes

lem-weil-pbc-etale-limit-replacement-exact-systems isolates the construction and exactness
parts of 0EXZ/09YP with the canonical stage-to-limit short-complex morphisms. It has no
cohomology or acyclicity conclusion. Its witnesses are destructured only in a theorem
proof; no definition chooses arbitrary data from its unproved existence assertion.

lem-weil-pbc-etale-limit-injective-colimit-acyclic isolates the positive-cohomology
vanishing step of 09YP/09YQ for any compatible injective coefficient system. It does not
construct a replacement, cokernels or boundary maps. Both nodes inherit the parent's
chapter and unit and have full proof docstrings, statements and search records.

No change records or forced adaptations are needed.

## Second reading by T3

1. **Interface: pass.** Compared the parent module with the read-only repository using
   diff, and checked its complete theorem signature byte for byte. The only differences
   are proof imports, a declaration-local unused-variable linter setting, and the proof.
   There are no existing definition or statement changes, forced adaptations, or change
   records. Both new declarations have their own modules and matching new nodes.
2. **Proof and axioms: pass, with the reported lower holes.** Read the proof from its
   construction witnesses through vanishing and both boundary naturality identities.
   The first and third components of the supplied short-complex morphism are exactly
   the comparison maps used in the conclusion. The limit boundary formula is definitional;
   pullback naturality comes from the proved ladder and coefficient naturality from
   the proved upstream Sheaf.H.map_δSucc. There are exactly two delivered sorries, each
   a whole named public theorem, and no data definitions or prohibited declarations.
   Local compilation and explicit #print axioms checks are recorded below.
3. **Split statements: pass as decomposition.** Independently read Stacks 0EXZ, 09YP,
   09YN and 09YQ. Construction is the compatible product-of-direct-images injective
   embedding, its actual cokernels, and exact filtered colimits with canonical legs.
   Vanishing is independently true for any compatible system of stage injectives;
   section continuity and finite-cover Cech complexes prove it without higher-degree
   continuity. Zero systems, empty schemes, a singleton index, and n=0 introduce no
   missing hypothesis. Only positive-degree vanishing is asserted. Neither lower
   theorem restates the item. Each has a source, proof docstring and node. Witnesses
   are eliminated inside a proposition proof; no definition selects arbitrary data
   from either unproved existence assertion.
   Independent LeanFinder search for inverse-system injective sheaf acyclicity returned
   affine-transition/global-structure-sheaf results, not these statements. Loogle
   queries for Sheaf.H.map_δSucc and Injective/Sheaf reported unknown identifiers, so
   the upstream sources were read directly instead. msearch grep for injective/colimit
   and repository rg found the generic site replacement and fixed-scheme injective
   colimit results; neither supplies this changing-scheme interface. The affine
   comparison theorem depends back on class descent and this replacement, so it is
   not a shorter noncircular route. Neither lower hole can be closed by a short
   application of the currently available interfaces.
4. **Route and pruning: pass after report repair.** Read the generic site replacement,
   construction dependency, pullback ladder, and the sk-thm-p1 unit's realized fields.
   The injective-system/finite-cover Cech route is retained below the fixed unit route;
   no realized unit node is removed. The original proof-dependency nodes moved to the
   two lower arguments are now all explicitly listed under No longer needed, distinct
   from global pruning. The two redundant upstream imports removed from the parent
   are now listed there too. All newly added proof imports are plain imports.
5. **DAG: pass.** Checked all three Lean statement records against their declarations,
   the union of each proof step's uses against proof_deps, and the new-node source,
   creation, search, blueprint ancestry, chapter/unit and Lean records. The existing
   node changes only proof, proof_deps and proof_origin. Its boundary step names the
   actual ladder and upstream Ext-cohomology naturality nodes. The unit record is
   unchanged. The lower nodes retain the original construction and vanishing route.

Second reading changed only report completeness: added the two omitted removed upstream
imports, explicitly enumerated every old direct proof-dependency node moved to the lower
arguments, and added this independent review. No mathematical statement or Lean proof
was changed. One original hole is closed and two are added: decomposition, net minus one
hole closed, with no globally pruned module.

Validation: deliver3.py --no-push printed OK (dry run), with all three delivered modules
compiling cleanly and preflight passing (CODEX: new nodes and statement modules).
Explicit #print axioms on each of the three declarations, from an import-only scratch
module compiled through lcompile.py against that compiled set, printed exactly propext,
Classical.choice, Quot.sound and sorryAx. This agrees with the two named lower holes.
Some earlier parent compilation attempts hit 60 seconds on this loaded machine;
a single-file retry compiled in 43.6 seconds and the complete dry-run compile passed
without changing Lean or compiler settings. Scratch probes are removed from the sandbox.
