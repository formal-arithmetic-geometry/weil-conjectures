## What changed

Repair of reviewer X-9989a (head 9989a2e9a): added the sourced public theorem
`ModuleSheafConstantRingEquivalence` with Λ : Type (u+1), X : Scheme.{u}, and a
natural isomorphism of the underlying-abelian forgetful functors. The constant
ring is explicitly the CommRingCat constant sheaf followed by forget-to-RingCat;
it is not an arbitrary ring sheaf or an extra hypothesis. Added its node to
acyclicity proof step 0 and proof_deps and cited it in the declaration docstring.
Replaced proof step 2 uses with the exact five ids requested and added the
Ext comparison and derived-single identification to proof_deps. The docstring
now explains terminal evaluation, derived-global-section identification, and
Ext/Sheaf.H identification in that order.

Repaired reviewer X-a10b8's points D1/D2 and 6. Removed the returned module
`Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclicComparison` and its node
`lem-weil-pbc-affine-closed-injective-acyclic-comparison` from this delivery.
The replacement `AffineClosedEtaleNeighborhoodComparison` compares closed-fibre
cohomology with a filtered colimit of etale-neighborhood cohomology. It has no
injectivity hypothesis, applies in degree zero, and does not identify any group
with zero. `InjectiveModuleSheafHCohomology` states acyclicity on the injective's
own site, without a closed immersion, affine hypothesis, or torsion assumption.

The assigned theorem now explicitly proves each diagram value zero: install the
etale property of the neighborhood map, apply the existing etale preservation of
injectives theorem, then apply underlying-abelian acyclicity and transport across
the object isomorphism. `Functor.isZero_iff` and `IsColimit.isZero_pt` prove the
colimit zero. Transport along the closed-fibre comparison finishes the original
conclusion. The assigned theorem's signature is unchanged.

Updated the existing affine node's `proof`, `proof_deps`, and `proof_origin` to
record precisely this Lean proof. Added no changes to existing statements or
definitions. The two public imports of the assigned module are retained; the
three new proof imports are private to its module.

## Proved and sorry left

`AlgebraicGeometry.Etale.subsingleton_H_affine_closed_of_injective`: its one local
sorry is removed, with a compiled combination of two smaller interfaces and the
existing proved etale restriction theorem.

Three new named theorem sorries remain, each in its own module:

- `AlgebraicGeometry.Etale.affine_closed_etale_neighborhood_comparison`, node
  `lem-weil-pbc-affine-closed-etale-neighborhood-comparison`.
- `AlgebraicGeometry.Etale.subsingleton_H_underlying_of_injective_module`, node
  `lem-weil-pbc-injective-module-sheaf-H-acyclic`.

- `AlgebraicGeometry.moduleSheaf_constantRing_equivalence`, node
  `lem-weil-pbc-module-sheaf-constant-ring-equivalence`.

All three have a source and full natural-language proof in the declaration docstring.
None is the original assertion with a renamed or equivalent conclusion.

## No longer needed

Second reading also removed the redundant public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf` from the new constant-ring equivalence
module; TorsionSheaf already publicly imports Mathlib. No node is pruned by this.

Removed the import, module, and node of the rejected zero-group comparison:
`Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclicComparison` and
`lem-weil-pbc-affine-closed-injective-acyclic-comparison`.

No original mathematical ingredient is pruned: pair henselization, Gabber
comparison, continuity, inverse-image composition, and preservation of torsion
are retained as dependencies of the neighborhood comparison. Etale preservation
of injectives is used directly in the assigned Lean proof. The 03FD argument
remains in the underlying-abelian acyclicity interface. The existing module
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic` is not directly imported:
its current statement uses a SheafOfModules encoding with R : Type u and
rightDerived evaluation, whereas this item uses ModuleCat-valued sheaves with
Lambda : Type (u+1) and Sheaf.H. The new interface records the needed encoding
and universe version of the 03FD argument. This is not a claim that the existing
acyclicity node is globally pruned.

For completeness, the old direct `proof_deps` no longer used directly by the
assigned proof are:

- `lem-weil-pbc-pair-henselization`;
- `prop-weil-pbc-gabber-pair-comparison`;
- `lem-weil-pbc-inverse-image-torsion`;
- `lem-weil-pbc-inverse-image-composition`;
- `lem-weil-pbc-etale-cohomology-limit-of-schemes`;
- `lem-weil-pbc-injective-module-abelian-acyclic`.

The first five are dependencies of the new comparison node, so their mathematical
route is retained. The sixth is replaced here by
`lem-weil-pbc-injective-module-sheaf-H-acyclic` for the encoding and universe reasons
above. `lem-weil-pbc-etale-restriction-injectives` remains a direct dependency.
No existing library module is asserted to be globally unreachable or pruned.

The tentative explicit imports of `Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
and `Mathlib.Algebra.Category.Grp.Zero` were removed after compilation showed
that the used imports already expose their declarations.

## Where the brief, the DAG or earlier work was wrong

The previous delivery and its second reading incorrectly treated an isomorphism
to the trivial group as a strictly smaller intermediate statement. For an
abelian group it is equivalent to subsingleton, so it relocated the whole item.
The replacement separates a comparison which also holds for noninjective
sheaves and in degree zero from acyclicity on the injective's own site.

The earlier delivery also omitted the existing affine node update. It is now
included with a dependency union exactly matching the three steps of the
combining proof. Source checking identifies Gabber's all-degree theorem as
Stacks Tag 09ZI; Tag 09ZH is the degree-zero lemma.

Edge cases checked mathematically: q = 0 is allowed in the comparison but not
in the acyclicity theorem; no assertion that degree-zero cohomology vanishes is
made. An identity closed immersion gives the usual neighborhood comparison.
For an empty closed subscheme the pair henselization has empty spectrum and
continuity still gives the comparison. The acyclicity statement allows the zero
ring and empty scheme and does not assume the underlying abelian sheaf is
injective. Neither source requires a torsion coefficient ring: only the
underlying sheaf is torsion for Gabber comparison. The unit's realized steps are
unchanged and no unit route is bypassed.

## New nodes

`lem-weil-pbc-module-sheaf-constant-ring-equivalence` states the missing encoding
equivalence and natural additive compatibility, with explicit coefficient and
scheme universes. It is in `ModuleSheafConstantRingEquivalence.lean`, sourced
from Stacks 093I and the underlying-abelian convention of 03FD. The detailed
local-action/gluing argument is written by the worker from these definitions.

`lem-weil-pbc-affine-closed-etale-neighborhood-comparison` isolates the first two
displayed comparisons of the affine case of Stacks 0A51, using henselization,
09YQ continuity, and 09ZI Gabber comparison. Its colimit is not asserted zero.

`lem-weil-pbc-injective-module-sheaf-H-acyclic` gives the 03FD acyclicity step
in the ModuleCat/Sheaf.H encoding and coefficient universe used by this item.
It has no closed-fibre assertion. Its plan follows the free Cech complex,
injective presheaf, Cech vanishing criterion, and global cohomology comparison.

No change records: no existing definition or statement was changed.

## Earlier second reading (a previous round; superseded)

Repair check for X-9989a (performed by this repair worker; the preceding delivery's
independent second reading is superseded on the missing bridges):

1. Checked the new bridge signature against its node and docstring. Λ is in
   Type (u+1), X in Scheme.{u}, the ring sheaf uses CommRingCat.{u+1} and
   RingCat.{u+1}, and the module/abelian carriers are in universe u+1. The
   forgetful compatibility is a natural functor isomorphism, not just unrelated
   objectwise isomorphisms. No scalar ring is assumed torsion. The empty scheme
   and zero ring are allowed. The local scalar action extends along sheafification;
   restricting along its unit is inverse. Separatedness gives independence and
   the unit/counit identities. This is not acyclicity under another name.

2. Checked the exact requested five ids in acyclicity proof[2].uses. Terminal
   evaluation is global sections; derived-single identification gives the
   rightDerived/derived-global-sections comparison; the existing Ext comparison
   gives Sheaf.H. Read both cited node statements and Lean records: the derived
   identification is generic in an abelian category, and the Ext comparison is
   on AddCommGrpCat.{u+1}-valued étale sheaves on Scheme.{u}. They match the
   coefficient and site universes of this item. Both are in proof_deps, and
   the declaration docstring explains their separate applications.

3. The original assigned theorem signature and combining proof are unchanged.
   Its local sorry remains removed. The two prior split theorems and the new
   encoding bridge are the three named sorry theorems reported above. No target,
   definition, or existing statement changes. The unit route is preserved.
   Every node's proof_deps equals the union of proof step uses.

4. Compiled all four modules in import order with lcompile.py --all without
   errors or warnings. The new bridge requires ConcreteCoefficients to supply
   constant ring sheafification at the correct universe; bare constantSheaf
   elaboration without that import fails instance search. LeanSearch was attempted (Internal Server Error, recorded unavailable).
   Actual LeanFinder, Loogle and grep searches were run and recorded by msearch.py and in the node.
   No existing matching equivalence was found. This repair adds no pruning.

## Earlier second reading (a previous round; superseded)

Repair follow-up: checked the added bridge citations. The constant-ring proof now cites
`lem-weil-pbc-ring-sheafification-underlying-sets` for the underlying set-valued
sheafification and `lem-weil-pbc-site-sheafification-sections-local` for local
representatives and local equality; both statements match the local-action/gluing
argument and the stated universes. The affine-neighborhood comparison now cites
`lemma-weil-pbc-etale-pullback-forget-modules` alongside inverse-image composition;
this supplies compatibility after forgetting module coefficients at the required
universes, exactly as used to identify the closed-fibre sheaf.

1. **Unchanged public statements: pass.** Read all four modules and diffed the
   assigned module against the repository. The only differences there are three
   plain proof imports and the replacement of its `by sorry` by the combining
   proof. The existing theorem signature and docstring are byte-for-byte unchanged;
   no existing definition or target is changed. The existing node differs only
   in `proof`, `proof_deps`, and `proof_origin`. The other three declarations are new.

2. **Proof and trust check: pass as a partial delivery.** Compiled the four modules
   with `lcompile.py --all` in import order, without errors or warnings. Scratch
   copies with `#print axioms` for each of the four declarations returned precisely
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The assigned theorem
   has no local sorry; its proof still depends on the explicitly open comparison
   and injective-acyclicity interfaces. The three remaining local sorries are
   exactly the named public theorems listed above, each with a node and a proof
   docstring. No definitions, extra axioms, unsafe declarations, opaque declarations,
   implementation replacements, or extern declarations occur in the delivery.
   The diagram proof installs both the etale instance and the preserved injectivity
   before applying acyclicity; its two `of_iso` transports have the correct direction.

3. **New statements and sources: pass.** Read Stacks
   [0A51](https://stacks.math.columbia.edu/tag/0A51),
   [09ZI](https://stacks.math.columbia.edu/tag/09ZI),
   [03FD](https://stacks.math.columbia.edu/tag/03FD), and
   [093I](https://stacks.math.columbia.edu/tag/093I).
   The comparison separates the two all-degree comparisons in 0A51's affine
   argument: it requires affine X, a closed immersion, and torsion of the sheaf,
   but no injectivity. Gabber's theorem requires torsion of the abelian sheaf,
   so a torsion coefficient ring is unnecessary. The injective-acyclicity interface
   isolates the second paragraph of 03FD, on the injective's own site; it requires
   positive degree but no affine, closed-immersion, or torsion hypothesis.
   The encoding equivalence is the worker's local-action/gluing construction,
   supported by 093I's constant algebraic structures convention, rather than a
   verbatim assertion of that section. Restriction along the sheafification unit
   and extension by local scalar representatives are inverse, and the identical
   additive sheaves give the stated natural forgetful-functor isomorphism.
   Its coefficient universe and explicit constant CommRingCat sheaf match its node.
   Checked q = 0 (only the comparison applies), q = 1, the zero ring, empty scheme,
   empty closed subscheme, and identity closed immersion. None produces a false
   vanishing or an extra assumption. These three lemmas are distinct parts of the
   argument, not renamed versions of the assigned theorem.

   Ran fresh LeanFinder searches for injective-module abelian acyclicity, henselian
   continuity/closed-fibre comparison, and extension of scalar action to constant
   ring sheafification; ran Loogle for `SheafOfModules, CategoryTheory.Equivalence`
   and msearch grep for module-sheaf equivalences and henselian cohomology. Also
   searched the repository, upstream etale sources, and Mathlib's module-sheaf
   sources with rg. No exact existing statement was found. LeanFinder did locate
   `PresheafOfModules.Sheafify.module`, `smul`, and `smulCandidate`: these implement
   the local scalar-action part and should be reused when the encoding equivalence
   is proved, but do not themselves give the equivalence or its natural additive
   compatibility. The upstream restricted-injective theorem remains an open proof,
   not a shorter proved route. The existing `InjectiveModuleAbelianAcyclic` has the
   different rightDerived/ULift encoding described above.

4. **Route and pruning: pass.** Read `dag/units/sk-thm-p1.json`, including `realized`.
   No realized unit statement or step is bypassed: the reduction remains inside
   the affine ingredient of the strict-henselian argument. Pair henselization,
   Gabber comparison, continuity, torsion preservation, and inverse-image
   composition are retained in the comparison node; etale restriction of injectives
   is used directly. The report lists all six old dependencies no longer used
   directly. They are not asserted globally pruned. Removed the redundant public
   import `Mathlib.Algebra.Category.ModuleCat.Sheaf` from the new equivalence module:
   its declarations are already available through TorsionSheaf's public Mathlib
   import. Recompiled that module successfully. ConcreteCoefficients supplies
   statement-level constant-ring sheafification instances and remains public;
   the imports of the assigned module's new proof ingredients remain plain imports.

5. **DAG agreement: pass, with open implementation work identified.** Read the
   new nodes and the statements/Lean records of the cited comparison, Cech, and
   derived-identification ingredients. Each new Lean signature agrees with its
   recorded `lean.statement`. For all four delivered nodes, `proof_deps` equals
   the union of the proof steps' `uses`. The assigned node describes the exact
   three-part Lean combination, and only its allowed proof fields change.
   The free-Cech exactness declaration currently has coefficient universe u,
   whereas the new acyclicity interface has coefficient universe u+1; its eventual
   implementation must supply the corresponding universe adaptation. This is
   open work inside the named split theorem, not a completed Lean application
   claimed by this delivery. The generic mathematical Cech argument and 03FD apply
   at the stated universe. The Ext comparison explicitly has the required
   AddCommGrpCat.{u+1} coefficients on Scheme.{u}, and the derived-single
   identification supplies the separate rightDerived comparison.

Changes made by this reading: removed one redundant public Mathlib import;
corrected the constant-ring node's unavailable LeanSearch verdict from null to
`unavailable`; recorded the independent source, edge-case, search, compile, axiom,
and DAG checks above. No proof or statement rewrite was needed. Three sourced
split theorem proofs remain open; no existing library module is globally pruned.

## Second reading by S1

Independent reading of the current repaired sandbox, not authored by this reader.

1. **Visible declarations: pass.** Diffed the assigned module against the repository.
   Its existing signature and docstring are byte for byte unchanged; the only changes
   are three plain proof imports and replacement of its proof. The other three modules
   are new. No existing definition, target, or statement changes; no change record needed.

2. **Proof and axioms: pass as a reduction.** Compiled all four modules in import order
   with lcompile.py, without errors or warnings. Compiled scratch copies with explicit
   `#print axioms` for all four public theorems: each has only propext, Classical.choice,
   Quot.sound, and sorryAx. Inspected all proof bodies: the assigned theorem has no local
   sorry and correctly transports objectwise zero through the colimit and comparison.
   The only three local sorries are exactly the three named, sourced split theorems
   already listed above. No prohibited declarations or hollow definitions occur.
   This delivery does not claim that the assigned theorem is axiom-free yet.

3. **Split statements: pass.** Read all three statements, their docstring proofs, and
   nodes. Rechecked Stacks [0A51](https://stacks.math.columbia.edu/tag/0A51),
   [09ZI](https://stacks.math.columbia.edu/tag/09ZI),
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [03FD](https://stacks.math.columbia.edu/tag/03FD), and
   [093I](https://stacks.math.columbia.edu/tag/093I).
   The all-degree comparison needs torsion of the underlying sheaf, not of the ring;
   the injective acyclicity theorem has neither torsion nor closed-fibre hypotheses.
   The equivalence extends locally constant scalar actions by gluing and retains the
   additive sheaf naturally. Checked degree zero, positive degree, empty schemes,
   identity immersion, and zero ring. The comparison permits nonzero degree-zero
   cohomology. None of the split statements relocates the whole assigned conclusion.
   Fresh LeanFinder searches used forgetting scalars, fixed-scalar module objects,
   and inverse limits of affine etale schemes; Loogle searched module-sheaf equivalences.
   Direct rg searches covered Mathlib module-sheaf/cohomology sources and lean/.
   No exact existing replacement was found. The nearby rightDerived theorem uses
   smaller-universe coefficients and a different encoding; it cannot be applied
   directly. None of the three remaining proofs admits a quick closure from the hits.

4. **Route and pruning: pass.** Read sk-thm-p1 and its realized steps. The affine
   reduction remains below the unit level and keeps henselization, Gabber comparison,
   continuity, inverse-image composition and torsion, and etale injective restriction.
   The six old direct dependencies removed by this reduction are fully listed above;
   no existing node is declared globally pruned. New proof imports are plain imports;
   the constant-ring module's ConcreteCoefficients import supplies statement-level
   sheafification instances. No additional import repair was required.

5. **DAG agreement: pass.** Parsed all four nodes and checked that each proof_deps
   equals the union of proof-step uses, all dependencies exist, and each new
   lean.statement exactly matches its source signature. The existing node differs
   only in proof, proof_deps, and proof_origin. Checked the rightDerived-single and
   Ext comparison declarations. The free-Cech coefficient-universe adaptation noted
   in the previous round remains implementation work within the named open theorem;
   it is not presented as an already typechecked application. The ring-sheafification
   compatibility dependency is a Mathlib leaf with sheafifyComposeIso, and local
   sheafification sections have their existing Lean declaration.

Changes by this reading: appended this independent review and recorded fresh searches,
compilation, and explicit axiom checks. No Lean or node repair was needed. Removed
all temporary probe source files before delivery. One assigned theorem is reduced;
three split theorem proofs remain open.
