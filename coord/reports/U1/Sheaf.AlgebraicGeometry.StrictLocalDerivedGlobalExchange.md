## What changed

Proved `AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_derivedGlobal_exchange` without
changing its signature. Added three modules: `DerivedGlobalGerm` constructs actual global
and pulled global germ natural transformations, derives them using the existing Leray and
exact-functor APIs, and proves that invertibility passes to the derived comparisons;
`StrictLocalGlobalGermIso` proves their invertibility for local maps of strictly henselian
rings; `DerivedGlobalGermExchange` isolates the remaining exchange compatibility equation.

The original proof now takes homology of that equation, uses naturality of
`Functor.mapDerivedCategoryPlusHomologyFunctorIso`, inverts the two canonical comparisons,
and converts their inverse categorical isomorphisms to additive equivalences. This assembly
is fully checked Lean, not an application of a renamed version of the original statement.
The remaining theorem has no strict-local hypotheses and asserts only compatibility,
without any invertibility or additive-equivalence conclusion. The strict-local comparison
is separately proved; the unit and chapter route are preserved.

Repair of the returned delivery: removed the duplicate private theorem
`AlgebraicGeometry.Etale.strictLocal_pointedSection`. The proof now uses the existing
`AlgebraicGeometry.Scheme.strictlyHenselianSections_pointedSection` through
`import all Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`. Lean's module-system
`import all` makes the private helper available to this proof without altering its
original module. Its statement and proof are unchanged and need only a field, so they
apply to separably closed point fields. It explicitly installs
`LocallySmall` and shrinks preservation of filtered colimits to avoid instance-search loops.
Both residue-point images are checked using `IsLocalRing.comap_closedPoint`.

Edge cases: the constructions allow arbitrary schemes and bounded below derived objects,
all integer degrees, and separably closed fields that need not be algebraically closed.
No use is made of properness, quasi-compactness, torsion, nonempty total spaces, or positive
degree. For zero objects the natural transformations and homology maps specialize to zero
maps; negative degrees use the same exact-functor homology comparison. Compatibility is
stated for all cartesian squares and geometric points, without assuming the germs invertible.

All four delivered modules are checked locally in import order. Final validation is
the delivery tool's dry run, including its axiom probe and preflight.

## Proved and sorry left

Closed the original module's one local sorry (a decomposition, not a sorry-free proof):
`AlgebraicGeometry.Etale.exists_addEquiv_strictLocal_derivedGlobal_exchange`.

Also proved `AlgebraicGeometry.Etale.strictLocal_globalGerm_isIso` and the two transport
lemmas `isIso_derivedPulledGlobalGerm` and `isIso_derivedGlobalGerm`. All four new definitions
contain real constructions, with no postponed proof or data.

One hole closed and one hole added: net zero holes closed. The new compatibility statement
is strictly the non-invertibility part of the argument; the invertibility and homology
assembly are proved. Exactly one new sorry remains:
`AlgebraicGeometry.Etale.derivedGlobalGerm_exchange`, node
`lem-weil-pbc-derived-global-germ-exchange`, in
`lean/Sheaf/AlgebraicGeometry/DerivedGlobalGermExchange.lean`. It is the whole proof of a named
public theorem with a source and complete proof in words. It is strictly the compatibility
part of the original argument. Future work is the mate/germ identity and the right-derived
unit/Leray transport, as explained in its docstring.

## No longer needed

Removed direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`,
`Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`,
`Sheaf.Paper.InverseImageStalkGerm`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`.

`CohomologyPullbackDerivedUnit` and `DerivedExchangeTermwise` remain proof imports of the
remaining compatibility item, so their nodes are retained transitively. The precise
inverse-image stalk isomorphism comes from the already proved source module
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`, which accepts separably closed fields.
The strict-local proof now imports `StrictlyHenselianSectionsStalk` and uses its existing
pointed-section theorem. Its algebraically closed stalk wrapper is not used. Removed
`WeilConjectures.RingTheory.ProEtale.HenselianLocalRing` from `StrictLocalGlobalGermIso`;
localization and Olivier remain encapsulated in the existing pointed-section proof.

The original item no longer directly needs these old proof-dependency nodes:
`lem-weil-pbc-cohomology-pullback-derived-unit`,
`lem-weil-pbc-derived-exchange-termwise`,
`lem-weil-pbc-dplus-injective-representative`,
`lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-strictly-henselian-sections-stalk`,
`prop-weil-pbc-cohomology-resolution-independent`,
`prop-weil-pbc-geometric-stalks-exact`, and
`prop-weil-pbc-inverse-image-exact`.
The algebraically closed inverse-image germ wrapper is also removed from the new
compatibility node: its general-site proof must be applied directly to separably closed
points, via the source comparison construction.
The representative and termwise calculations still belong to the compatibility proof plan;
this report makes no claim that they are globally unreachable. Exact stalks and homology
are supplied by proved Mathlib/source APIs; exact inverse image is already available from
the statement imports. No public import of the original module was removed.

## Where the brief, the DAG or earlier work was wrong

The existing public theorems `strictlyHenselianSections_geometricStalk_isIso` and
`inverseImage_stalk_germ` impose `IsAlgClosed` on the point field. The original item only
assumes `IsSepClosed` for the residue fields; the implication to `IsAlgClosed` is false in
positive characteristic. The underlying pointed-section proof works already for a field,
and the source `upperStarCompSheafFiberIso` already accepts `IsSepClosed`. The delivery
therefore proves the needed generality without changing any existing interface.

The earlier delivery duplicated the private pointed-section theorem, contrary to the
reuse rule; the landing tool correctly refused it. The repair imports the original
private helper with `import all`, a supported Lean module-system import form also used
in Mathlib. No existing library file is adapted, and no statement, definition or public
interface changes. The strict-local node now records the existing sections/stalk node
as its proof dependency, rather than Olivier directly. The previous second-reading
section below describes the returned version and is retained as historical review;
its assertion that a copied helper should be retained is superseded by this repair.

Searches used leanfinder, loogle and grep. LeanSearch returned an Internal Server Error,
recorded by the required search script. No whole comparison lemma was found. Blueprint
searches for global germ and stalk/global sections found no duplicate blueprint node.

The local literature checkout lacks `literature/stacks-project/etale-cohomology.tex`.
The cited passages were read at the official Stacks pages:
https://stacks.math.columbia.edu/tag/03QO,
https://stacks.math.columbia.edu/tag/03Q1, and
https://stacks.math.columbia.edu/tag/095T.

## New nodes

`def-weil-pbc-derived-global-germ`: the four concrete canonical germ constructions and
invertibility transport lemmas in `DerivedGlobalGerm`. These definitions fix the maps
used in the compatibility theorem, rather than choosing arbitrary equivalences.

`lem-weil-pbc-strict-local-global-germ-iso`: the proved invertibility of both underived
canonical germs over strict-local bases in `StrictLocalGlobalGermIso`, using pointed
sections, germ representatives, locality, and the inverse-image stalk isomorphism.

`lem-weil-pbc-derived-global-germ-exchange`: the one remaining compatibility equation in
`DerivedGlobalGermExchange`, with no assertion of invertibility. The node records the
termwise and derived-unit/Leray steps separately. No existing statement or definition is
changed, so no interface change record is required.

## Earlier second reading (a previous round; superseded)

1. Compared the existing module against the repository with `diff -u`: its declaration
   signature and docstring are byte for byte unchanged; only the proof, proof imports and
   a local elaboration option changed. The other three modules are new. No definition or
   existing interface was changed, and no change record is required. Verdict: pass.
2. Read all four Lean files and compiled them in dependency order. There is exactly one
   `sorry`, the named public compatibility theorem listed above; no hollow definitions,
   forbidden axioms or unsafe declarations. Checked the pointed-section localization,
   germ bijectivity, derived isomorphism transport, homology naturality and inversion
   assembly. Explicit `#print axioms` checks show only propext, Classical.choice and Quot.sound
   for all four constructions, both transport lemmas and strict-local invertibility.
   Only the compatibility hole and the original theorem assembled from it also use sorryAx. Verdict:
   a valid decomposition, with one local hole closed and one added, not a complete proof.
3. The compatibility equation compares two specified canonical maps and makes no
   invertibility assertion. The strict-local invertibility is separately proved. Checked
   the identity-square specialization, zero complexes, arbitrary integer degrees, and
   separably closed imperfect fields: no extra finiteness, properness or algebraic
   closedness is required. Its docstring gives the resolution/mate/unit/Leray argument,
   and its node matches the equation. Additional leanfinder, loogle and grep searches
   with different terms found no existing complete derived compatibility result; the
   finite-base-change stalk formula has algebraically closed hypotheses and a different
   conclusion. Closing the remaining derived transport is not a few-minute proof.
   Verdict: genuinely smaller remaining compatibility task, not a restatement.
4. Read the existing dependency declarations, source comparison and unit realization.
   The shortest proved general-site and exact-functor APIs are used; all old proof
   dependencies removed from this item's direct proof are enumerated above. The
   strict-local comparison in `sk-thm-p1` remains realized through its existing nodes;
   no curve, closed-fibre or chapter step is bypassed. No globally pruned module is
   claimed without the maintainer's reachability calculation. Verdict: pass.
5. Compared node proof steps and dependency unions with the Lean construction and the
   remaining proof plan. Found an inapplicable dependency on the algebraically closed
   `inverseImage_stalk_germ` wrapper in the new compatibility node and removed it,
   recording instead the direct general-site comparison expansion used for separably
   closed points. Made all three new nodes' Lean statement records agree with the tool's normalized
   signatures (omitting the `noncomputable` modifier and preserving return-type lets).
   Existing node changes remain restricted to stage-3-owned fields. Verdict: pass
   after repair.

Changes by the second reader: removed unused public imports of BaseChange.Derived and
EtalePoint from DerivedGlobalGerm (EtalePoint is already supplied by the stalk comparison),
and imported BaseChange.Derived directly in DerivedGlobalGermExchange, whose statement
uses exchange. Repaired the compatibility node's dependency plan and the new Lean
signature records. Clarified the zero-net decomposition count in this report. The Lean
proofs were correct and retained.

Second-reader source check: read [Tag 03QO](https://stacks.math.columbia.edu/tag/03QO),
[Tag 095T](https://stacks.math.columbia.edu/tag/095T) and
[Remark 08J6](https://stacks.math.columbia.edu/tag/08J6) on the official Stacks site.
The arbitrary-complex compatibility is the categorical expansion documented in the
new theorem, rather than a claim that the proper/torsion theorem directly states it.


## Second reading by U1

1. Compared the original module with the repository using `diff -u`. Its theorem signature
   and docstring are byte for byte unchanged, including all residue-field assumptions,
   arbitrary bounded below K and integer q, and the equation for the additive equivalences.
   Only proof imports, a local elaboration option, and the proof change. The three other
   modules are new; no existing definition or statement is adapted. Verdict: pass.
2. Compiled all four modules in import order through `lcompile.py --all`: no errors or
   warnings. Read the germ constructions, pointed-section reuse, germ bijectivity,
   derived isomorphism transport, and homology/inversion assembly. There is one named
   public sorry, `derivedGlobalGerm_exchange`, with its source, proof docstring and node;
   no hollow definition or forbidden declaration. Explicit `#print axioms` in a scratch
   copy gives only propext, Classical.choice and Quot.sound for the four constructions,
   both transport lemmas and `strictLocal_globalGerm_isIso`. The compatibility theorem
   and original theorem additionally use sorryAx. Verdict: valid decomposition, net zero
   holes closed, not a completed proof independent of sorry.
3. The remaining equation fixes canonical maps and asserts no invertibility. The strict-local
   invertibility and passage to additive equivalences are proved separately, so the hole
   is strictly a part of the argument rather than the original item renamed. Checked
   identity squares, zero objects and all integer degrees; the germ argument works for
   separably closed imperfect fields and uses no properness or torsion. Read the existing
   `Scheme.strictlyHenselianSections_pointedSection` proof: its signature needs only a
   field, and its localization lift proves equality of the full marked point. The repaired
   `import all` reuses this declaration rather than copying it. New leanfinder search for
   “right derived functor mate base change evaluation compatibility” found derived-unit
   and counit compatibility APIs, not this equality; loogle for the plus natural-transform
   API reported unknown identifier, and grep for base-change/germ combinations found no
   matches. Also searched the project and upstream Lean with rg. The remaining mate/germ
   and Leray transport is not a few-minute application of any found theorem. Verdict: pass.
4. Read Stacks Tags 03QO, 095T and Remark 08J6, the source stalk-comparison construction,
   and the two imported derived-unit/termwise statements. Tag 03QO supplies the pointed
   neighbourhood/section route; the arbitrary-complex compatibility is the categorical
   expansion in the split theorem's proof, not an invocation of proper/torsion base change
   outside its hypotheses. In the strict-local proof, common-neighbourhood equality is
   pulled back through a section for injectivity; germ representatives give surjectivity.
   Locality is used explicitly through comap_closedPoint for both residue-point images.
   In the original proof, homology naturality yields j1 ≫ stalk(e) = H(p) ≫ j2, then
   inversion gives the required equation. The old direct dependencies removed from the
   target are all listed above; sections/stalk is retained transitively in the strict-local
   lemma, and termwise/derived-unit imports remain in the compatibility module. Proof-only
   imports are private. Read sk-thm-p1.json realized: the strict-local exchange step and
   the curve/closed-fibre route stay in place. No globally unreachable module is claimed.
   Verdict: pass.
5. Read all four node files against their Lean: signatures and proof steps match, the
   proof_deps lists equal their step-use unions, and the three new nodes carry source,
   searches, creation, blueprint, chapter/unit and Lean records. The existing node changes
   are confined to stage-3-owned fields. The original theorem uses the canonical germ
   node, strict-local invertibility, compatibility and the exact-functor homology API as
   recorded. Verdict: pass.

Changes in this reading: completed the No longer needed list with the removed direct
StrictlyHenselianSectionsStalk import and its node (still used transitively), and appended
this review. Retained the repaired Lean proofs and node records unchanged.
