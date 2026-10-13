## What changed

Replaced the proof of `RingTensorCohomology.firstLocalization_comparison` in
`Sheaf.Algebra.Homology.FirstLocalizationComparison`. Its statement, universes,
visibility and coefficient-compatibility assumptions are unchanged.

The proof uses two new proof-only imports: `FirstLocalizationOrdinarySquare` and
`ScalarExtensionHomologySquare`. The first proves the ordinary counit square
before localization. The second proves a generic scalar-extension assembly lemma:
it assumes the ordinary cohomology square and coefficient-complex square as
separate inputs and has no derived functor, model, localization, or isomorphism
hypotheses. These are strictly different parts of the argument, not renamed
copies of the original theorem.

The coefficient-complex square is proved here: degreewise surjectivity of
`ordinaryIso.hom` represents each input by a tensor; tensor induction reduces the
square to `ordinaryIso_tmul`, `ordinaryToLocalized_tmul`, and the given formula
for tau. The two resulting B-coefficients coincide by the two B-to-D scalar towers.
The main theorem then assembles this square, the ordinary cohomology square,
`localized_eq` for each model, and `he`.

## Proved and sorry left

Closed the original hole in `RingTensorCohomology.firstLocalization_comparison`
(node `lem-pc-first-localization-comparison`). There is no sorry in the item module.

Proved `RingTensorCohomology.firstLocalization_ordinary_square`
(`lem-pc-first-localization-ordinary-square`) with no sorry. Counit naturality and
the canonical left-derived-functor isomorphism prove the B-linear square;
naturality of the homotopy and derived homology factorization isomorphisms gives
its ordinary form. Private helpers identify direct forgetting with restriction
followed by forgetting using cycles inclusions and homology projections, and
transport this square to additive groups.

Proved `ModuleCat.scalarExtension_homology_square`
(`lem-pc-scalar-extension-homology-square`) entirely from Mathlib, with no sorry.
Private helpers prove homology-projection compatibility and the agreement of
forgetting scalars directly with forgetting after restriction, by the universal
properties of cycles and homology. Homology naturality transports both adjunction
identities; the two input squares compose, and scalar-extension hom_ext plus he
finishes the D-linear equality.

One original hole closed, no lower holes added: net 1. Every delivered theorem
and private helper is proved. There is no sorry left in any of the three delivered
modules. The ordinary coefficient-complex square and final assembly are complete
Lean proofs. A separate diagnostic reports exactly propext, Classical.choice and
Quot.sound for each of the three public theorems. No existing dependency is
modified by this delivery. The existence result
`RingTensorCohomology.exists_firstLocalization_iso` is not used to construct e here.

## No longer needed

No existing import was removed. The existing `FirstLocalizationMap` import is
needed by the theorem's statement and by its ordinary derived-cohomology map.
Neither `exists_firstLocalization_iso` nor its K-flat/localization construction is
needed to prove this comparison square once e and its generator formula are given.
No existing dependency node or module can be removed from the import closure:
`def-pc-base-derived-tensor-cohomology-model` and `lem-pc-first-localization-map`
remain necessary, including for the statement.

## Where the brief, the DAG or earlier work was wrong

The original two proof steps correctly describe the mathematics, but their cited
modules do not state the ordinary naturality square or the generic transposition
lemma. Reading their actual signatures showed that these are glue arguments, not
applications of their existence theorems. The delivery proves those two strictly
smaller arguments and updates the original proof route to match the Lean.

The coefficient square needs only the B-to-D scalar towers. The other originally
included coefficient assumptions are retained verbatim; a declaration-local unused
section-variable linter option records that their non-use is intentional without
changing the signature.

Mathlib searches were run through msearch: LeanFinder and Loogle found generic
naturality and scalar-adjunction tools but no exact theorem. LeanSearch returned
Internal Server Error; this is recorded as unavailable. Source grep found
`leftDerivedNatTrans_fac`, `mapHomologyIso_hom_naturality`, and generic homology and
adjunction identities. Blueprint searches for counit, scalar extension and the
comparison keywords found no existing node for these two glue statements.

The edge cases checked for the new statements are identity coefficient maps,
zero complexes, zero modules and zero D. Their arguments use only exact forgetting
or restriction of scalars and tensor generators; neither flatness of D nor
invertibility of the comparison maps is assumed. The unit's route and realized
steps are unchanged.

## New nodes

`lem-pc-first-localization-ordinary-square` is the counit-naturality portion of the
original first step, before coefficient extension. It has no e, tau, localized
comparison, localization assumption, or final coefficient-compatibility hypotheses.
Its module is `Sheaf.Algebra.Homology.FirstLocalizationOrdinarySquare`.

`lem-pc-scalar-extension-homology-square` is generic transposition for ordinary
cohomology and coefficient-complex squares. It takes both squares as independent
hypotheses and has no base-derived tensor model or derived universal property.
Its module is `Sheaf.Algebra.Homology.ScalarExtensionHomologySquare`.

The scalar-extension module imports Mathlib alone; its initial dependency on the
base-derived model module was removed because neither its statement nor proof needs
any derived functor or model. The redundant HomologicalComplexAbelian import was
also removed after compiling without it; ChangeOfRingsExact and
ShortComplex.HomologicalComplex supply all required definitions and instances.

Both new nodes are fully proved. Both nodes are in
`dag/nodes/sec-picard-framework/`, inherit the original unit,
and give the complete argument in their proof fields and theorem docstrings.
No existing statement or definition was changed; no change record or forced
adaptation is needed.

## Second reading by D3

1. PASS: diffed every delivered module against the repository. Only
FirstLocalizationComparison exists there; its full declaration signature, universes,
section instances, include list, visibility, and existing docstring are byte for byte
unchanged. Its differences are two plain proof-only imports, a declaration-local
unused-section-variable linter setting, and the proof replacing sorry. The other
two modules introduce new proved theorems and private proof helpers. No definition
or existing statement is changed, and no change record is required.

2. PASS: independently compiled all three modules in import order with lcompile.py,
with no errors or warnings. A scratch-copy #print axioms check of all three
public theorems returned exactly propext, Classical.choice and Quot.sound,
with no sorryAx. Read every proof, including the private cycles and
homology coherence helpers. The coefficient square uses tensor induction after
ordinaryIso surjectivity; both coefficients reduce through the two B-to-D scalar
towers. No sorry, axiom, unsafe, opaque, implemented_by, extern, hollow definition,
or arbitrary witness construction occurs in any delivered module.

3. PASS: there are no split-off holes. The two new fully proved statements are
strict parts of the argument: ordinary counit naturality and generic transposition
of two independently supplied squares. Identity units, zero complexes, zero modules
and zero coefficient rings cause no exception: the arguments use exact restriction
and forgetting, naturality, and scalar-extension generators, not flatness. Both
theorem signatures match their node Lean records verbatim and both docstrings give
the full mathematical argument. Independent msearch queries for extension/restriction
transposition and homology-isomorphism composition, plus repository source searches,
found generic naturality tools but no duplicate public theorem. The existing
restrictionCompositeHomology concerns two ring restrictions, rather than forgetting
to additive groups, and its general composition helper is private; it does not
replace either new public square or the direct-forgetting coherence proof here.

4. PASS: the proof starts at the original hole and uses proved counit naturality,
exact-functor homology naturality and tensor-generator extensionality. It does not
use the localization-isomorphism existence theorem or introduce lower holes. The
FirstLocalizationMap import is public because the original signature needs it;
both new imports are plain because only the proof needs them. The new modules'
public imports supply their signatures and required instances. Neither old
proof dependency is prunable: the model fields and first-localization unit/map
are used. The unit sk-thm-picard-semicon has realized statement [] and steps [[]];
this delivery neither changes it nor bypasses a realized step.

5. PASS: compared old and new node records. The existing node changes only proof,
proof_deps and proof_origin, and its three steps describe exactly the ordinary
square, coefficient tensor calculation, and scalar-extension assembly in Lean.
The new nodes carry all required fields, have proof_deps equal to the union of
their step uses, and accurately describe the proved statements and proofs.

Changes by the second reader: added this review and recorded the independent
search and validation results; no mathematical or Lean repair was needed.
