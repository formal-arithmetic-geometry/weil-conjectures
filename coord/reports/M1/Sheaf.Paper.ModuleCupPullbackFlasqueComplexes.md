## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_flasque_complexes`
with a complete Lean assembly from six existing Godement models and one new
coefficient-map compatibility lemma. Its signature, universes, hypotheses,
visibility and existing public imports are unchanged.

Added `Sheaf.Paper.ModuleCupGodementFMapSummands`, which states compatibility
for arbitrary coefficient maps φ, ψ, χ across a scheme morphism satisfying
a pure-tensor section equation, and for six already supplied concrete models
with prescribed codegeneracies. It supplies cosimplicial pairings and maps
between the individual coefficient complexes with front/back summand equations.
It does not construct total tensor chain maps or assert quasi-isomorphisms,
support or flasqueness. Thus it isolates the coordinate compatibility part of
the original plan rather than renaming the original resolution-existence theorem.

The main proof obtains its six models from `moduleCup_godement_models_exist`,
checks the generic lemma's tensor hypothesis using the section-normalization
clause of `module_pullback_tensor`, and uses the existing quasi-isomorphism
and flasqueness proofs for all six models. The proved `aw_components` helper
constructs the two total tensor cochain maps with explicit components.
`moduleCup_ι_awComponent` and `moduleCup_awSummand_zero` yield the augmentation
formulas; the same inclusion/component identity in general bidegree yields
the final section equation by composing three equalities.

Added only proof imports to the original module. `import all` gives access to
the already proved private helpers `modelFlasque` in
`ModuleCupGodementCosimplicialInput` and `aw_components` in
`ModuleCupCosimplicialAWNaturality`; their original modules are unchanged.
The theorem-local heartbeat bound is 800000 because specializing six models
and the section identities elaborates large tensor-complex types. The wall-clock
file limit remains unchanged; the final local compilation took about 23 seconds.
Updated the original node's proof, proof_deps and proof_origin to match this route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_flasque_complexes`
(node `lem-sc-module-cup-pullback-flasque-complexes`). No `sorry` remains in
that module.

Added one hole, the entire proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_fmap_summands`
(node `lem-sc-module-cup-godement-fmap-summands`), in its own module.
There are no other delivered holes. This is a decomposition: one original
hole closed, one strictly lower compatibility hole added, net zero new-hole
reduction. It is not a claim that the original theorem is free of sorry axioms.
Both delivered modules compile with no warnings through lcompile.py.

Checked the new statement's edge cases in its coordinate argument: the empty
scheme and empty opens use empty products, zero coefficients and zero maps
use zero coordinate families, and (p,q)=(0,0) uses identity front/back faces.
The arbitrary coefficient-map hypothesis explicitly requires the tensor
compatibility that the induction uses; no flatness or nonemptiness is added.
All given models retain both their canonical coface and codegeneracy conditions.

## No longer needed

No original imports were removed: each of the four original public imports
provides types or definitions in the unchanged signature. Every added proof
import is used. No whole module is claimed to leave the targets' import closure.

The main proof no longer applies `moduleCup_godement_pairing` from
`Sheaf.Paper.ModuleCupGodementPairing` (node `lem-sc-module-cup-godement-aw`):
its existential pairing would not identify the component formulas required
for cross-scheme compatibility. The explicit `aw_components` construction
replaces that planned direct dependency.

These original planned nodes are no longer direct proof dependencies of this
item: `def-sc-module-cup-godement-model`,
`def-sc-module-cup-godement-codegeneracies`,
`lem-sc-module-cup-godement-relations`,
`lem-sc-module-cup-godement-model-pairing-pairing`,
`lem-sc-module-cup-godement-object-flasque`, and `def-pc-module-pullback`
(the last remains a statement dependency).
They remain available through the model-existence, flasqueness or new generic
compatibility argument. This is not a claim that their modules are globally
pruned. The updated DAG retains the actual upper proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned declarations cover same-scheme model existence and pairings, not
cross-scheme maps compatible with those pairings. In particular,
`moduleCup_cosimplicial_aw_natural` assumes all six cosimplicial objects lie in
one module category, whereas this theorem has two schemes and pushforward.
The new lemma states precisely the missing coefficient-map coordinate argument.
No existing signature or definition needed correction, and no forced adaptation
was made. A broad dependency-closure check encountered a pre-existing DAG cycle
between `lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`; neither is edited
here. A separate reachability check confirms that no dependency of the new node
reaches it or its parent, so the delivered edges create no new cycle. The unit and chapter routes are unchanged.

Searches used Lean Finder, Loogle, Mathlib grep and repository grep. Lean Finder
returned unrelated Mayer--Vietoris/Dold--Kan entries, and Loogle found the
ordinary extension-map API. No existing cross-scheme Godement tensor theorem
was found. LeanSearch was attempted and returned Internal Server Error; that
unavailable service was not used as evidence of absence. The existing
same-scheme coefficient-model and naturality modules were read and reused where
applicable. The new proof is the explicit coordinate extension of the Stacks
Godement construction, not an assertion that Tags 0FKR or 0FKU directly state
this new cross-scheme theorem.

## New nodes

`lem-sc-module-cup-godement-fmap-summands` supplies compatible cosimplicial
pairings, coefficient-complex f-maps, augmentation squares and individual
front/back section-operation equations for six given concrete Godement models.
Its source is the Godement product-of-stalks construction in Stacks Tag 0FKR,
with the coordinate extension written out in the node and docstring, the naive
product in Tag 0FKU, and the existing Banerjee §1.1.4 front/back formula.
It is strictly below the item: the main proof separately constructs all six
models, proves the pullback coefficient tensor equation, supplies all analytic
resolution properties, and constructs the two total tensor cochain maps.
The node records all search attempts and the complete coordinate induction.
No change record was needed, since no existing interface changed.

## Second reading by M1

1. **Existing interface: PASS.** Compared the complete module with the repository
   using diff and compared its theorem signature byte for byte. The signature,
   docstring, universes, visibility and all four public imports are unchanged.
   The only changes are five private proof imports, a theorem-local heartbeat
   option and the proof body. No definitions or other existing modules change;
   no change record or forced adaptation is needed.
2. **Kernel proof and holes: PASS as a decomposition.** Recompiled both delivered
   modules through lcompile.py in dependency order: 2.9 and 20.4 seconds, no
   diagnostics. The original module has no sorry; the new module has exactly
   the named theorem moduleCup_godement_fmap_summands with its complete source
   and coordinate proof docstring. No forbidden declarations or hollow
   definitions occur. A scratch module prints the axioms of both declarations:
   only propext, Classical.choice, Quot.sound and sorryAx occur for both. This closes one upper hole and adds one lower
   hole; it does not certify the target as sorry-free.
3. **Split-off statement: PASS.** Read the concrete iterate, insertion,
   multiplication and codegeneracy definitions and checked the coordinate
   argument against them. The stalk f-map sends the germ of a section on V
   to its image germ on f inverse V. For multiplication, represent the outer
   germ on a neighbourhood of f(x') and evaluate its f(x') coordinate; both
   composites then apply the same coefficient stalk map. For tensor compatibility,
   representatives of the two input germs can be restricted to a common open,
   where hχ applies; this proves the induction step coordinatewise. The term
   equalities supplied separately by the model and codegeneracy predicates agree
   by proof irrelevance, as in the existing pairing-for-models proof. Empty
   opens/schemes, zero coefficients, zero compatible maps, the identity morphism
   and bidegree (0,0) require neither flatness nor nonemptiness. The statement
   omits all resolution properties and total tensor maps and is a strictly
   lower compatibility result, not a restatement of the item. It cannot be
   closed in a few minutes: the cross-scheme semilinear coordinate construction
   and its monad identities still need formalization. Independent searches used
   Lean Finder for morphisms of ringed spaces and multiplicative stalk-product
   resolutions, Loogle for TopCat.Presheaf.stalkPushforward, and Mathlib grep for
   skyscraper maps/tensors and pushforward stalks. These identify the stalk API,
   not a duplicate. Repository searches and reading ModuleCupGodementCoefficientModels
   confirm its maps and pairings all lie on a single scheme. Checked Stacks
   [0FKR](https://stacks.math.columbia.edu/tag/0FKR) and
   [0FKU](https://stacks.math.columbia.edu/tag/0FKU): the cross-scheme argument is
   explicitly an extension of their construction, not a theorem quoted from them.
4. **Top-down assembly and pruning: PASS.** Read the complete proof and the
   existing model-existence, modelFlasque and aw_components helpers. All six
   models are supplied independently of the new hole; support, quasi-isomorphisms,
   flasqueness and the two total tensor chain maps are assembled separately.
   Section normalization supplies exactly hχ. The augmentation and general
   bidegree equations follow from the two inclusion/component identities and
   the new compatibility equation. No shorter existing cross-scheme route was
   found. Each added import supplies a used declaration; each public import
   supplies the existing interface. Compared old and new proof_deps: all seven
   removed direct dependencies appear in No longer needed. None is claimed
   globally pruned. Read dag/units/sk-prop-av-cube.json and its realized record:
   this change stays below its cube-theorem step and changes no unit route or
   realization.
5. **DAG agreement: PASS.** The only edited fields of the existing node are
   proof, proof_deps and proof_origin. In both delivered nodes proof_deps is
   exactly the union of the proof steps' uses, and lean.statement matches its
   Lean signature verbatim. The new node has its source, full proof, three
   successful search kinds, creation record, blueprint ancestry, chapter,
   unit and Lean attachment. The original node accurately records the helper
   constructions actually used, rather than claiming an application of their
   enclosing public naturality/input theorems.

**Second-reader changes:** added this independent review and its search/axiom
verification evidence. No mathematical, Lean source or DAG repair was needed.
