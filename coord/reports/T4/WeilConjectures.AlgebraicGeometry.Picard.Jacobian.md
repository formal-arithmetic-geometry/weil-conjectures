## What changed

Closed both original holes in
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`, with its signature unchanged.
Added seven proved supporting modules under `Sheaf.AlgebraicGeometry`: a finite separable
scheme model, pointwise pullback limits, a finite model of universal transport, faithfully flat
testing of transport axioms, descent-datum refinement, affine neighbourhoods of finite
sets in projective schemes, and fpqc representability descent. Added
`PicardDegreeSheafFpqc` for the remaining degree-sheaf obligation. Added ordinary proof imports only; existing public imports,
definitions and target signatures are unchanged. Updated `cor-pd-finite-level` and Step 7 of
`thm-pd-jacobian-general-field` to follow these constructions.

The construction uses the already proved finite-presentation limit API. Only the universal
transport morphism needs spreading. Its identity and cocycle equations follow by cancellation
of faithfully flat covering maps. Existing properness and quasi-projectivity descent produce
a closed projective embedding; graded prime avoidance produces the required affine opens.

## Proved and sorry left

Original holes: two. Closed both original proof placeholders:

- `AlgebraicGeometry.exists_intermediateField_descentDatum` (`cor-pd-finite-level`): a complete
  proof from existing library results and the six new proved finite-level lemmas.
- `AlgebraicGeometry.nonempty_representableBy_picardFunctorDegree_of_isPullback`
  (`thm-pd-jacobian-general-field`, Step 7): reduced to the fpqc sheaf property of the Picard
  degree part by a completely proved general fpqc representability-descent theorem.

One new hole remains:
`AlgebraicGeometry.isSheaf_fpqc_sheafify_picardDegree`
(`lem-pd-degree-picard-sheaf-fpqc`, module `Sheaf.AlgebraicGeometry.PicardDegreeSheafFpqc`).
Its proof is exactly `by sorry`, with a full proof in words. This is a sheaf condition, with
no representing object, cartesian square or transport-invariance hypothesis. It is strictly
part of the remaining argument, not the original representability theorem under another name.
There is no `sorry` left in the Jacobian module and none in the other seven new modules.
Net direct holes closed minus holes added: 2 - 1 = 1. The first original proof placeholder is closed, relative to the upstream library; the second
is a decomposition with the categorical descent part proved.

What the remaining lemma needs: construct the equivalence with normalized degree classes
on a finite separable covering with a curve point; upgrade normalized invertible-module
existence and uniqueness from fppf to fpqc descent; check fibrewise degree by residue-field
base change; and glue back along the finite fppf cover. The existing
`isSheaf_picardFunctorNormalized` proves only the fppf statement. Its existence argument
already uses fpqc descent, but its uniqueness argument invokes the fppf sheaf and must be
replaced by normalized morphism rigidity and fpqc full faithfulness. The complete plan is
in the new declaration's docstring and DAG node. No arbitrary witness is put in a definition.

The seven new proved declarations are:

- `AlgebraicGeometry.exists_finiteSeparable_schemeModel`.
- `CategoryTheory.Limits.isLimit_pointwisePullback`.
- `AlgebraicGeometry.exists_finiteSeparable_universalTransportModel`.
- `AlgebraicGeometry.exists_descentDatum_of_universalTransport`.
- `AlgebraicGeometry.exists_finiteSeparable_descentDatum_refinement`.
- `AlgebraicGeometry.exists_isAffineOpen_of_finite_projective`.
- `AlgebraicGeometry.nonempty_representableBy_of_effective_fpqc_descent`.

All nine delivered modules compile together in import order with `lcompile.py --all`.
The original module compiles in about 19 seconds; the largest new module takes about 9 seconds.
The finite-set lemma includes the empty set, arbitrary coordinate types and finite ground
fields. The transport-testing lemma uses only flatness and surjectivity of the testing cover.

Axiom audit by the second reader: all seven new proved declarations use only `propext`,
`Classical.choice` and `Quot.sound`. Both original declarations still use `sorryAx` through
open upstream results; the representability declaration additionally uses the one new hole.
Thus neither original declaration is claimed to satisfy the global target completion criterion.

## No longer needed

No original import or whole module is removed. Removed redundant imports from new modules:
`Mathlib.AlgebraicGeometry.PullbackCarrier` and
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`. The original module needs
no added direct import of `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`:
its proved API is already exposed by the existing projectivity import. The finite scheme
model imports the spreading API privately rather than exposing its proof dependencies.
 At the route level, the finite-level proof no
longer uses the eventual-equality clause (3) of `thm-pd-spreading-out`, separate spreading of
identity and triple-product cocycle equations, or spreading of a chosen projective embedding.
Clause (1) and morphism factorization remain needed. Projectivity instead follows by properness
and quasi-projectivity descent. The universal transport construction avoids a separate theory
of colimits of double tensor products: pointwise fibre-product limits suffice.

`lem-pd-descent-cocycle` is no longer a direct proof dependency of `cor-pd-finite-level`:
the already constructed canonical datum contains its cocycle proof. `def-pd-descent-datum`,
`def-pd-separable-closure`, `def-pc-morphism-conventions`, `def-pc-base-change` and
`def-pc-projective-morphism` are used through the new supporting nodes rather than as
separate direct steps. None of these nodes is claimed to be globally unreachable.

The second reader removed the redundant `Mathlib.AlgebraicGeometry.Limits` imports from
`FiniteSeparableSchemeModel` and `FiniteSeparableUniversalTransportModel`: their public
finite-presentation API already exposes what the signatures need. The first worker had
incorrectly made these proof-related imports public.

`thm-pd-spreading-out` is also no longer a direct dependency of `cor-pd-finite-level`; its
clauses remain used inside the finite-model supporting nodes. The old general-field node's
`lem-pd-group-scheme-descent` and `lem-pc-dim-base-change` dependencies are removed: the
existing Lean proof obtains the group law from the represented group-valued functor by Yoneda,
and its fpqc property theorem already descends smooth relative dimension `g`. Their modules
are not claimed globally unreachable. No whole module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

No existing mathematical statement was changed or disputed. Step 7 of
`thm-pd-jacobian-general-field` incorrectly said that an fppf sheaf is determined by base
change along the general faithfully flat field extension `k_s/k`. Such a morphism need not
be locally of finite presentation and hence need not be an fppf covering. The proof now uses
the needed fpqc sheaf statement explicitly; the generic fpqc gluing argument is proved.
 The planned route works, but
spreading equations separately is unnecessary: faithfully flat epimorphism cancellation
proves them at the stage where the transport morphism is defined. Likewise the existing
quasi-projectivity descent theorem gives a shorter route than spreading an embedding.

LeanSearch was unavailable (Internal Server Error); the search records retain that failure.
Loogle and Mathlib grep searches ran and supplied ingredients, without an exact theorem for
these specialized constructions. No process workaround was used.

## New nodes

`lem-pd-finite-separable-scheme-model`: finite-presentation spreading over the spectra of
finitely generated subalgebras, converted to finite separable intermediate fields.

`lem-pd-pointwise-pullback-limit`: explicit universal-property construction of the limiting
cone of pointwise fibre products over a fixed base, for a nonempty index category.

`lem-pd-finite-separable-universal-transport-model`: factors the universal transport morphism
through one finite field stage and proves its compatibility on every test scheme.

`lem-pd-datum-from-universal-transport`: constructs transport from its universal morphism and
proves identity and cocycle by faithfully flat testing, including the base-change equality.

`lem-pd-finite-separable-datum-refinement`: combines transport spreading and faithful-flat
testing to refine an existing finite separable model with its descent datum.

`lem-pd-projective-finite-affine-neighbourhood`: graded prime avoidance and affine inverse
images provide an affine open containing any finite set.

`lem-pd-fpqc-representability-descent`: the local universal section is compatible by
transport invariance, glues by the fpqc sheaf condition, and gives a locally bijective Yoneda
map. A locally bijective map of sheaves is an isomorphism. This node is fully proved.

`lem-pd-degree-picard-sheaf-fpqc`: the fpqc sheaf condition for the fppf degree-part
sheafification, stated independently of the representing scheme. This is the one remaining
hole, with the precise missing steps listed above.

Seven new nodes are proved and one remains open. No change record is required because no
existing signature or definition changed.

## Second reading by T4

1. **Existing interfaces: pass.** Read the complete diff of Jacobian against the repository.
   Its 76 declarations have the same statements, declaration kinds and visibility; the only
   declaration-body edits are the two original holes and their explanatory docstrings.
   All existing public imports and definitions are unchanged. The six new imports there are
   plain proof imports. Every other delivered module is new; no adapted existing module and
   no interface change requiring a change record occurs.

2. **Proof and axioms: pass, with the reported open obligation.** Compiled the nine modules
   in dependency order using `lcompile.py --all`. The only literal hole is the named theorem
   `AlgebraicGeometry.isSheaf_fpqc_sheafify_picardDegree`, whose exact body is `by sorry`.
   Printed axioms of both original declarations and every new public declaration in a scratch
   copy. All seven new proved declarations use only the three permitted axioms. Both original
   declarations also use upstream `sorryAx`, and the new sheaf theorem uses `sorryAx`; no
   other axiom occurs. Read the constructed data in `isLimit_pointwisePullback`: the lift,
   factorization and uniqueness fields are explicit; its arbitrary index only uses the stated
   nonemptiness. No forbidden axiom/unsafe/opaque/extern construct, holed definition, or
   arbitrary witness chosen from an unproved existence theorem occurs in the delivery.

3. **Split statements and mathematical checks: pass after source repairs.** Read Stacks
   [01ZM](https://stacks.math.columbia.edu/tag/01ZM),
   [023V](https://stacks.math.columbia.edu/tag/023V),
   [02VW](https://stacks.math.columbia.edu/tag/02VW),
   [01ZY](https://stacks.math.columbia.edu/tag/01ZY),
   [00JS](https://stacks.math.columbia.edu/tag/00JS),
   [02W0](https://stacks.math.columbia.edu/tag/02W0),
   [0D28](https://stacks.math.columbia.edu/tag/0D28),
   [0D2B](https://stacks.math.columbia.edu/tag/0D2B),
   [023T](https://stacks.math.columbia.edu/tag/023T) and
   [056U](https://stacks.math.columbia.edu/tag/056U).
   Scheme-model spreading has exactly the locally finite presentation, quasi-compactness
   and quasi-separatedness assumptions needed by 01ZM. Universal-transport spreading
   constructs the double-product limit and factors a morphism over the second base; it
   does not assume that the finite model already represents Picard. Transport testing lifts
   one map for identity and three maps for the cocycle; their covering composite is flat
   and surjective, so 02VW permits cancellation. Refinement simply combines these proved
   statements. The finite-affine-open argument uses positive-degree graded prime avoidance
   and inverse images under affine morphisms, so it also works over finite fields, for an
   empty finite set, and with an empty coordinate type (then the target projective space is
   empty). The pullback-limit construction handles a singleton or disconnected nonempty
   index category: its explicit compatibility hypotheses identify the maps to the fixed base.
   The generic representability theorem glues the universal section along the base-changed
   fpqc cover, then proves local bijectivity; it works for the identity cover and empty schemes.

   The one open theorem is strictly the fpqc sheaf condition, with no representing object,
   cartesian square or transport-invariance assumption. Its plan is valid: 056U supplies a
   finite separable point extension; 0D28 identifies normalized classes with the relative
   Picard sheaf; 0D2B gives uniqueness of normalized morphisms; 023T glues normalized bundles
   and their morphisms. Degree is checked after surjective residue-field base change.
   The empty test scheme has its unique class for every integer degree, and no rational
   point over the original field or infinitude of that field is assumed. This hole is a
   proper part of the argument, not a renamed representability statement. Independent
   LeanFinder, Loogle and Mathlib grep queries for rigidified Picard/fpqc sheaves found no
   exact match. Read `Picard.Defs.isSheaf_picardFunctorNormalized` and the normalized
   descent modules: their existing uniqueness argument still invokes fppf separatedness,
   so closing this hole requires a substantial fpqc uniqueness construction, not an
   immediate application. The source proof and complete remaining proof are in its docstring
   and node. Corrected the source's lemma tag from the section tag 0D24 to 0D28/0D2B,
   and the erroneous epimorphism citation 02L3 (open-immersion descent) to 02VW.

4. **Route and pruning: pass after bookkeeping repairs.** Read
   `dag/units/sk-prop-jacobian-descent.json`, including its statement, all steps and `realized`
   (currently empty lists). The geometric Jacobian, canonical datum, finite model, effective
   descent, representing isomorphism and equivariance route all remain. Pointwise pullback
   limits avoid a separate tensor-product limit theory; faithfully flat cancellation avoids
   spreading equality constraints. Existing properness and quasi-projectivity descent give
   the projective embedding. Compared Mathlib connected-pullback and functor-category
   pullback APIs, the upstream coordinate-cover argument, and `AmpleFiniteSetAffine`:
   none is an immediate replacement for these exact supporting interfaces. Removed the
   redundant public Limits imports and completed the list of old direct dependencies no
   longer used. The report distinguishes closing two original placeholders from the one
   new hole and the representability decomposition; it claims net direct holes +1 and
   no globally pruned module, not global target completion.

5. **Nodes against Lean: pass after repairs.** Matched each new node's Lean statement and
   module to its declaration, and checked the proof-step `uses` union against `proof_deps`.
   Corrected the two Step-7 nodes' blueprint parent/location: they serve the general-field
   functorial identification, not finite-level scheme construction. Made the refinement
   node self-contained and stated quasi-separatedness explicitly in the finite-model nodes.
   Its projections compose as `r ∘ q_L`, as the Lean equation `qL ≫ r = q` requires.
   Replaced the remaining hole's unnecessary point-spreading dependency with the existing
   dense-separable-points theorem. Aligned the general-field node's Steps 5 and 6 with the
   existing Lean proof: group operations come from Yoneda after representation, and smooth
   relative dimension is descended directly. Recorded LeanSearch's failures as unavailable.
   No target statement, unit record, or existing declaration signature changed.

Changes by this reader: redundant public Limits imports removed; source tags and new-node
blueprint locations corrected; finite-model/refinement statements made explicit; the open
sheaf theorem's source proof shortened using finite separable closed points; general-field
DAG Steps 5–6 and dependency pruning aligned with Lean; axiom qualifications and the full
independent reading added to this report. No additional hole was introduced or closed.
