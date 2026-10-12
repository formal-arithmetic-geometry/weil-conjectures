## What changed

Change record: `coord/changes/stalk-tensor-proof.md`.

Proved `SheafOfModules.stalkTensorIso` with its original statement, visibility, and
public imports. Added the fully proved module `Sheaf.Topology.PresheafStalkTensor`
and its theorem `PresheafOfModules.exists_stalk_tensor_iso`. The sheaf comparison
composes its presheaf comparison with the inverse sheafification stalk map.
Naturality follows by cancelling that map and checking pure tensor germs.
Private helpers construct the presheaf stalk functor over the CommRingCat stalk,
prove its laws, identify the tensor unit map with the adjunction tensorator,
and prove that its stalk map is invertible. Updated both DAG records attached
to the item and added the presheaf comparison record. Proof imports remain private.

## Proved and sorry left

Closed the one original hole: `SheafOfModules.stalkTensorIso`, attached to
`lem-pc-ringed-space-module-stalk-tensor` and its scheme specialization
`lem-weil-pbc-module-stalk-tensor`. Added no holes. The new theorem
`PresheafOfModules.exists_stalk_tensor_iso` is fully proved, as are all private
helpers. No `sorry` remains in either delivered module; this is a proof, not a
decomposition. The direct construction also covers zero modules, the zero ring,
and arbitrary nonempty neighborhood systems; the point assumption supplies a
neighborhood even when no proper open neighborhood exists.

## No longer needed

Removed the proof import `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`.
The item no longer uses `lem-weil-pbc-filtered-colimit-tensor-varying-rings` or
that module: the direct germ construction proves its needed neighborhood case.
No claim is made that other targets no longer need this general algebra lemma.
The duplicate scheme node now uses only the general ringed-space node, so its
old direct dependencies are no longer separately needed by that specialization:
`def-pur-sheaf-tensor-product`, `def-weil-pbc-module-stalk`,
`def-weil-presheaf-modules-sheafification`,
`lem-weil-pbc-filtered-colimit-tensor-varying-rings`, and
`lem-weil-pbc-stalk-sheafification-space`. The definitions and sheafification
stalk lemma remain used by the general ringed-space proof.
The public tensor-product and module-stalk imports remain required by the
statement; `Sheaf.Topology.PresheafModuleStalkFunctor` supplies stalkAddMap.
The unit statement and realized proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The given PresheafOfModules.moduleStalkFunctor takes scalars in a RingCat stalk;
the target uses the CommRingCat stalk. These are distinct chosen colimits, so a
definitional identification is invalid. A private functor with the required
scalar ring is constructed and proved here, without changing any interface.
The generic colimit theorem is stated for preorder-indexed diagrams, while
stalks are defined over the opposite neighborhood category; the direct proof
avoids the reindexing and scalar-transport glue. The existing proof docstring
records the original colimit plan; the implementation and updated DAG use the
direct common-neighborhood construction of its presheaf step.
Stacks Sheaves Tag 007K explicitly treats extension of scalars, not two arbitrary
module factors; the new lemma cites the presheaf part of the omitted proof of
Modules Tag 01CB and records 007K only as the scalar-extension special case.
The source text was read in the local Stacks checkout. LeanSearch returned
Internal Server Error; LeanFinder, Loogle, and Mathlib source searches ran.
The existing change-of-rings presheaf stalk node was read and is distinct:
its first factor is a ring, and its module factor is required to be a sheaf.

## New nodes

`lem-pc-presheaf-module-stalk-tensor`, in
`dag/nodes/sec-picard-framework/lem-pc-presheaf-module-stalk-tensor.json`, is
realized by `PresheafOfModules.exists_stalk_tensor_iso` in
`lean/Sheaf/Topology/PresheafStalkTensor.lean`. It states only the presheaf
comparison step, is already fully proved, and creates no proof obligation.
No definition, existing statement, or public import changed, and no forced
adaptation is needed. The command-environment review is documented in
coord/changes/stalk-tensor-proof.md.

## Earlier second reading (a previous round; superseded)

Second reader, repair round: I read both delivered Lean modules, all three
node records, the repository's module-stalk functor, and the two unit records
with the statements and proof bodies open. This reading replaces the earlier
checklist; the following checks concern the actual mathematical constructions.

1. `SheafOfModules.stalkTensorIso` quantifies over
   `X : AlgebraicGeometry.RingedSpace` and `x : X`. There is no scheme,
   locally-ringed-space, local-ring, finiteness, or local-freeness hypothesis.
   Its `R` is the structure sheaf with scalars forgotten to `RingCat`, and
   `S = RingedSpace.moduleStalkFunctor X x` takes values in
   `ModuleCat (X.presheaf.stalk x)`. Thus every `Φ F G` is an isomorphism
   over that commutative stalk ring, not merely an additive isomorphism.
   This matches `lem-pc-ringed-space-module-stalk-tensor`; taking
   `X.toRingedSpace` gives the scheme node
   `lem-weil-pbc-module-stalk-tensor` without extra assumptions. Comparing
   the repository and delivered theorem confirms the statement is unchanged.

2. The first clause specifies the canonical map by sending
   `germ(θ(s ⊗ t))` to `germ(s) ⊗ germ(t)`. Here `θ` is exactly the
   sheafification adjunction unit on `F.val ⊗ G.val`, followed by
   `(forget R).map (tensorObjIsoSheafification F G).inv`.
   `tensorUnitMap` abbreviates this composite. The private `commStalkFunctor`
   uses the same commutative stalk ring as `S`; `commStalkMap_linear`
   checks scalar compatibility on a common neighborhood.
   `tensorUnitMap_stalk_isIso` uses stalk invariance of abelian
   sheafification and reflection of isomorphisms by forgetting scalars.
   The constructed `Φ` is the inverse of this stalk map followed by the
   presheaf comparison `e`. The first proof branch uses `stalkMap_germ`
   and `IsIso.hom_inv_id_assoc` to recover precisely the stated formula.
   The choices of `e` satisfy the formula on all pure tensor germs, which
   generate the source stalk; they do not introduce an arbitrary comparison.

3. The second clause is naturality for the very same `Φ` bound by the
   existential, in both sheaf morphisms `f` and `g`:
   `S.map (f ⊗ₘ g) ≫ (Φ F' G').hom =
   (Φ F G).hom ≫ (S.map f ⊗ₘ S.map g)`.
   `tensorUnitMap_natural` identifies `θ` with the right-adjoint lax
   monoidal tensorator, so tensorator naturality supplies the square
   before taking stalks. The proof cancels the invertible `θ` stalk map,
   then `hcancel` reduces both composites to the already chosen `e` maps.
   Every remaining stalk element has a section representative; tensor
   induction reduces equality to pure tensors. On those, the germ formulas
   for `e`, `TensorProduct.map_tmul`, and `stalkMap_germ` give the square.
   No independently chosen natural isomorphism replaces the first-clause map.

4. `PresheafOfModules.exists_stalk_tensor_iso` matches
   `lem-pc-presheaf-module-stalk-tensor` with arbitrary
   `X : TopCat`, `R : X.Presheaf CommRingCat`, and arbitrary module
   presheaves `F,G` over `R ⋙ forget₂ CommRingCat RingCat`. Neither `R`
   nor the factors are assumed to be sheaves. The tensor restriction
   formula builds the cocone defining the forward additive map `p`.
   For the reverse pairing, `rep` puts both germs on a common neighborhood.
   `uniq` applies `germ_eq` separately to the factors, intersects the two
   resulting neighborhoods, and uses restriction composition and `move`
   to equate their tensor germs. Consequently the chosen value `b m n`
   is independent of representatives, as recorded in `hb`; its defining
   existence statement and `uniq` determine the value uniquely.
   `baddM` and `baddN` prove additivity on common representatives.
   `bsmulM` and `bsmulN` first represent an arbitrary stalk-ring scalar,
   restrict both vectors into its neighborhood using `repAfter`, and use
   `germ_smul` with the tensor scalar identities. These prove bilinearity
   over `R.stalk x` and construct `β` and its linear tensor lift `q`.
   `hqp` proves `q (p z) = z` by section representation and tensor induction;
   `hpq` proves `p (q z) = z` by tensor induction on stalk tensors and common
   representatives of their factors. Injectivity of `q` then transports
   its scalar compatibility to `p`, giving the linear isomorphism and the
   exact pure-tensor germ formula in the node. Zero modules and the zero
   ring require no cancellation assumption; for any specified point,
   the whole space supplies a neighborhood. Both delivered modules have
   complete proof bodies, with no new holes or forbidden declarations.

5. I read the actual local source at
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/modules.tex`,
   label `lemma-stalk-tensor-product` (Tag 01CB), and
   `/home/ubuntu/work-bp/sheaf/literature/stacks-project/sheaves.tex`,
   label `lemma-stalk-tensor-presheaf-modules` (Tag 007K).
   The former states the ringed-space isomorphism and functoriality and
   omits its proof. The latter treats extension of scalars along a ring
   presheaf morphism, not two arbitrary module factors, and also omits
   its proof. Thus the new node correctly records an agent-written direct
   germ argument for the presheaf comparison underlying 01CB; it does not
   claim that 007K contains this general proof.
   In `dag/units/sk-thm-picard-duality.json`, `realized.statement` and
   the sole `realized.steps` entry are empty. In
   `dag/units/sk-thm-reduction.json`, the realized statement and all seven
   realized step lists name the reduction, finite-morphism, locality,
   Chow, projective-space, composition, and cancellation results; none
   names `lem-weil-pbc-filtered-colimit-tensor-varying-rings`.
   That removed node is a lower algebraic tool of the old stalk proof,
   not a realized unit statement or step. Replacing its application by
   the proved presheaf germ construction therefore preserves the unit
   route. The updated ringed-space node follows the presheaf comparison,
   sheafification stalk invariance, and naturality proof above, while the
   scheme node invokes the ringed-space result. The removed proof import
   is unused; the retained imports supply the stalk maps, sheafification,
   and tensor constructions actually invoked.


## Second reading by Q2

Independent second reader, 2026-10-13. I read both delivered modules in full,
compared the existing module with the repository using diff, and read the
three delivered node records, the original two nodes, both unit records,
the module stalk functors, and the existing change-of-rings comparison.

1. Interface: PASS. The diff leaves the complete existing
   `SheafOfModules.stalkTensorIso` signature byte for byte unchanged, including
   the germ characterization and naturality for the same existentially bound
   family. Its public imports and visibility are unchanged. The added functor,
   tensor-unit map and monoidal instances are private. No existing definition
   changed and no forced adaptation was added. The theorem still concerns an
   arbitrary ringed space, not merely a scheme or locally ringed space.
2. Proof: PASS. Launcher compilation of both files in import order was clean
   (9.9 and 38.2 seconds). Scratch copies with `#print axioms` compiled too:
   both public theorems use exactly `propext`, `Classical.choice`, `Quot.sound`.
   Neither module contains `sorry`, a forbidden declaration or a hollow
   definition. For the presheaf inverse, `ex` is proved from germ representation;
   `uniq` proves independence after intersecting the two equality neighborhoods.
   Thus choosing `b` does not choose arbitrary data from an unproved existence
   assertion. `hqp` and `hpq` prove both inverse identities, and injectivity of
   the linear inverse proves the forward map is linear. In the sheaf proof,
   reflection through the forgetful functor establishes invertibility of the
   actual sheafification stalk map; cancellation and tensor induction establish
   the required germ formula and naturality of the constructed family.
3. New statement: PASS. No statement is split off with `sorry`. The new proved
   presheaf comparison is strictly the presheaf step: arbitrary commutative
   ring presheaf and two arbitrary module presheaves, with an isomorphism over
   the commutative stalk ring and the specified pure-tensor germ formula.
   I checked zero factors, the zero ring and a one-point space: all constructions
   and identities still apply, with no nonzero, flatness or finiteness hypothesis.
   An empty space has no point parameter, so contributes no excluded case.
   Independent searches used LeanFinder query "tensor product commutes with
   germs of module presheaves", Loogle query '"stalk", "tensor"', and grep
   query 'tensor.*germ|germ.*tensor|stalkTensor'; these returned sectionwise
   tensor constructions or unrelated spectrum results, no matching theorem.
   Repository and upstream searches also found no applicable shorter comparison.
   The existing `stalkChangeOfRingsPresheafIso` requires sheaf factors and treats
   extension of scalars, so cannot supply this arbitrary two-factor result.
4. Route and pruning: PASS. I read Stacks `modules.tex`,
   `lemma-stalk-tensor-product` (01CB): arbitrary ringed space, two module
   sheaves, canonical stalk-ring isomorphism and functoriality, proof omitted.
   I also read `sheaves.tex`, `lemma-stalk-tensor-presheaf-modules` (007K):
   extension of scalars only, proof omitted. The source attribution correctly
   describes the new general germ proof as agent-written. The old varying-ring
   colimit node is absent from both units' realized statements and steps;
   replacing that lower algebra tool preserves the unit route. The general node
   removes exactly that dependency; the scheme node now invokes the general
   result and removes its five former direct dependencies, listed explicitly
   above. The public imports supply the statement, and all added imports are
   private proof imports supplying the germ comparison or sheafification facts.
5. DAG: PASS. Existing node edits are confined to `proof`, `proof_deps` and
   `proof_origin`. The general node describes the direct presheaf comparison,
   sheafification stalk isomorphism and tensorator naturality used in Lean;
   the scheme node specializes that same ringed-space result. The new node
   matches the presheaf theorem, includes its full germ proof, source,
   statement dependencies, proof dependencies, provenance, creation record,
   blueprint ancestry, searches and Lean record. No new proof obligation hides
   in its construction. The report still closes one original hole and adds none.

Changes by this reading: made the list of removed scheme-node dependencies
explicit and added this independent review. No Lean proof, statement, definition,
import or node required repair. Scratch axiom probes were removed after checking.
