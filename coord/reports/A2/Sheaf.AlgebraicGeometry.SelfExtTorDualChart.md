## What changed

`Sheaf.AlgebraicGeometry.SelfExtTorDualChart` now has a complete Lean proof of
`AlgebraicGeometry.selfExt_tor_dual_chart`, with its signature and public imports unchanged.
The proof obtains common complex representatives, constructs the evaluation map, transports
its target using the internal Hom bifunctor, and proves the required restricted maps invertible
by expanding the two functor images of the composite.

Two proof imports and two new modules supply the remaining obligations:

- `Sheaf.Algebra.Homology.HomologyEvaluation`: the cycle characterization of evaluation,
  the explicit quasi-isomorphism-roof predicate `HasFiniteFreeZeroModel`, and the generic
  evaluation/perfection theorem. Its definition `homologyEvaluation` selects a map from an
  **existence-and-uniqueness** theorem whose cycle formula determines the map. It does not
  select arbitrary data from mere existence. The termwise open/over restriction functor is
  constructed using a separately proved zero-morphism theorem.
- `Sheaf.AlgebraicGeometry.SelfExtTorResolutionModel`: existence of common complexes T and J,
  pure degree-zero cohomology of J, three object isomorphisms, and regular-chart finite free
  zero-differential models. Its statement contains no Ext-to-dual-Tor morphism or assertion
  that such a morphism is invertible. The witnesses are obtained inside the theorem proof;
  no definition chooses a resolution from this unproved existence result.

The projection definition uses the existing `homComplex_projections_exists` interface,
which avoids repeated unfolding of the large Hom-bifunctor existence type.

All three modules compile together with `lcompile.py --all`; the only remaining holes are
whole proofs of the two named public theorems listed below. No existing definition, statement,
visibility, or target was changed. Only the assigned node's proof fields were updated.

## Proved and sorry left

Closed: `AlgebraicGeometry.selfExt_tor_dual_chart`
(`lem-sc-self-ext-tor-dual-chart`), one of the original module's one holes.

Added, still `:= by sorry`:

- `CategoryTheory.exists_homologyEvaluation`
  (`lem-sc-homology-evaluation-formal-complex`). This is a generic Hom-complex evaluation
  theorem for arbitrary complexes on a scheme, including its locally formal perfection
  calculation. It has no immersion, Koszul sequence, or derived self-Ext/Tor hypotheses.
- `AlgebraicGeometry.exists_selfExt_tor_resolution_model`
  (`lem-sc-self-ext-tor-resolution-model`). This constructs common resolutions and their
  chart models; it does not assert the comparison morphism sought by the original theorem.

This is a **decomposition**, not a completed axiom-free proof: one upper hole closed and two
strictly smaller obligations added, net -1 holes if both new nodes enter the import closure.
The evaluation definition depends on the first named theorem; its data are uniquely specified
by evaluation on cycle representatives. There are no holes in definitions or private helpers.
`moduleOpenOver_preservesZeroMorphisms` and `homologyEvaluation_isIso` are proved.

The new statements were checked mathematically on the zero complex, empty chart and zero
quotient ring: the complexes and maps are zero and the characterization determines the unique
map. A length-zero regular sequence gives T represented by O_Z[0], so degree-zero evaluation
is multiplication and other degrees vanish. For n above the generator length the local finite
model has zero relevant terms. The generic finite-free argument also allows rank zero and an
arbitrary degree-zero coefficient module. None of these cases needs a proper-ideal or
positive-length hypothesis.

## No longer needed

No original public import was removed. The proof no longer needs these planned nodes
and their modules:

- `lem-sc-derived-hom-finite-free-model` /
  `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`: eG is now obtained globally by
  derived pullback/internal-Hom adjunction, followed by Hom into the K-injective J on Z.
  The finite-free chart calculation is performed by the generic evaluation lemma.
- `lem-sc-derived-internal-hom-restrict-open` /
  `Sheaf.Paper.DerivedInternalHomRestrictOpen`: the geometric model restricts derived
  pullback representatives and the generic evaluation restricts the ordinary Hom complex;
  the required comparison is `lem-sc-hom-complex-restrict-open` instead.

The original `new-j3-koszul-projective-resolution` and
`lem-sc-affine-quotient-resolution-sheafification` remain needed below the resolution-model
node. No claim is made that the two pruned modules have no other target consumers. All final
proof imports are used. Redundant imports in the newly written evaluation module were removed
before its final compilation.

## Where the brief, the DAG or earlier work was wrong

The assigned module did not import its four recorded proof dependencies. Reading their
signatures showed that none supplies the global pairing or a joint self-Ext/self-Tor model:
there is a genuine construction gap between the resolution-computation statements and the
original conclusion. The reduction makes this gap explicit as the common-model theorem,
and separates the generic homological evaluation calculation from the geometry.

The final route keeps the quotient Koszul computation and does not bypass the unit's
statement or realized steps; the unit record has no realized node bound to this item.
The new model also uses the existing derived internal-Hom pullback adjunction and the
qcqs derived projection formula as generic tools, with the hypotheses supplied by a closed
immersion and its quasi-coherent structure-sheaf pushforward. It uses exact closed pushforward
and its fully faithful counit as generic tools; the exactness statement is about underlying
abelian sheaves and must be transported to module sheaves by the faithful exact forgetful
functor. The evaluation node uses the existing quasi-isomorphism invariance of Hom into
K-injectives and restriction of Hom complexes. These tool uses do not change the unit's
Koszul route.

LeanSearch was unavailable (Internal Server Error); it was recorded as unavailable, not as
absence of a result. LeanFinder, Loogle and logged Mathlib grep searches found no exact result.
Project-wide searches found only the assigned map and its nested-chart consumer. Whole
blueprint searches for Ext/Tor, homology evaluation and derived self-intersection found no
matching blueprint statement. The local literature checkout contains lists only; the cited
Stacks pages 0A8X, 08DH, 0BQY, 068G, 08I3, 08DL and 08KS were read online. No literature files
or project files outside the sandbox were written by the worker.

## New nodes

`lem-sc-homology-evaluation-formal-complex`, in
`dag/nodes/sec-picard-framework/lem-sc-homology-evaluation-formal-complex.json`, records the
cycle-characterized generic evaluation and its finite free zero-model calculation. Its
source and complete proof in words are also in `HomologyEvaluation.lean`. It includes the
explicit open/over complex restriction construction used by both new modules.

`lem-sc-self-ext-tor-resolution-model`, in
`dag/nodes/sec-picard-framework/lem-sc-self-ext-tor-resolution-model.json`, records the common
complex representatives obtained by derived pullback and injective resolution, their Ext/Tor
object identifications, and their Koszul zero-differential chart models. Its source and
complete proof in words are also in `SelfExtTorResolutionModel.lean`.

Both nodes inherit the assigned item's chapter and unit and point to the same finite-duality
blueprint ancestor. The existing comparison node now records the Lean composition route.
There are no change records and no forced adaptations.

## Second reading by A2

1. **Interfaces: pass.** I diffed the assigned module against the repository. Its existing
   theorem signature is byte-for-byte unchanged. The two added imports are proof-only.
   No existing definition, visibility, or target statement changes; no change record or
   forced adaptation is required.
2. **Kernel and holes: pass as a decomposition.** All three delivered modules compile
   individually with `lcompile.py`. A scratch probe printed axioms for the target, both
   split theorems, the evaluation definition, its projection, and both restriction
   declarations. They use only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   where the two split proofs remain open. In particular, the projection and restriction
   construction have no `sorryAx`. There are exactly two source holes, both whole named
   public theorem proofs with matching nodes and proof docstrings. No forbidden declaration
   or holed definition occurs. The evaluation witness is uniquely determined by its cycle
   formula, using local lifts through the two homology epimorphisms; the resolution witnesses
   are eliminated inside the target's existential proof and are not selected by a definition.
3. **Split statements: pass.** I checked the cycle formula, the finite-support Hom
   calculation, and the closed-immersion model reduction. For zero complexes, rank zero,
   empty opens, and the zero quotient the relevant morphisms are the unique zero-object
   maps. A length-zero Koszul sequence yields the unit in degree zero; degrees above its
   length vanish. Negative n in the generic evaluation theorem gives the same shifted
   finite-product calculation. Neither split theorem restates the target: the generic
   theorem has no immersion and the model theorem has no Ext-to-dual-Tor map. Independent
   searches used “universal coefficient edge morphism”, “cohomology of internal Hom”, and
   `CohomologyClass.toHom`. LeanFinder/Loogle return Hom-complex classes and homotopy maps,
   not this sheaf-valued evaluation or joint model theorem. Mathlib grep and searches in
   both project source roots found no exact replacement. The remaining obligations are
   substantial constructions and cannot be closed by these search results in a few minutes.
4. **Route and pruning: pass.** The composite of eG, evaluation, and the contravariant/
   covariant internal-Hom transport has the required type. Functor images of all three
   factors are isomorphisms on each chart. Both new proof imports are used. I checked all
   four old proof dependencies: the finite-free derived-Hom model and derived-internal-Hom
   open restriction are replaced; the two Koszul-resolution dependencies remain in the
   new model node. The unit's `realized` fields are empty, so no realized step is bypassed;
   the model's chart step retains the unit's Koszul route. The pruning list above describes
   replaced planned dependencies, not a claim that their modules leave every target closure.
5. **DAG: pass.** Existing-node changes are confined to proof fields. New-node statements
   and verbatim Lean signatures agree with the source; proof-step uses have the recorded
   union, and both nodes have sources, searches, creation records, split status, and the
   assigned chapter/unit/blueprint ancestor. The target node records precisely the Lean
   composition. The evaluation and model proof sketches account for their stronger generic
   hypotheses and their boundary cases.

**Second-reading changes:** corrected the description of Tag 08I3: it provides the pullback
internal-Hom evaluation mate, not directly the internal pullback/direct-image isomorphism.
Expanded the model theorem's proof docstring and DAG step with the tensor--Hom/derived
adjunction/Yoneda argument that supplies that isomorphism. No Lean statement or proof term
was changed. Added this independent review and its axiom/search evidence. The delivery
remains one upper hole closed and two lower holes added, hence a decomposition, not a
completed axiom-free proof.
