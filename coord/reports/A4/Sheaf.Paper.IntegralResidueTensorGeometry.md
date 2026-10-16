## What changed

Replaced the sole hole in `integralResidue_tensorGeometry` by a complete naturality
and cancellation proof. Package both routes as natural transformations. On a
representative whose ordinary pullback is K-flat, an explicit target comparison
is invertible. The two route-computation formulas identify their composites with
the same constructed homotopy-level map. Cancel that comparison, then use
naturality and an isomorphism from the representative to descend to every object.
The original theorem signature and both coefficient-construction bodies are unchanged.

Constructed the model from the tensor-extension counit, exact-pullback counit,
inverse braiding and ordinary tensor comparison. Proved
`CategoryTheory.Functor.tensorModelTarget_isIso` and the coefficient-transport
specialization `integralResidue_pullback_preservesFlat`. The latter uses the new
general inverse-image flatness obligation. Moved the two unchanged coefficient
constructions to an acyclic module and publicly re-exported them from Geometry.
Change record: `coord/changes/A4-residue-tensor-presentations-relocation.md`.
No module held by another group is adapted.
The generic and specialized model-target definitions are irreducible. The cancellation proof
unfolds its two wrappers with `delta` only when establishing invertibility; the route comparison keeps the
tensor construction folded.

Validation: all seven delivered Lean modules compiled in import order. The
unchanged direct consumer `Sheaf.Paper.IntegralResidueTensorSquare` compiled against
the overlay as well. Its temporary unchanged source copy was then removed. The
original theorem signature and both relocated definition bodies were compared
against the shared repository.

## Proved and sorry left

Original holes: 1. Closed upper hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry`.
The item has zero local holes. Added holes: 3. This is a decomposition, not a net
proof. The delivered declarations' hole arithmetic is -2; the ledger determines
the net change in the targets' full import closure.

- `AlgebraicGeometry.ProEtale.inverseImageModule_preservesFlat`
  (`new-proetale-inverse-image-module-flat`): needs tensor compatibility for the
  internal-to-sectionwise module equivalence and the local finite-relation
  inverse-image calculation. Existing constant ModuleCat pullback lemmas have a
  different coefficient category and do not apply directly.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model`
  (`new-integral-residue-tensor-route-model`): needs counit normalization of the
  fixed tensor presentation and compatibility of the derived tensor comparison
  with inverse braiding. A generic normalization proof was compiled during this
  session; further generic glue remains in scratchpad and is not delivered.
  The normalization proof factors the presentation into `leftDerivedUnique`,
  `leftDerivedNatIso` and the coefficient/braiding isomorphisms. Cancel the latter
  two, then apply `leftDerivedNatTrans_app` to each remaining derived comparison.
  This yields the specified tensor counit followed by Qh of the inverse
  `homotopyTensorSingleIso`; the remaining task is moving it through the derived
  tensor comparison and its inverse braiding.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarRoute_model`
  (`new-integral-residue-scalar-route-model`): needs the inverse-mate scalar-counit
  identity combined with ordinary balanced tensor and coefficient-unit comparisons.
  Its formula contains no derived oplax tensor comparison.

Each route formula computes one route into an explicit ordinary homotopy tensor.
Neither restates the square under a renamed representative. Neither assumes
K-flatness of the source complex or flatness of the residue coefficient. Image
K-flatness is used only in the proved target-comparison cancellation. Every added
hole is a named public theorem with exactly `:= by sorry`, full proof docstring
and matching node. All model data are explicit constructions.

Also proved without an added hole in their modules:
`CategoryTheory.Functor.tensorModelTarget_isIso` and
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_pullback_preservesFlat`.
The latter depends on the general flatness obligation listed above.

## No longer needed

No module is pruned. From Geometry's old direct `proof_deps`,
`new-integral-residue-tensor-presentation`, `new-integral-residue-ordinary-monoidal`,
and `new-integral-residue-derived-pull-square` are delegated to the presentation,
model and route nodes; all remain used transitively.
`new-integral-residue-derived-monoidal` remains a direct dependency.

Removed Geometry's redundant direct imports TensorPresentation, OrdinaryMonoidal
and PullSquare; TensorPullPresentation re-exports their public interfaces.
TensorModel now imports TensorPresentation and OrdinaryMonoidal directly instead
of the unrelated pulled-coefficient presentation. ScalarRouteModel explicitly
imports that pulled-coefficient presentation because its statement uses it.
Both route modules obtain their monoidal interfaces through TensorModel.

The two flatness modules no longer import OrdinaryMonoidal. The general flatness
statement instead imports the ordinary pullback and module-tensor interfaces;
its three proof-plan interfaces are plain imports. The specialization needs only
the coefficient comparison interface and PreservesFlat publicly, with the
general flatness theorem imported for its proof. Their stale ordinary-monoidal
node dependencies were removed.

No scratchpad normalization, generic-route or derived-braiding module is
delivered or imported. Unchanged dependency source copies used to build missing
local artifacts were removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The plan's flatness and balanced-tensor steps had no Lean lemma at the required
internal-module interface. The constant-coefficient ModuleCat flatness result has
a different ring/category. The existing sectionModuleEquivalence supplies an
underlying equivalence but does not expose its tensor compatibility. These are
missing interfaces, not counterexamples; no original statement is disputed.

The coefficient presentation on X must remain canonical: an arbitrary
isomorphism could differ by an automorphism and invalidate the square. All data
are fixed here. The model uses inverse braiding and does not assume a separately
installed symmetric derived instance. New formulas were checked at zero complexes,
identity maps, empty schemes and zero coefficient objects; the counits and tensor
presentations remain defined, and image K-flatness is used exactly when the tensor
counit is inverted. The blueprint unit and its realized steps are preserved.

## New nodes

`def-weil-pbc-integral-residue-tensor-pull-presentation`: the two unchanged
coefficient constructions, moved to avoid an import cycle.

`new-proetale-inverse-image-module-flat`: general flatness for internal module
inverse image followed by transport along a coefficient isomorphism.

`new-integral-residue-pullback-preserves-flat`: the proved specialization to the
actual ordinary integral inverse image via an explicit transport isomorphism.

`new-integral-residue-tensor-model`: explicit generic and specialized common maps,
and the proved invertibility of the target comparison on K-flat-image representatives.

`new-integral-residue-tensor-route-model`: computation of the tensor route in the
ordinary homotopy model.

`new-integral-residue-scalar-route-model`: independent computation of the scalar
route in that same model.

Change record: `coord/changes/A4-residue-tensor-presentations-relocation.md`.

## Second reading by A4

1. Compared every delivered module with the shared repository. Geometry is the
only pre-existing module changed. Its theorem signature is byte-for-byte
identical. Both relocated coefficient definitions, including their attributes,
signatures and bodies, are byte-for-byte identical after excluding the
new source/blueprint docstrings. The relocation is declared in
`coord/changes/A4-residue-tensor-presentations-relocation.md`; all twelve
transitive users were rechecked with `downstream.py --uses`. No target statement
or construction data changed, and no module held by another group was adapted.

2. Read the complete proof and explicit model constructions. The representative
is chosen only inside a proof; every defined model map is a fixed composite of
existing counits and comparisons. There is no arbitrary choice of data from a
holed existence theorem. The only three local holes are exactly the named public
theorems listed above, each with its source, proof docstring and DAG node.
All seven modules compiled cleanly in import order against the published library
(Geometry: 30.4 s).
The scratch `#print axioms` check covered every public declaration delivered:
only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` occur.
All delivered definitions and `tensorModelTarget_isIso` use only the three
standard axioms; none of their data depend on `sorryAx`.

3. Checked each split separately. The flatness statement is the isomorphic-ring
case of [Stacks Tag 05VD](https://stacks.math.columbia.edu/tag/05VD), verified against the source. Its proof plan imports
the internal/sectionwise equivalence and both local finite-relation criteria.
The tensor formula normalizes just the tensor route; the scalar formula
normalizes just the inverse-mate route into the same explicitly constructed
ordinary model. Neither asserts equality of those routes. The coefficient
counit remains a morphism on arbitrary P, so neither formula requires a flat
residue quotient. At zero complexes the maps vanish; at identity pullback the
counit normalizations reduce to the ordinary tensor presentation. Zero
coefficients and empty schemes impose no additional hypothesis. Repeated
LeanFinder/Loogle/grep searches with different queries found generic scalar
adjunction and sheaf pullback APIs, but no duplicate of these internal-module
computations. Existing constant-coefficient Noetherian flatness lemmas do not
apply to these continuous coefficient ring objects. The remaining statements
are true, independent parts of the argument; this remains a decomposition with
net hole count -2, not a completed proof of the import closure.

4. Read the naturality/cancellation descent from the top down. The target
comparison is invertible exactly when the image of P is K-flat; no K-flatness
of P itself is assumed. After cancellation the two natural transformations
agree on such representatives, and precomposition with the representative
isomorphism gives equality on every object. The old proof-dependency steps
remain in use through the lower computations. Checked
`dag/units/sk-thm-properbasechange.json`: none of its realized statement or step
nodes is bypassed. Removed imports and delegated direct dependencies are listed
under No longer needed.

5. Checked node declarations against the Lean signatures, `proof_deps` against
the unions of step citations, and the actual naturality/cancellation route
against `proof` and `proof_origin`. Removed stale ordinary-monoidal dependencies
from the two flatness nodes and the stale pulled-coefficient dependency from the
model node. Added the ordinary-monoidal dependency actually used to construct
the specialized model map, and recorded the independent search results in the
three holed nodes.

Changes by the second reader: supplied the omitted proof-plan imports for the
flatness obligation; narrowed public dependencies of the flatness and model
modules; made route interfaces explicit; corrected dependency records and the
list of removed direct imports. The generic target comparison is kept
irreducible so its explicit construction remains folded during the upper proof.

The initial full compile hit the 60-second limit in Geometry. Isolating the
invertibility step identified excessive definitional reduction while unfolding
the generic tensor target. Marking the generic target irreducible and using
`delta` to unfold only the two explicit wrapper definitions retained exactly
the same data and proof route; the resulting full theorem compiled in 38.4 s.
No theorem or file was split to avoid the timeout.

Final validation: the unchanged direct consumer
`Sheaf.Paper.IntegralResidueTensorSquare` compiled against the delivered overlay
in 27.1 s. Its scratch source and the axiom-check source were removed. Every
DAG `lean.statement` occurs verbatim in its delivered source, all proof-dependency
lists equal their step-citation unions, and only the three reported named holes
remain in the seven delivered modules.

The second reader also removed nine non-delivery modules from the local compiled
overlay, including unchanged dependency copies and unused scratch modules. The
published versions of the dependency artifacts were present and had different
hashes. The first push attempt was stopped for this cleanup. All seven source
modules were then rebuilt successfully against only the published library plus
the seven delivered modules; no dependency source was copied or delivered.

The repeated scratch-copy axiom check and unchanged consumer compile both passed
against the cleaned overlay. Only the seven delivered modules remain in
`.lbuild`; the axiom check again found only the three standard axioms and the
expected `sorryAx` in the open proof dependencies.
