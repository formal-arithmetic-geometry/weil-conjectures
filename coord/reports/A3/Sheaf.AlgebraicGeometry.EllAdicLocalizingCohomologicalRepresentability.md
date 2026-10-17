## What changed

Replaced the assigned theorem's `sorry` by a compiling reduction with its original
signature, universes, visibility, coefficient certificate, and scheme hypotheses.
It proves essential smallness of the bounded constructible generators, uses the
localizing hull's minimality, obtains a small solution family, and applies a proved
cohomological solution-set criterion.

Four new modules contain three proved public theorems and one remaining obligation.
The proved arguments are local-presentation embeddings into products of right
adjoints and well-poweredness, finite Postnikov induction with small extension
classes, and a cofiber/kernel-killing construction followed by splitting an
idempotent. No existing definition or statement is changed.

The heart proof also proves joint zero detection for abelian sheaves. Cover
restrictions are conservative by the proved source-library localization theorem.
For the finitely many quasi-compact stratum immersions, private proved helpers adapt
the source-library section-vanishing argument to abelian groups. This avoids the
admitted `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` altogether.

Local presentation data are stored in a private structure. An earlier dependent
Sigma expression made elaboration exceed the single-file limit; the structure and
small pullback API bring the complete heart proof to approximately ten seconds.
All five modules compile through the prescribed launcher. Axiom probes show that
all three new proved public theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The assigned theorem's unchanged direct consumer
`Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` also compiled
against the sandbox overlay. Separate baseline and overlay probes print identical
elaborated signatures, including all hypotheses and universes.

## Proved and sorry left

One original hole is closed by decomposition:
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_cohomological_isRepresentable`
(node `lem-sfb-adic-localizing-cohomological-representability`). Its module now has
zero `sorry`. This is a decomposition, not a complete proof from standard axioms.

Exactly one hole is added, the only `sorry` in the five delivered modules:
`CategoryTheory.setGeneratedDerived_cohomological_solutionSet`, node
`lem-sfb-set-generated-derived-solution-set`, in
`lean/Sheaf/CategoryTheory/SetGeneratedDerivedSolutionSet.lean`.
It asserts a small family of weakly universal elements, without uniqueness or a
representing object. It still needs Neeman's well generation of a Grothendieck
derived category, Krause 7.2.1 on set-generated localizing subcategories, and the
perfect-generator cellular solution-set construction. Its docstring and node give
the argument and universe requirements. Searches found no existing Lean
implementation. The final argument from that family to representability is proved
separately, rather than left in this obligation.

New public theorems proved from the three permitted axioms, with no holes:

- `AlgebraicGeometry.ProEtale.constructibleModuleObjects_essentiallySmall`.
- `DerivedCategory.bounded_homologyProperty_essentiallySmall`.
- `CategoryTheory.cohomological_isRepresentable_of_solutionSet`.

Every private helper is proved. Syntactically one hole is closed and one added:
net zero. The delivery ledger gives the authoritative target-closure counts.

Edge cases checked in the arguments include empty schemes, zero coefficient rings,
empty generating classes, and empty cohomological intervals. No compactness of the
original constructibles or finite cohomological dimension of the base field is used.

## No longer needed

Removed the assigned module's proof import
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`; that module leaves
this item's project import closure. Its former node dependency
`def-weil-pbc-internal-abelian-sheaf-module-equivalence` is removed.

The former planned node `lem-weil-pbc-ring-sheaves-grothendieck`, with module
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`, is unnecessary:
`CategoryTheory.Mod.isGrothendieckAbelian` and the existing pro-etale sheaf instances
supply Grothendieckness directly. That module was a DAG dependency, not an actual
original direct import.

The planned node `det-brown-hypotheses-small` is replaced by two proved theorems for
the actual constructibility and bounded-homology predicates. It has no Lean
attachment, so no module is withdrawn. Descent-data classification, Ext-one
classification of glued strata, and compact generation of constructibles are not
needed. Neither `Sheaf.AlgebraicGeometry.NoetherianStratumDetection` nor its
`proEtale_isZero_of_stratum_cover` theorem is needed: the final heart proof proves
the zero-detection step itself. This avoids a provisional dependency and is not
counted as pruning a module from the original baseline.

The redundant direct proof import
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory` is omitted.
Its infrastructure remains used through the generic solution-set module's public
import; its module is not claimed as pruned. No unit statement or realized unit
proof step is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The assigned node lists `det-brown-hypotheses-small` without a Lean attachment.
Its constructible finite-Tor setting does not directly express this item's
`boundedConstructible` predicate. The heart and Postnikov proofs handle that
predicate explicitly. The module-object Grothendieck API also makes the planned
sectionwise sheaf-module equivalence unnecessary.

The blueprint ancestor helper does not follow the assigned node's `created.item`
module-name string as a node id. The new nodes explicitly retain its existing
`blueprint.from.node` ancestor and put the assigned node in `via`.

The remaining construction must use perfect generation in the coherent-functor
category; it cannot assume that the original constructible generators are compact
or that their Hom functors commute with sequential telescopes. This distinction
is recorded in the remaining theorem's proof in words.

## New nodes

`lem-sfb-constructible-module-objects-essentially-small` records the proved local
presentation/product embedding argument for any ring object. It includes proved
abelian-sheaf zero detection, using the source library's proved cover conservativity.

`lem-sfb-bounded-homology-essentially-small` records extension counting and Postnikov
induction for an essentially small, isomorphism-invariant heart property. It does
not require extension closure of that property.

`lem-sfb-cohomological-solution-set-representability` records the proved passage
from a small solution family to representation, including uniqueness.

`lem-sfb-set-generated-derived-solution-set` records the remaining well-generation
and cellular solution-set argument. It is the sole new admitted declaration.

There are no change records or forced adaptations: no existing signature,
definition, or other group's module is modified.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
