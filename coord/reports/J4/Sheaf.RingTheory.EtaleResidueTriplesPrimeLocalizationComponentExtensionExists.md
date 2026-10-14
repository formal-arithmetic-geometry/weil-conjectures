## What changed

Proved the unchanged declaration
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_exists`
in `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionExists`.
Only this Lean module and its existing DAG node are delivered. No statement,
public definition, target, or other module changes.

The proof uses the already proved `primeLocalization_etale_algebra_model` to obtain
an etale R-algebra C and a localization map i:C to t.B. Restricting the given
pointing constructs a global triple c with ring C, using Mathlib's explicit
`SpecToEquivOfField` equivalence. Every cocone leg inverts elements outside its
pointed prime, by unit refinement and naturality, so eta_c extends to C at that
prime. The localization denominators of i are outside this prime, giving
j:t.B to that same local ring. Set b to j followed by the extended leg.

For each compatible beta:s.B to t.B, finite presentation of s.B over R factors
beta followed by j through a principal localization of C. Point that stage by
its map into K; it gives actual global arrows from c and s. Naturality and
principal-localization extensionality identify its leg with the extension of
eta_c. Their composite with the descended map is eta_s, which proves beta;b=eta_s.
All eight private helpers are proved or explicit constructions; there is no
choice of arbitrary data from an unproved existence statement.

Added four ordinary proof imports: `Sheaf.RingTheory.PrimeLocalizationEtaleAlgebraModel`,
`Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`,
`WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`, and
`Mathlib.Algebra.Category.Ring.FinitePresentation`. The node's proof,
proof_deps and proof_origin now describe the implemented route.

The source ingredients are Stacks [00U2 (10)](https://stacks.math.columbia.edu/tag/00U2),
[00CR](https://stacks.math.columbia.edu/tag/00CR),
[00QO](https://stacks.math.columbia.edu/tag/00QO), and
[04GW](https://stacks.math.columbia.edu/tag/04GW).
Mathlib search used leanfinder, loogle and grep through msearch.py; local searches
found the already proved unpointed model and the general finite-presentation
factorization theorem. No duplicate or new intermediate obligation was introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_exists`
(node `new-lem-sbc-etale-triples-prime-localization-component-extension-exists`).
One of one holes closed; zero holes added or split off; zero holes remain in the delivery.
This is a complete proof, not a decomposition into new obligations.

A clean single-file lcompile.py compile succeeded. A separate verification compile
with `#print axioms` showed exactly `propext`, `Classical.choice` and `Quot.sound` for
the main theorem, including its transitive dependencies. That verification command
was removed from the delivered source. The proof does not reach `sorryAx`.

The argument covers arbitrary K with the given field map and arbitrary V, including
the zero ring V. It does not assume K is separably closed, or that a compatible beta
is injective, surjective, or epic. An element of the model's denominator monoid is
proved outside the pointed prime by mapping its unit to K; the zero-denominator
case is therefore impossible under the existing pointing hypotheses.

## No longer needed

No original imports were removed: the delivered base had only its two statement
imports and proof_deps was empty after retirement of the false Aux route. Each new
proof import supplies a declaration used by the proof.

This proof does not need the historical component-extension Aux chain:
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAux`,
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxFactorization`,
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel`,
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelStructure`,
or `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelPointing`.
Their respective nodes ending in `-aux`, `-aux-factorization`, `-aux-model`,
`-aux-model-structure` and `-aux-model-pointing` are unnecessary for this argument.
Some were already retired by the delivered base; no further retirement is claimed here.

The original prose route through scheme-level finite-data descent, affine-stage
descent and common-stage morphism descent (01ZM, 07RP and 01Z6) is also unnecessary
for this component proof. Ring-level model descent plus Mathlib's finite-presentation
factorization suffices. No other module is changed or withdrawn. No unit statement
or realized unit step is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

The current node correctly says that the former uniform cancellation/factorization
assertion is false, and had restored the original unresolved existence statement.
The proof never uses that assertion. It factors each beta after mapping to the local
ring of the model's pointed prime. It does not assert an arrow from one fixed model
to every global source, nor cancellation along an arbitrary map of etale algebras.

The existing unpointed model theorem states localization at an arbitrary submonoid M,
without identifying M with the image of R minus p. That statement is sufficient:
every denominator in M is a unit in t.B and hence has nonzero pointing in K. This
lets the proof pass to C at its pointed prime and avoids strengthening the model theorem.

## Second reading by J4

1. **Unchanged interface: PASS.** Compared the sole delivered Lean module with
   the repository using diff and checked the original theorem signature byte for
   byte. Its docstring, public imports, universe, hypotheses and conclusion are
   unchanged. There are no adapted modules, change records or public definitions
   added. The only new declarations are eight private helpers.
2. **Proof and construction: PASS.** Independently compiled the module with
   lcompile.py, without errors or warnings. Compiled a scratch copy with
   `#print axioms` for the main theorem and all eight helpers: each uses only
   `propext`, `Classical.choice` and `Quot.sound`, and none uses `sorryAx`.
   Scanned for sorry and forbidden constructs: none occur. The two private
   constructions use the explicit field-point equivalence and comma-category
   constructors. The model and factorization witnesses are obtained from proved
   theorems, not unproved existence assertions.
3. **Split statements and edge cases: PASS.** No statements are split off and
   no holes are added. Read every private helper and both imported Sheaf proof
   ingredients. The pointing kernel identity uses injectivity of field maps;
   it needs no separable-closedness assumption. Unit refinement applies exactly
   to elements outside that kernel. A zero denominator cannot belong to the
   model's monoid, since its image in K is a unit. For the empty finite stage
   the product is one and the principal localization argument still applies.
   The zero ring V is allowed, and arbitrary compatible beta need not be epic.
4. **Shortest route and pruning: PASS.** Repeated leanfinder, loogle and grep
   searches with a natural-family query, `IsLocalization.lift_comp`, and the
   finite-presentation factorization declaration; also searched local Lean for
   cocone extensions and field-point constructions. No shorter noncircular
   extension theorem was found. The proof already uses the proved unpointed
   model, Mathlib factorization, and source-library principal-localization
   colimit. Independently removed each of the four new proof imports in scratch
   copies: each removal produces an unknown identifier for its used ingredient.
   Thus all four are necessary and correctly ordinary imports. The repository
   node's old proof_deps is empty: there are no omitted old dependencies to list
   and no new module pruning is claimed. Read the full unit record
   `dag/units/sk-prop-input-spreading.json`; its statement and seven steps stay,
   and its realized fields are untouched. This component argument changes only
   a route below the unit level.
5. **DAG agreement: PASS.** Compared the existing node with the repository:
   only proof, proof_deps and proof_origin change. Checked its Lean statement
   against the exact theorem signature and checked that proof_deps is precisely
   the union of the steps' uses. The two Sheaf dependencies name the declarations
   actually applied; the third dependency's Mathlib match is exactly
   `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`. Read the colimit
   construction in the source library named in the proof prose. The seven DAG
   steps track the implemented construction, factorization and naturality proof.
   No new nodes require checking.

Second reading changed only this report by adding the independent review.
No Lean or DAG repairs were needed. The delivered result closes the sole original
hole, adds zero holes, and splits off zero statements. Scratch checks are outside
the delivered lean directory.
