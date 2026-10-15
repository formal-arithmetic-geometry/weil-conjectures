## What changed

The original module now proves
`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite` without changing its signature
or any existing declaration signature. Its other declarations are unchanged. The second
reader made the factorization and lower-shriek-functoriality imports private, and publicly
imports `WeilConjectures.WeilSheaf.LowerShriek` for the statement definitions instead.
The proof uses the actual pro-etale implementation of Weil sheaves: finite pullbacks of affine w-contractible objects
are again w-contractible; exactness can then be checked by evaluation. Exactness passes through
the adic and Frobenius-equivariant forgetful functors. The exact derived-functor comparison
reduces positive homology to that of a degree-zero object.

Added `Sheaf.RingTheory.FiniteWContractible`, proving finite finitely presented stability of
w-contractibility from its component-space part. The w-locality and strictly henselian
maximal-localization parts are fully proved here, using the existing finite henselian product
and strictly henselian quotient theorems. There are no new definitions with unproved data.

Added `Sheaf.RingTheory.FiniteWContractibleComponents`, proving the passage to the closed-point
quotient and the component-space conclusion from a simpler spectrum theorem. Added
`Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected` for that remaining topological step.
Updated the attached finite-direct-image node's proof while preserving its original
etale argument for the other declarations attached to that node. Added three matching nodes.
No existing definition or statement was changed. The second reader made forced import-only
adaptations in `QuasiFiniteStalk`, `FiniteMap`, and `FibreCohomology`, as documented below.

The source is Stacks [Tag 0986](https://stacks.math.columbia.edu/tag/0986), with its last
component-space step supplied by [Tag 0985](https://stacks.math.columbia.edu/tag/0985).
The new spectrum node expands the finite case through the existing finite affine
section-cover theorem, so it does not assume that the broader quasi-finite thickening node
states the stronger finite-flat stratification that its proof discusses.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`.
Its Lean proof combines affine covering, finite pullback stability, exact evaluation,
reflection of exactness, and the derived comparison. None of these steps is left as a local
`sorry`. The module contains zero remaining `sorry` declarations.

Also proved `isWContractibleRing_of_finite_finitePresentation`, together with private helpers
for prime quotients, w-locality of integral algebras, finite local factorization, and strict
henselianity of maximal localizations. This result still depends on the component-space
statement below; it is not an unconditional sorry-free proof of finite w-contractibility.

Also proved `extremallyDisconnected_components_of_finite_finitePresentation`. Its actual Lean
proof constructs the closed-point ideal, transports Hausdorffness and extremal disconnectedness
to its quotient spectrum, proves separable closedness of its residue fields, transports
finite presentation through the quotient/tensor equivalence, and identifies the target
closed-point quotient with the component space.

Added exactly one hole:
`extremallyDisconnected_spectrum_of_finite_finitePresentation`
(node `lem-ce-finite-algebra-extremally-disconnected`). Its base spectrum is already
Hausdorff and extremally disconnected, and all its residue fields are separably closed.
It proves only extremal disconnectedness of the finite algebra's spectrum, not finite
pushforward exactness, vanishing, w-locality, or strict henselianity. What remains is the
finite section-cover construction, the clopen incidence/equality partition, and the
homeomorphism obtained from a continuous section. The complete proof in words is in its
docstring and node. The existing section-cover, zero-dimensional spectrum and projective-section
declarations are named there; this delivery does not duplicate them. The residue-field tensor calculation
is already proved by the private helper
`subsingleton_primeSpectrum_tensor_of_isSepClosed`, using Mathlib
`PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable`. The general
field-tensor node is therefore unnecessary for this argument. The private helpers
`tripletTensor_subsingleton` and `pullbackPoint_ext` also formalize the transfer from
field tensors to actual scheme pullback points and uniqueness from their two projections,
under the indicated residue-integrality hypothesis.

The intermediate component theorem and its predecessor ring theorem were both initially
split off during this session and then proved from this strictly smaller final step.

This is a decomposition: one upper hole closed and one strictly narrower hole added (net
zero among changed holes). It is not claimed as a proof with only the three permitted axioms.
A `#print axioms` check of the public proved declarations reports exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`, as expected from the named remaining hole.
All seven delivery modules compile together with `lcompile.py --all`; no compiler errors
or warnings were reported. Temporary axiom probes were removed after checking.

## No longer needed

No existing module was withdrawn. The quasi-finite factorization and lower-shriek
functoriality modules remain imported for proofs, with their accidental public visibility
removed by the second reader. `WeilConjectures.WeilSheaf.LowerShriek` is now the public
import supplying the statement definitions. The proved quasi-finite vanishing theorem
continues to use Zariski's main theorem, so no unit-level step was bypassed.

For the attached Weil-sheaf declaration, the etale geometric-stalk proof is unnecessary:
`lemma-weil-pbc-finite-stalk-formula`, `lemma-openclosed-point-ulift`, and
`lemma-weil-pbc-geometric-stalk-conservative` are not imported or used by the new proof.
They remain in the shared node's dependency list because its unchanged etale declarations
still use that route; these nodes are not claimed globally pruned.

Removed redundant proof imports tried during development from the item and
`Sheaf.RingTheory.FiniteWContractible`:
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Mathlib.Algebra.BigOperators.Pi`, and `Mathlib.RingTheory.Ideal.Quotient.Operations`.
`Mathlib.FieldTheory.PurelyInseparable.Basic` is used in the new spectrum module for its
proved tensor-spectrum helper, so it remains a proof import there.
The final compilation verifies the remaining imports suffice. The two new proof dependencies
are plain imports in the existing item module; its public lower-shriek import supplies the
existing statement definitions. The broad quasi-finite affine etale thickening decomposition
module is not imported: its signature does not give the stronger finite locally free base
change that the component argument needs. The candidate dependency `lem-weil-pbc-field-tensor-irreducible` /
`Sheaf.FieldTheory.FieldTensorUniqueMinimalPrime` is unnecessary: its required finite
specialization is proved directly from Mathlib in the remaining theorem's module. It is
not imported and is absent from the final new node's dependency list. This does not assert
that its other parents no longer need it. There are no globally pruned modules in this delivery.

## Where the brief, the DAG or earlier work was wrong

The shared finite-direct-image node describes ordinary etale abelian sheaves, while this
item's attached declaration concerns the actual adic pro-etale/Frobenius-equivariant category.
Applying the finite etale stalk formula would not by itself prove this declaration. This
is an interface gap, not a disputed mathematical statement. The new proof resolves it using
existing exactness criteria for the pro-etale site and finite w-contractible pullbacks.

The existing affine weakly contractible covering theorem does not retain a w-contractible
ring witness in its conclusion. Such a witness is needed for the finite pullback argument,
so the private cover helper repeats its already proved covering construction with that
extra information. It introduces no new obligation.

The remaining spectrum claim and the proved component claim have been checked on the
empty/zero case, identity maps, finite products,
nonreduced algebras, and non-flat finite quotients. Finite presentation is retained: it is
used to make the incidence/equality loci constructible and therefore clopen on the
zero-dimensional compact Hausdorff spaces. Separably closed residue fields ensure that
residue-field tensor products have a unique prime in the finite case. No Noetherian
hypothesis is added to any new ring statement.

The auxiliary results from the henselian-product/quotient, finite section-cover,
zero-dimensional spectrum, projective-section and closed-point/component nodes are used
as generic tools, rather than as a replacement for the unit's route.
The independent reader recorded these generic tool uses in the three new nodes. The
already-closed source covering/evaluation declarations are tools automatically; the report
records their use for the existing node, whose metadata edits remain confined to its
stage-3 editable fields.
LeanSearch was unavailable (HTTP 500); semantic LeanFinder, Loogle and source grep searches
were performed and are recorded. No unavailable search is treated as evidence of absence.

## New nodes

`lem-ce-finite-finitely-presented-wcontractible`:
`lean/Sheaf/RingTheory/FiniteWContractible.lean`, declaration
`isWContractibleRing_of_finite_finitePresentation`. It proves the ring-theoretic input to
finite pro-etale pushforward exactness from the separate component claim. Its w-local and
strict-local parts have genuine Lean proofs; it contains no `sorry` itself.

`lem-ce-finite-finitely-presented-wcontractible-components`:
`lean/Sheaf/RingTheory/FiniteWContractibleComponents.lean`, declaration
`extremallyDisconnected_components_of_finite_finitePresentation`. This theorem now has a
complete Lean proof from the finite Hausdorff spectrum theorem. The closed-point quotient,
residue-field comparison, and quotient/tensor base change are fully proved in this module.

`lem-ce-finite-algebra-extremally-disconnected`:
`lean/Sheaf/RingTheory/FiniteAlgebraExtremallyDisconnected.lean`, declaration
`extremallyDisconnected_spectrum_of_finite_finitePresentation`. This is the sole remaining
obligation, the finite case of Stacks 0985. Its node and docstring give the finite section-cover
argument and name its existing tools. It needs no w-locality or strict henselianity argument.

All three nodes retain the item's chapter `sec-curve-estimates`, unit `sk-prop-cd`, and blueprint
ancestor `lemma-weil-pbc-finite-direct-image-exact`. Whole-blueprint searches for 0986, 0985,
w-contractibility, extremal disconnectedness and finite presentation found no duplicate.
The import visibility change and its users are recorded in
`coord/changes/QuasiFiniteVanishing-imports.md`. Existing signatures and definitions are
unchanged; the record covers only import scope and the three forced proof imports.

## Second reading by E3

1. **Existing interfaces — pass.** Compared all delivered modules with the shared repository.
   The three Sheaf modules are new. The three adapted WeilConjectures modules
   each add exactly one plain import; their declarations and bodies are byte-identical. All five existing declaration signatures in
   `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` are byte for byte identical,
   including the finite vanishing theorem and `WeilComplex.upperStarToComplexIso`.
   No existing definition body, hypothesis, conclusion, or declaration visibility changed.
   The only existing theorem body changed is
   `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`; the added helpers are
   private. The three import-only adaptations are forced by the compiler errors recorded below.
   Import visibility was corrected explicitly
   as described in point 4; it is not an undeclared statement change.

2. **Proof and axioms — pass as a decomposition.** Compiled all seven delivered modules in
   import order through `lcompile.py --all`, and compiled scratch copies with `#print axioms`.
   The original module has no local hole. Its finite vanishing theorem and the two new
   proved ring theorems use only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The sole new hole is the public theorem
   `extremallyDisconnected_spectrum_of_finite_finitePresentation`, whose entire proof is
   `by sorry`, with its source, complete proof in words, and matching node. No forbidden
   declarations or mechanisms occur, and no definition contains a hole. The private
   quotient homeomorphism is constructed from a closed embedding and the explicit quotient
   map. Existential local-factor witnesses are used only within theorem proofs, not to
   define arbitrary data. Thus one original hole is closed and one smaller hole added;
   this is net zero among the changed holes, not an axiom-free proof of finite vanishing.

3. **New statements — pass.** Read Stacks Tags 0986, 0985, and 03HW, and the actual Lean
   interfaces of the finite henselian product, strictly henselian quotient, finite affine
   section cover, zero-dimensional spectrum, and continuous-section results. Tag 0986
   supplies the finite finitely presented w-contractibility claim. Its w-local and strict
   local parts are genuinely proved, with finiteness supplying integrality and finite
   residue extensions. The component theorem explicitly takes the w-strict-locality that
   its proof needs; its caller supplies it. The remaining spectrum theorem is exactly the
   finite specialization of 0985, with Hausdorffness, extremal disconnectedness, and
   separably closed residue fields all present. Its docstring expands 03HW through clopen
   incidence/equality partitions and a continuous section. Finite presentation makes the
   closed-immersion and equalizer images constructible, hence clopen; zero-dimensionality
   follows from integrality. The tensor step uses purely inseparable algebraic extensions,
   including imperfect separably closed fields, and does not assert equality of tensor
   rings. Tested the zero base/zero algebra, identity, finite products, the non-flat finite
   quotient `k × k → k`, and `k[ε]/(ε²)` over a separably closed field. All satisfy the
   stated conclusions. The open statement concerns only extremal disconnectedness of a
   finite spectrum; it does not restate exactness or higher-direct-image vanishing.
   Independent LeanFinder, Loogle, and Mathlib grep searches used the alternative wording
   “finite morphism over an extremally disconnected Stone space” and found no exact result.
   Also searched the shared Sheaf library and the upstream WeilConjectures source. The
   existing quasi-finite thickening theorem has only an affine surjective base change in
   its signature, insufficient for the compact Hausdorff section argument; its proof text
   does not justify assuming a stronger interface. No split can be closed in a few minutes
   from those available statements without introducing further obligations.

4. **Route and pruning — pass after import correction.** Read the exact-evaluation criterion
   and exact derived-functor comparison used by the main proof. The ring witness retained
   by the private covering helper is necessary; the existing weak-contractible covering
   theorem discards it. The proof checks finite pullbacks by that ring witness, reflects
   exactness through the adic forgetful functor, transfers it to Frobenius-equivariant
   sheaves, and compares the derived image with a degree-zero object. The other vanishing
   proofs remain unchanged, including the use of Zariski's main theorem for quasi-finite
   shriek vanishing. Corrected two proof-only public imports: quasi-finite factorization
   and lower-shriek functoriality are now plain imports; the lower-shriek definitions are
   imported publicly from `WeilConjectures.WeilSheaf.LowerShriek`. The revised module and
   its exposed definition compile. The original QuasiFiniteStalk, FiniteMap, and
   FibreCohomology each fail against the reduced public imports; adding the functoriality
   module as a plain proof import fixes them. All are unclaimed in the shared claim snapshot.
   A change record lists all 54 downstream modules, and a source-reference audit identifies
   these three as the only users of the removed named project results. The original
   FormalSteps and WeilConjectures umbrella compile with their existing independent imports. All original proof dependencies of the shared finite
   direct-image node remain needed by its unchanged etale declarations, so none is claimed
   pruned. The unit `sk-prop-cd` and its route are untouched; its `realized` arrays were
   already empty in the repository, which is a pre-existing bookkeeping gap, not evidence
   of any newly bypassed step. No module is globally pruned.

5. **DAG agreement — pass after tool-use bookkeeping.** Checked the three new Lean
   signatures occur verbatim in their node records, the source and creation fields,
   blueprint ancestry, chapter and unit, and the recorded searches. In each of the four
   delivered nodes, `proof_deps` is exactly the union of the proof steps' `uses`.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`, preserving
   its etale route and adding the actual pro-etale argument for the attached Weil theorem.
   The two proved new nodes record their genuine reductions; the spectrum node records
   the remaining section-cover argument and distinguishes its proved private tensor and
   pullback-point helpers from that unproved conclusion. Added `tool_uses` to the three
   new nodes for the generic henselian, quotient, component, spectrum, section-cover, and
   projective-section inputs; these do not replace a unit-level step.

Second-reading changes: corrected the two proof-only public imports, recorded accepted
cross-unit tool uses in the three new nodes, added three forced plain proof imports with their change record, and updated this report
to distinguish interface preservation from import visibility and decomposition from net progress.
No mathematical statement or proof argument required repair. Temporary probes are removed
before delivery; `deliver3.py --no-push` is the final validation before the push.


## Forced adaptations

The item now imports the factorization and lower-shriek-functoriality modules privately,
retaining a public import of the lower-shriek definitions. A change record is required for
this import-scope change: `coord/changes/QuasiFiniteVanishing-imports.md`. All adapted
modules were unclaimed in the shared repository when checked. They each add precisely
`import WeilConjectures.WeilSheaf.LowerShriekFunctoriality` and preserve every original
signature, declaration visibility, definition body, and proof body.

- `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk`: the original fails at lines
  232 and 264 with `Unknown constant
  AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso` (followed by the
  consequent failed `rcases`). Added the plain import after the existing imports. Its
  proofs of the quasi-finite stalk/base-change formulas use this isomorphism.
- `WeilConjectures.DeligneLaumon.Reduction.FiniteMap`: the original fails at line 62 with
  `Unknown constant AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`
  and at line 95 with `Unknown constant
  AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion`.
  Added the plain import after the existing imports. These are the composition and
  open-immersion isomorphisms already used by its unchanged cohomology proofs.
- `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology`: the original fails at line 304
  with `Unknown constant AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`.
  Added the plain import after the existing imports, supplying the base-change isomorphism
  used by its unchanged fibre-cohomology proof.

Originals were compiled individually from scratch copies with `lcompile.py` against the
changed sandbox modules. The revised files compile in the final delivery set. These are
forced import repairs, with no opportunistic edits. No adapter adds or closes a hole.
