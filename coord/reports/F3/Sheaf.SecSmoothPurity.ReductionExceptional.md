## What changed

In `Sheaf.SecSmoothPurity.ReductionExceptional`, proved three realization and Tate
scalar-interface lemmas. Every existing signature, definition body, visibility and import
is unchanged. No new public declaration or module is added.

`reductionConstantPush_eq` identifies the coefficient structure maps by the inverse laws
of the sheaf adjunction's Hom equivalence. Congruence identifies the sectionwise module
pushforwards and then their right derived functors.

`reductionRealizationScalarMap_isIso` uses a completely proved private categorical helper.
For adjunctions connected by two equivalences and an invertible restriction square,
precomposition by the inverse mate is a composite of Hom equivalences. Naturality identifies
this composite with the specified mate; the target realization counit extends the calculation
to every test object. The coyoneda criterion proves invertibility without a flatness
hypothesis on the coefficient ring map.

`reductionEtaleTateMap_existsUnique` constructs the sectionwise map using the scalar-extension
adjunction. The additive B-root generator is automatically ZMod N-linear for the restricted
coefficient action. Its transpose sends a tensor z to phi(a) tensor z. Root-generator
naturality makes the maps a presheaf morphism, which lifts through sheafification. The unit
identity gives the generator formula. Tensor induction and sheafification hom extensionality
prove uniqueness. The construction needs no positivity or invertibility hypothesis on N and
allows zero coefficient rings.

The node copy records these completed interface arguments in Steps 4 and 6, preserving all
thirteen steps of the unit's main geometric route and its existing dependencies.

## Proved and sorry left

Closed 3 of the original 5 holes, all on `det-sp-reduction-exceptional`:

- `AlgebraicGeometry.ProEtale.reductionConstantPush_eq`.
- `AlgebraicGeometry.ProEtale.reductionRealizationScalarMap_isIso`.
- `AlgebraicGeometry.ProEtale.reductionEtaleTateMap_existsUnique`.

Added 0 holes and split off 0 statements. The private helper
`reductionInverseMate_isIso` is completely proved.

The following original holes remain unchanged, on `det-sp-reduction-exceptional`, with
their existing source and complete natural-language proof docstrings:

- `AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap_isIso`.
- `AlgebraicGeometry.ProEtale.reductionExceptional_isIso`.

The first still needs derived computation on the flat Tate line and identification of the
adjunct with the proved generator-normalized map. The main theorem still needs the recorded
chart, trace, summation, transport and locality argument. Neither is claimed as decomposed.

## No longer needed

None. No existing import, module or node is pruned: the unfinished main theorem retains its
recorded geometric route. The scalar-realization mate interface needs no additional K-flat
representative theorem or new import.

## Where the brief, the DAG or earlier work was wrong

No statement error established. The scalar-mate support lemma has a shorter categorical proof
because both realization functors are equivalences. This simplifies only the interface
calculation in Step 4; the unit's chart, trace, summation and locality route is preserved.

Validation: the original edited module compiled through `lcompile.py` in 17.2 seconds with
no errors or warnings. After the packaging repair, the explicit-tensor version compiled
in 18.9 seconds; its five line-width warnings were fixed by wrapping those lines. The Tate-map proof was first checked independently in a scratch module.
A separate axiom probe also compiled: all three proofs retain transitive `sorryAx` through
the existing admitted library interfaces; none of the three contains a direct admission.

The resumed dry run found one packaging diagnostic: additional top-level universe and
notation-scope commands required an interface change record. The repair removes both
commands: the private helper uses anonymous universes, and base-change tensors are
written explicitly inside the Tate-map proof term, without opening a notation scope. The scalar-mate proof docstring now describes
the actual categorical proof. Existing public signatures and importer-visible commands
are unchanged. Final compilation and delivery checks are recorded by the delivery tool.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
