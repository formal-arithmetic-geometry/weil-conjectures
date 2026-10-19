## What changed

Completed eleven original proof obligations in `Sheaf.Paper.FrobeniusSquareExchange`.
The raw scalar localization now has proved identity/composition laws and proved
naturality for localized transformations. A proved private tensor-induction helper
identifies localization of a composite with the composite of localizations.
The rational pullback, source, and target identifications use the existing
normalization/uniqueness statements and those explicit tensor maps.

The intrinsic comparison cocycle uses the existing common-refinement formula.
Etale pullback preserves the original lower cohomological bound by the exact-derived
functor API. The selected operation is linear by cases on its support recipe, using
the existing direct-image and compact-support linearity declarations; the source
and target inherit linearity by composition.

The prescribed integral scalar/pullback comparison is now a natural isomorphism:
restrict the completion isomorphism to constructible objects and compose its whiskerings
with the existing ordinary scalar/pullback natural isomorphism. This yields exactly
the prescribed completed components. Extensionality proves uniqueness.

Every existing statement, definition, visibility, and public import is unchanged.
The node proof records these arguments and the existing construction dependencies.
No new module, statement repair, or change record is needed.

## Proved and sorry left

Closed 11 of the module's original 18 holes, all in namespace
`WeilConjectures.FrobeniusExchange`:

- `intrinsicCompactificationComparison_cocycle`
- `etalePull_lowerBound`
- `localizedHom_laws`
- `localizedTransformation_naturality`
- `localizedPullback_eq`
- `modelLinear`
- `modelSource_linear`
- `modelTarget_linear`
- `modelRationalSource_eq`
- `modelRationalTarget_eq`
- `pullScalar_existsUnique`

Seven original holes remain, each attached to node
`def-weil-operation-exchange-coefficient-descent` with its original source and
natural-language proof in its declaration docstring:

- `intrinsicCompactificationCoherence`: transport the recorded witnessed-domain
  coherence through the intrinsic realization, including normalization.
- `intrinsicCompactificationComparison_refinement`: identify the transported
  proper/open and compositor factors with the recorded refinement factors.
- `pullback_linear`: prove constant-coefficient linearity of the normalized
  K-flat/Roos integral pullback construction.
- `modelScalarMap_isIso`: prove invertibility of the actual finite-free
  whole-system operation coefficient mate.
- `modelRationalScalar_existsUnique`: localize the specified integral comparison
  with the recorded scalar functors and prove its component normalization.
- `stageBeta_coherence`: transfer the normalized whole-system coefficient-tower
  identities through localization and the recorded stage transition maps.
- `stageExchange_compatible`: establish mate-pasting compatibility of the
  operation exchange with those coefficient comparison maps.

Added holes: zero. Split-offs: zero. The private helper `localizedFunctor_comp`
is proved. Revalidation through `lcompile.py` against the current published library passes
in 31.7 seconds without errors or warnings.
This is a partial proof delivery from existing stated dependencies, not a decomposition.

## No longer needed

None. No original import, node, or module is pruned. The existing public imports
support the unchanged exposed construction and its remaining obligations. No generic
holed transport theorem was imported: the localized Hom and naturality laws are proved
by tensor induction in this module.

## Where the brief, the DAG or earlier work was wrong

The assigned node had empty `proof` and `proof_deps` fields despite eighteen named
proof obligations. Its declaration docstrings supplied the plans. The node copy now
records the completed arguments alongside the construction dependencies; the seven
remaining original statements are unchanged. No false statement was found and no
unit statement or route was bypassed.

The retained sandbox proof was compared with the current source module and
recompiled against the current published library on 2026-10-19. All eleven proof
replacements remain applicable; the current source still has the same eighteen
original holes. The required delivery dry run is being retried without modifying
any delivery or compile tool.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
