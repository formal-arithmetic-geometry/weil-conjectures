## What changed

Proved `CategoryTheory.unit_power_localDerivedComplete` with its original signature.
The localization universal property constructs inverse maps for a unit times a positive
power. Their sheafifications preserve the localization unit. The resulting actual
augmented chain isomorphism induces the natural completion comparison and preserves
the specified augmentation-induced units.

For the reflection assertions, the proof uses the existing general extended Cech
model and reflector properties. It constructs singleton generating sections of the
image ideal, proves finite type, and proves that the actual principal two-term complex
has the required local description. Its slice comparison includes the canonical ring
comparison and the augmentation square, on complexes and after derived restriction.
The singleton tensor unit is removed by the right unitor. The private restriction
calculation follows the existing localization-factor comparison, keeping its ring
component explicit: an arbitrary arrow isomorphism does not specify the canonical
ring comparison required by the local description. Finally the Hom bijection
characterizes complete objects by invertibility of their units, giving the equivalence
of completeness for a and b.

All additional helpers are private and proved. No public definition, statement,
attribute or public import changed. The change record
`coord/changes/unit-power-private-proof-context.md` documents the added elaboration
options, scoped zero-object notation and private-helper section variables that preflight
classifies as context changes. The sole downstream importer was checked; its statements
need no adaptation. The node proof, dependencies and proof origin
record this route. The three obsolete top-level tool approvals are removed, without
adding or reordering approvals.

Edge cases: the construction uses invertibility, not cancellation or a domain
hypothesis. It applies to the zero ring, nilpotent or invertible b, and an empty site.
The positive exponent is used to deduce that b is invertible after a is inverted.
The ideal remains the categorical image, including sections divisible only locally.

Validation: the complete module passed remote `lcompile.py` with exit code 0,
no warnings, in 50.2 seconds. A delivery compile later exceeded 60 seconds; profiling
identified repeated sheaf-composition instance searches and unnecessary equality
coercions. Explicit equality types and a proved private local-instance cache reduced
the profiled compile to 46.9 seconds. The temporary profiler option was removed. The original theorem signature is unchanged, checked
after whitespace normalization. Both new proof imports pass `import_direction.py`;
the revised DAG dependency closure does not contain this item. Every Lean line has
at most 100 characters. The final delivery checks compile the optimized file again.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.unit_power_localDerivedComplete`.

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the item: 0.
There are no new public statements or nodes and no admitted private helpers. The proof
uses the existing declarations of the general extended Cech model and its reflector
properties; their existing proof dependencies remain separate project work.

## No longer needed

Removed the following private imports and the corresponding original proof dependencies:

- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`, node
  `lem-weil-pbc-ringed-derived-complete-elements-ideal`: the Hom-bijection
  characterization of complete objects replaces the generator-vanishing argument.
- `Sheaf.CategoryTheory.RingedCechKoszulDualLimit`, node
  `lem-weil-pbc-ringed-cech-koszul-dual-limit`: the principal two-term complex is
  treated directly as an augmented Cech model, without a Koszul tower comparison.
- `Sheaf.Paper.WeilCompletedTensorReflector`, with the original dependency
  `lem-weil-pbc-ringed-koszul-completion-reflector`: the general Cech reflector
  properties give the needed reflection clauses directly.

All three modules are absent from the new import closure of this item. These are
removals of dependencies of this proof. No module is withdrawn, no source-library
declaration is removed, and no claim is made that other targets cease to use them.
The original statement dependencies and all public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically valid, but the imported
`WeilCompletedTensorReflector` interface is specialized to schemes and adic
coefficient data. The available generic `ringedKoszulCompletionReflector` also asks
for a derived-category instance for the strict tower category, which the present
statement does not assume. The shorter general Cech route avoids both interface
mismatches and proves the unchanged statement. No false statement was encountered.

The first delivery preflight requested the context change record; it was added with
the original and new signatures verbatim and the downstream user audit. The Lean proof
was not changed in response to that metadata request. Subsequent private elaboration
optimizations address the delivery compile limit without changing a public signature.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
