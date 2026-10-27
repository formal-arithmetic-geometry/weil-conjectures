## What changed

`Sheaf.Paper.DerivedPullbackTensorHom` constructs the common-stage internal Hom
functor from the prescribed normalized arrows. The proof represents arbitrary
input arrows at a common finite coefficient stage, proves their outputs uniquely
determined, proves identity and composition using rational Hom functoriality and
cancellation of the endpoint comparisons, and proves functor uniqueness by
heterogeneous extensionality. The contravariant input composes in reversed order.

`CommonStageInternalHomData` extracts seven existing public declarations without
changing their commands: the recorded transition identification and the literal
Hom-pair, Hom object, permitted larger-stage pair and canonical comparison data.
The original module publicly re-exports them; the former statement imports and
private generic helpers used by `import all` consumers are retained.

`CommonStageInternalHomRepresentative` defines the prescribed input and output
representatives and their underlying normalized arrow. It proves representative
independence from a strictly smaller single-extension transport equation. Equality
in the two input quotient Hom sets gives eventual equality at a common larger
stage; transport and the equation give equal output classes.

`CommonStageInternalHomDescent` contains the proved representative, identity,
composition and unique-output-arrow calculus. It is a proof import of the item.
After profiling exposed expensive cached category-instance comparisons, the proof
reduces those small wrappers locally. The calculus is then separated from the
existing pullback/tensor proofs to keep each file within the compile budget; it
adds no hole and changes no shared definition or transparency attribute.

The existing private `pairDescent_with_components` and
`rawBilinearIso_existsUnique` signatures are retained as thin wrappers. Their
complete generic proofs are extracted into `PairDescentPrescribedComponents` and
`RawBilinearScalarComparison`, respectively. Profiling showed substantial type
checking and instance synthesis in the original monolithic file; these proved
interfaces isolate that work. The raw scalar comparison also keeps composition
abstract locally and uses its existing pure-tensor API. No private consumer name
is removed, and these two new modules introduce zero holes.

The two existing literal pullback definitions are extracted verbatim into
`CommonStagePullbackData`. The already proved comparison-data and descent lemmas
are isolated in `CommonStagePullbackDescent`; their original global names and signatures
remain available through a public re-export. The two existing DAG nodes follow these complete
proof implementations. This split leaves all definitions and pullback behavior
unchanged and reduces the measured artifact-compilation time.

The definition relocation and consumer inventory are recorded in
`coord/changes/E3-common-stage-internal-hom-data.md`. No existing module other
than the assigned item is edited. All eight delivery modules compiled together through `lcompile.py --all`, with
artifact generation and no compile errors. The main file took 28.2 seconds. The
unchanged direct importers `RationalRestrictionComparisonCoherence` and
`CommonStagePullbackNormalizedDescent` also compiled against these artifacts
(39.5 and 40.6 seconds). Their validation copies were removed from the packet.

Additional validation: `FiniteProductFieldCoefficientDescent` completed without
a type error but exceeded the limit against this delivery (104 seconds). Its
unchanged source also exceeded the limit against the published library in an
isolated baseline sandbox (90 seconds), so this is an existing consumer timing
problem. No adaptation or withdrawal of that source is included. The baseline
validation directory and all unchanged consumer copies were removed.

The initially selected `GeometricFrobeniusInternalHomComparison` consumer was
quarantined by the concurrent build at 13:10 UTC because it imports
`FiniteRealizationScalarMate`; its archive is untouched. The active pullback
consumer above was used instead.

## Proved and sorry left

Closed: `WeilConjectures.commonStageDerivedInternalHom_existsUnique`, the sole
remaining direct hole in the assigned live module. Its exact statement is kept.
The item has zero direct `sorry` occurrences after the reduction.

Added: one direct hole,
`WeilConjectures.CommonStageInternalHom.value_transport`, in
`Sheaf.Paper.CommonStageInternalHomRepresentative`, attached to
`lem-weil-common-stage-internal-hom-representative`. It asserts equality of
normalized arrows at one larger coefficient stage. It does not assert a
quotient map or a functor, and does not include identity, composition or functor
uniqueness. Its docstring gives the full natural-language tower calculation.

This is a decomposition: one old hole closed and one strictly smaller hole added;
net direct hole count change is zero. The new data module has zero holes. There
is no sorry in a definition. The arrow chosen inside the proof is specified by
a proved existence-and-uniqueness theorem, not by arbitrary mere existence.

## No longer needed

The direct import of `Mathlib.Logic.Small.Defs` is removed. The direct proof imports
of `StageSystemFunctorDescent` and `RationalPullbackStageCoherence` are replaced by
the extracted proof interfaces; both modules remain needed transitively. No
project node, module, declaration or unit step is withdrawn. The tensor proof
still needs `RationalTensorStageCoherence` and `BilinearCoefficientDescent` through
`import all`, including their private comparison data. The Hom proof uses the
actual StageSystem quotient calculus; no separate opposite-stage or unrestricted
bilinear descent module is added.

## Where the brief, the DAG or earlier work was wrong

The assignment's queue summary is older than the live source: the pullback and
tensor obligations are already proved, leaving only the internal-Hom existence
and uniqueness theorem. The original node's last proof step merely said this
was unfinished. It is replaced with the actual representative, identity,
composition and uniqueness argument and its one precise transport obligation.

The latest blueprint defines ambient condensed-coefficient operations and no
longer states the historical common-stage construction. The assigned library
still exposes that construction and its consumers. This delivery preserves its
statements and literal definitions, and records the existing formal proof plan as
the source of the new transport step; it does not attribute this legacy paragraph
to the newest blueprint or attempt a silent coefficient-framework replacement.

Mathlib searches: Lean Finder returned eight results about locally directed
functors, ind objects, coends and filtered categories; none states this restricted
contravariant descent. Loogle reported no identifier
`CategoryTheory.Functor.ofFullyFaithful`. The grep search returned 24 unrelated
Mathlib descent/resolution hits. Source inspection found the existing univariate
and covariant bilinear descent theorems, which serve the earlier proofs but do
not directly handle the permitted contravariant Hom domain. Blueprint search
found no duplicate for the new single-extension transport statement. A further
source search found `specifiedHomScalarRational` and
`specifiedHomScalarRationalCoherence`; their module
`SpecifiedHomScalarEvaluation` already imports the assigned item, so importing it
here would create a cycle. The new obligation records the missing common-stage
transport equation below that boundary, from the ordinary scalar comparison laws.

A final LeanSearch query returned eight general descent hits, including
`CategoryTheory.Quotient.lift`. That theorem assumes a functor on one category
and respects a supplied relation; it does not construct the directed-stage
permitted-pair representative formula or prove its normalized scalar comparison.
The project StageSystem API supplies the relevant quotient calculus here.

## New nodes

`def-weil-common-stage-internal-hom-data` records the existing literal definitions
now extracted into `CommonStageInternalHomData`, and the already proved
permitted-pair persistence theorem. Its node preserves the same common-stage
category and constructibility domain.

`lem-weil-common-stage-internal-hom-representative` records the single-extension
normalized Hom arrow equation and its proved representative-independence
consequence. Its proof uses the existing scalar-Hom naturality and coefficient
tower calculations, and then the actual quotient calculus. Repeated stages,
identity inclusions, zero arrows and empty schemes satisfy the same equation;
no faithfulness, new constructibility condition or coefficient flatness is assumed.

`lem-weil-common-stage-internal-hom-descent-calculus` records the fully proved
unique-output-arrow calculus, isolated for compilation after profiling and local
wrapper reductions. Its module has zero holes. The original item combines these
arrow statements into the functor and proves its uniqueness itself.

`lem-weil-pair-descent-prescribed-components` records the existing, completely
proved conversion of coherent coefficient-pair descent to prescribed comparison
components. The original private theorem remains a wrapper with the same type.
It uses the same StageSystem descent node already used by the original pullback
proof, with no new unit route.

`lem-weil-raw-bilinear-scalar-comparison` records the original, completely proved
tensor-induction comparison of raw bilinear scalar extensions. Its scalar map
is still an arbitrary function, exactly as in the original helper. The private
wrapper remains available to `import all` consumers with its identical signature.
`def-weil-common-stage-pullback-data` records the two existing literal pullback
definitions, moved without changing their commands. The two existing comparison
and descent nodes now attach to the extracted complete proof implementations;
their original theorem names remain publicly re-exported by the assigned item.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
