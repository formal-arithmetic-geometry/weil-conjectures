## Worker report

This is a stage-2 statement delivery, not a reopening of the Q61 stage-1 split.
The live item has no Lean record. coord/brief-stage2.md §0 explicitly authorizes
this handoff despite the inherited stage-1 BLOCKED ending. The accepted statement,
proof and proof dependencies are retained. This packet repairs the returned
immutable head 3535fd6afae8, H13, concerning the dependency interface.

`Sheaf.AlgebraicGeometry.CoherentSupportRankAction` states the assigned result as
`AlgebraicGeometry.Scheme.Modules.coherent_support_filtration_rank_action`, with
one postponed proof. It constructs no data by choosing from an existence sorry.
The existential family T is characterized on every coherent generator, so its
operators are the specified tensor actions, rather than arbitrary endomorphisms.

Hypothesis and clause correspondence:

- The field F is `(F : Type u) [Field F]`; the scheme is `(X : Scheme.{u})`.
  `[X.Over (Spec (.of F))]` gives its field structure. Finite type is precisely
  `[LocallyOfFiniteType (X ↘ Spec (.of F))]` together with
  `[QuasiCompact (X ↘ Spec (.of F))]`, following the recorded finite-type node.
- Noetherian, including quasi-compactness, is `[IsLocallyNoetherian X]` and
  `[CompactSpace X]`. There are no regularity, smoothness, reducedness, rational
  coefficient, coefficient-flatness or torsion-freeness hypotheses.
- The nonnegative integer d is `(d : ℕ)`. The dimension bound is
  `topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. This is the supremum of lengths of
  irreducible closed chains, with bottom for the empty space, agreeing on affine
  charts with `ringKrullDim` by `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`.
- `CoherentObject X` uses the upstream exact coherence predicate
  `RingedSpace.IsCoherent X.toRingedSpace`, with both finite-type and finite-type
  kernel conditions. `CoherentG0 X` is the explicit free abelian group quotient
  by `coherentG0Relations X`; each relation comes from an actual short exact
  sequence of the underlying module sheaves. Isomorphic objects have the same
  class: the isomorphism sequence with zero cokernel is among these relations,
  and the all-zero sequence kills the zero-object generator. No abstract group
  supplied by a new assumption is used.
- `coherentG0Filtration X k` for nonnegative k is the integer span of classes
  whose nonzero-stalk support has subspace Krull dimension at most k. For every
  negative k it is definitionally bottom, in particular F_{-1}=0. Defining all
  negative indices as bottom merely extends the requested indexing convention.
  On coherent objects over the Noetherian scheme this support is closed.
- The first conjunct `coherentG0Filtration X (d : ℤ) = ⊤` is F_d=G_0(X).
- The existential T takes every module E, finite natural rank n and its actual
  `E.IsFiniteLocallyFreeOfRank n` certificate, and returns an integer-linear
  endomorphism of `CoherentG0 X`. The first T clause quantifies over every
  coherent M, asserts that `E ⊗ M.val` is coherent, and gives the generator
  equality `T E n hE (coherentG0Class M) = coherentG0Class ⟨E ⊗ M.val, h⟩`.
  The tensor is the existing sheaf tensor; no second tensor is introduced.
- The next conjunct quantifies over every `k : ℕ` with `k ≤ d` and every x in
  `coherentG0Filtration X (k : ℤ)`. It places
  `(T E n hE - n • (LinearMap.id : Module.End ℤ (CoherentG0 X))) x` in the step
  `((k : ℤ) - 1)`. The subtraction is done after the integer cast, so k=0
  really targets -1, rather than truncated natural subtraction.
- Every coefficient ring is quantified as `(B : Type v) [CommRing B]`, with v
  independent of u. `CoherentG0Scalars X B` is `B ⊗[ℤ] CoherentG0 X`.
  `coherentG0ScalarSymmetry X B` is the actual tensor symmetry from the stated
  order `CoherentG0 X ⊗[ℤ] B`. All claims use this canonical identification.
  The coefficient-first order gives the native B-module structure and native
  `LinearMap.baseChange B`; it changes neither the coefficients nor their action.
- `coherentG0ScalarFiltration X B k` is the B-span of `b ⊗ x` for integral
  x in F_k. This equals the image of the scalar extension of the inclusion:
  pure tensors generate its domain. It does not claim injectivity of the
  scalar-extended inclusion. The coefficient lowering conjunct uses precisely
  `(T E n hE).baseChange B - n • LinearMap.id` on every such filtration step.
- Every finite linear combination is indexed by `Fin s`, for arbitrary natural
  s. Each summand has its own E, rank and finite-local-freeness certificate;
  `b : Fin s → B` supplies arbitrary coefficients. The final clause is exactly
  `(∑ j, b j • ((T ...).baseChange B - n j • LinearMap.id)) ^ (d + 1) = 0`,
  equality in the endomorphism ring of the actual coefficient module. Any finite
  family admits such an enumeration; no commutation premise is added.

The theorem docstring carries every one of the five accepted proof steps, with
its cited DAG ids. Its plain proof imports are the currently stated proof
dependencies; the cycle-exact-sequence dependency has no statement module and
cannot yet be imported. The length-additivity Mathlib match is imported even
though its node has no lean field. No proof is supplied at this stage.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` for def-weil-field.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`; its topological
  counterpart is `Mathlib.Topology.KrullDimension.topologicalKrullDim` from the
  already recorded def-kun-topological-krull-dimension.
- `WeilConjectures.AlgebraicGeometry.Coherent`:
  `AlgebraicGeometry.RingedSpace.IsCoherent`, and the public Mathlib
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded cochainModulesMonoidal interface is publicly imported. The scheme
  specialization is the upstream global `MonoidalCategory X.Modules` instance
  from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, defined by the
  same `SheafOfModules.monoidalCategory X.sheaf` localization tensor.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently the underlying Mathlib `SheafOfModules`; no new module category.
- `Mathlib.Algebra.Homology.ExactSequence`:
  `CategoryTheory.ShortComplex.ShortExact` for actual module-sheaf sequences.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Tower`: `TensorProduct`,
  `LinearMap.baseChange`, and `TensorProduct.comm` for scalar extension.
- Proof imports: upstream CoherentFiniteTypeLocallyNoetherian
  (`Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`),
  FiniteTypeModuleSupportClosed (`Scheme.Modules.finite_type_module_support_closed`),
  CoherentKernelCokernelSum (`RingedSpace.coherent_kernel_cokernel_sum`),
  Modules.FiniteLocallyFreeTensorExact (`Scheme.Modules.finiteLocallyFree_tensorLeft_exact`),
  and Mathlib.RingTheory.Length (`Module.length_eq_add_of_exact`).

Edge cases checked mathematically before writing: X empty (dimension bottom and
all modules zero up to isomorphism); zero coherent module (its support empty and
its class zero by the all-zero short exact sequence); d=0 and k=0 (the lowering
target really is -1); rank n=0 (the tensor is zero); s=0 (the sum is zero and
exponent d+1 positive); the zero coefficient ring; coefficient torsion and
nonflat coefficient extension (the filtration is an image, never an asserted
embedded tensor subgroup). No false-statement counterexample was found.

Searches actually run through msearch.py:

- leanfinder: "Tensor by a vector bundle minus its rank lowers the support
  filtration on the Grothendieck group of coherent sheaves" returned module
  tensor ranks, supports and general tensor maps, not this statement.
- loogle: `"Grothendieck", "Sheaf"` returned Grothendieck-topology sheaf
  declarations, not a coherent Grothendieck group.
- grep: `GrothendieckGroup|supportFiltration` returned only the ordinary monoid
  completion, not the exact-category coherent group.
- leansearch: "Grothendieck group of coherent sheaves with dimension of support
  filtration" returned ordinary monoid completions and ordinary module supportDim.
- For the new definition, leansearch: "The abelian group generated by coherent
  sheaves modulo short exact sequences with its support dimension filtration"
  returned sheaf abelian-category infrastructure only; leanfinder:
  "Grothendieck group of coherent sheaves and support dimension filtration"
  returned module supportDim and unrelated derived t-structure declarations.
- grep: `coherentG0|CoherentG0|supportFiltration|Grothendieck.*[Cc]oherent` returned
  only Grothendieck-topology uses. Direct rg with the same expression across
  WeilConjectures and Sheaf found no relevant declaration. Searching the item id
  in WeilConjectures also found none. DAG searches found the assigned item and
  its generic-cycle proof dependency, but no existing definition node.
- `tools/blueprint_refs.py search 'coherent Grothendieck'` found zero blueprint
  nodes. `ancestor` confirmed the inherited missing blueprint ancestor is null;
  the new node preserves its complete inherited via path with this item prefixed.

The current CompactObject example module has been withdrawn; its record and the
current module-mode conventions were read. Both modules use explicit universes,
`set_option autoImplicit false`, public statement imports, plain proof imports,
and source/blueprint docstrings. No statement correction is needed.

## New nodes

`def-sfb-coherent-grothendieck-support` owns
`Sheaf.AlgebraicGeometry.CoherentGrothendieckSupport`. It defines the actual
coherent-object subtype, exact-sequence relation subgroup, quotient group,
canonical generator class, integer support filtration, coefficient extension,
canonical tensor symmetry and coefficient image filtration. Every definition
has real data; the module has no theorem, no axiom, no sorry and no selection
from mere existence. Its source is the paragraph preceding Stacks 02S8/02S9 and
Homology 02MX. The three recorded searches ran as above and found no such
notion in Mathlib, the project, the upstream source, the DAG or the blueprint.
The already existing generic-cycle theorem defines related groups only in its
statement; it has no Lean interface, and supplies no existing group definition.
The added definition is cited by the item's stmt_deps without altering its split.

## Dependency modules

`pqf-def-coherent`: §1(B) superset-interface repair in
`Sheaf.AlgebraicGeometry.CoherentFiniteType`. Its landed Q25 declaration
`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` exposes only
quasi-coherence and finite type, without the finite-type-kernel coherence clause.
The previous delivery incorrectly replaced that binding and dropped the old
module from the node record. H13 requires preserving the landed interface.

The repaired packet keeps the Q25 module, file, primary declaration, verbatim
signature, and definition body. Its only code addition to that module is the
public import of `WeilConjectures.AlgebraicGeometry.Coherent`; its module docstring
now describes all three notions. The dependency record stays `existing: false`
and lists the old `IsQuasiCoherentFiniteType`, exact upstream
`AlgebraicGeometry.RingedSpace.IsCoherent`, Mathlib
`SheafOfModules.IsQuasicoherent`, and `SheafOfModules.IsFiniteType`.
The corrected lean.note explains both the missing coherence clause and the
preserved consumer interface. Every non-lean field of this dependency equals
the current main node. Both rank-action modules now publicly import this
recorded dependency module, so their imports check the combined interface.
There is no duplicate declaration or replacement coherence definition.

Original delivery validation: scompile.py compiled both modules separately, against the published
library and the private sibling overlay, without errors or warnings. The
prescribed deliver2.py dry run also compiled the existing-declaration probes.
The first preflight required the new node's standard `import_flags` field;
adding the empty list repaired that schema omission. The next dry run printed
`OK (dry run)` and confirmed both compilation and preflight. No tool was changed.


## Repair self-check

The saved packet was retained and first dry-run unchanged as required;
`deliver2.py --no-push` printed `OK (dry run)` at ebf3c9c8e8d. The H13 return
nonetheless requires the concrete dependency repair above. The current live
Q25 module was checked with `scompile.py --source
Sheaf.AlgebraicGeometry.CoherentFiniteType` and agrees with the read clone.
The repaired declaration body is byte-for-byte identical to that published
module. The item statement, all five proof steps, and the new coherent-G0
definitions are unchanged; their only edit is the dependency import.

No second agent was started: the dispatcher explicitly prohibits it, and the
maintainer performs the independent review. The repair is confined to the
returned interface defect and its imports/documentation.

Repair validation: `scompile.py Q24 lem-sfb-coherent-support-filtration-rank-action`
compiled all three delivered modules separately in dependency order, including
both their private-overlay library identities and sandbox checks, without errors
or unexpected warnings (each compile 1.5--1.9 seconds). In particular the retained
Q25 conjunction and the upstream coherence definition coexist with all imports
of the coherent-G0 and rank-action modules; no import/declaration clash occurred.
A static comparison against current main confirmed the old definition and all
following code are verbatim, all non-lean dependency fields are equal, the
module/file/primary declaration/signature/branch/existing fields are preserved,
and all four requested declarations are recorded. Every delivered node's
recorded primary signature is verbatim from its module.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
