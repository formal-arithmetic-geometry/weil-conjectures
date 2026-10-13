## What changed

Replaced the hole in `moduleCup_equal_derived_maps_class` by a proof that transports
both output classes through the same linear equivalence to derived-global-sections
homology. It obtains the proved naive/derived global diagram, evaluates each of the
two supplied realizations, rewrites with `hmaps`, `ha`, and `hb`, and uses injectivity
of the equivalence. The original signature, public imports, and definitions stay.

The initial decomposition added three modules, each with one named intermediate theorem
and its own DAG node:
`ModuleCupDerivedHomologyTensor`, `ModuleCupDerivedClassComparison`, and
`ModuleCupSinglePairingHomology`. Their interfaces specify respectively the natural
bilinear tensor operation on derived module homology, the canonical resolution-class
comparison, and the evaluation formula for one realization. The structures are
interfaces; no definition selects data from an unproved existence theorem. Witnesses
are unpacked only inside the theorem proof. `cupLocalizedCycleClass` is an explicit
composite of the existing homology projection and localization factorization iso.

Repair of return C1/C4: added `ModuleCupHomologyRepresentability` and
`ModuleCupShiftedUnitTensor`, each with a named theorem and a matching node.
The first gives the natural k-linear equivalence from Hom out of the single free
complex in degree n to H^n, including its formula on every chain map representing
a cycle. The second gives the normalized shifted-unit tensor isomorphism, its
value at the generator, and its compatibility with the lax localization map on
arbitrary pairs of representative chain maps. The homology-tensor node cites both
new facts in both proof steps and in proof_deps. Its new proof-only import of
`ModuleCupShiftedUnitTensor` also provides the representability interface.
The class-comparison node now cites the existing
`lem-weil-pbc-dplus-injective-representative` in proof[0].uses and proof_deps.
No existing Lean signature or definition was changed by this repair.

Updated the parent node's proof route. A local irreducibility annotation for the
large right-derived functor and reuse of the existing realization instances keep
checking below the fixed file time limit. The main theorem has a larger heartbeat
budget for comparing the transported formulas; the wall-clock limit stays 60 seconds.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_equal_derived_maps_class`
(node `lem-sc-module-cup-equal-derived-maps-class`). No hole remains in the item.

Added five holes, each exactly `:= by sorry` in a separate module:

- `AlgebraicGeometry.Scheme.Modules.exists_cupDerivedHomologyTensor`
  (`lem-sc-module-cup-derived-homology-tensor`).
- `AlgebraicGeometry.Scheme.Modules.exists_cupDerivedClassComparison`
  (`lem-sc-module-cup-derived-class-comparison`).
- `AlgebraicGeometry.Scheme.Modules.moduleCup_single_pairing_homology`
  (`lem-sc-module-cup-single-pairing-homology`).
- `AlgebraicGeometry.Scheme.Modules.exists_cupHomologyRepresentability`
  (`lem-sc-module-cup-homology-representability`).
- `AlgebraicGeometry.Scheme.Modules.exists_cupShiftedUnitTensor`
  (`lem-sc-module-cup-shifted-unit-tensor`).

This decomposes one upper hole into three primary parts, with two additional
supporting facts required by the returned review. It does not complete the full
import closure. The first primary statement mentions no scheme or resolution;
the second mentions no pairing; the third concerns one pairing and assumes
neither equality of derived maps nor equality of input classes. The actual
two-resolution equality is proved in the item. The two supporting statements
isolate representability and normalized shifted-unit tensor compatibility.

Edge cases checked in the mathematical interfaces: degree zero uses the zero
incoming differential in extension by zero; neither tensor input is assumed flat,
projective, or bounded; the free rank-one source of the Hom representation is
projective; zero cycles and zero sheaves give zero values by linearity. The
single-pairing formula imposes no H-zero normalization on the supplied derived map.

## No longer needed

No original import was removed, and no module is claimed to leave the target import
closure. The original public import of `ModuleCupResolutionRealization` stays for
its existing public interface. Its realization-existence and H-zero theorem is not
used by this proof: the two realizing maps and their `Realizes` proofs are supplied
as hypotheses. The parent proof no longer directly cites
`lem-sc-module-cup-resolution-realization`; its statement dependency is unchanged.
The resolution-data and module-cohomology definitions are still needed in the
comparison interfaces. The naive/derived compatibility theorem is used explicitly.

## Where the brief, the DAG or earlier work was wrong

The existing node's prose passes from a derived-category diagram to named natural-
degree resolution classes without a Lean interface for that passage. The new
statements isolate precisely that passage and the derived homology tensor operation.
The source library has `homologyRightDerivedFunctorObjSingleFunctorIso`, which
supplies the underlying cohomology isomorphism, but not its `D.class` representative
formula. `TensorHomologyPairing` supplies an ordinary total-complex pairing, but not
its natural derived-category version. `ModuleCupRealizationEvaluation` is downstream
of this item, so using it here would create a cycle. LeanSearch was unavailable;
LeanFinder, Loogle, local searches, and Mathlib source searches were performed.

The return correctly identified that a homology definition and a triangulated
shift-compatibility theorem do not supply either homology representability or the
normalized shifted-unit isomorphism. Both are now separate precise Lean statements,
not merely source tags. The representability node cites the existing bounded-
projective localization node; the shifted-unit node cites bounded-above-flat
K-flatness and the existing K-flat tensor model. Its component formula has no
extra sign, since it uses the ordinary single-complex tensor without interchanging
factors or shifts. The equivalence's on_cycles and the tensor theorem's Q(h)
equality together provide exactly the representative compatibility for proof[1].

The Stacks pages were read directly, including Tag 0FKU's global diagram and
Tag 068G's tensor product of homology classes. No statement was disputed or changed,
and no unit route was bypassed. The unit record `sk-prop-av-cube` has no realized
node bindings that this decomposition removes. No other group's module is adapted.

## New nodes

`lem-sc-module-cup-derived-homology-tensor` states the natural tensor of derived
module homology with its cochain normalization. It is in
`lean/Sheaf/Paper/ModuleCupDerivedHomologyTensor.lean`.

`lem-sc-module-cup-derived-class-comparison` states the canonical equivalence and
representative formula for every computing resolution. It is in
`lean/Sheaf/Paper/ModuleCupDerivedClassComparison.lean`.

`lem-sc-module-cup-single-pairing-homology` takes those two interfaces and the proved
global diagram and states the evaluation of a single realized pairing. It is in
`lean/Sheaf/Paper/ModuleCupSinglePairingHomology.lean`.

All five nodes inherit the parent's chapter, unit, and blueprint ancestry. Each
contains its exact Lean theorem signature, source, complete proof in words, and
search record. The change record is
`coord/changes/moduleCup_equal_derived_maps_class-elaboration.md`: it documents the
local elaboration commands conservatively classified as an interface change by
the tools. No existing statement, definition, visibility, or public import changed.

`lem-sc-module-cup-homology-representability` states the natural linear
Hom/homology equivalence for every integer degree, normalized by evaluation at 1
of the actual single-complex map. Module:
`lean/Sheaf/Paper/ModuleCupHomologyRepresentability.lean`. Its proof invokes
`lem-pc-ring-derived-map-representative` and computes cycles modulo boundaries.

`lem-sc-module-cup-shifted-unit-tensor` states the isomorphism for two integer
single free complexes, including its component at 1 and the equality after the
lax localization comparison for arbitrary chain maps f,g. Module:
`lean/Sheaf/Paper/ModuleCupShiftedUnitTensor.lean`. Its proof invokes
`lem-pc-module-bounded-flat-kflat` and `lem-pc-source-kflat-module-tensor-model`.
These are supporting facts for the tensor-homology part, not restatements of
that pairing's existence or of the two-resolution equality.

## Earlier second reading (a previous round; superseded)

The reading below concerns the returned version, before this repair. It does not
certify the two new modules. A renewed independent reading must check:

- C1/C4: both tensor-node proof steps and proof_deps cite
  `lem-sc-module-cup-homology-representability` and
  `lem-sc-module-cup-shifted-unit-tensor`; verify the first theorem's on_cycles
  formula and the second theorem's component formula and Q(h) equation together
  provide the representative compatibility used by proof[1].
- C1: class-comparison proof[0].uses and proof_deps both contain
  `lem-weil-pbc-dplus-injective-representative`, whose clause (2) is precisely
  bounded-below complexes of injectives being K-injective.
- Recheck all six modules, the five remaining named holes, new node records,
  unchanged original signatures, and the dry-run result for this revision.

Historical reading of the returned version follows.


1. **Signatures and accidental changes.** Compared the delivered parent module with
the repository version. The theorem signature and all existing declarations are
unchanged; the only parent changes are a proof-only import, local elaboration
options, and the proof body. The three added modules contain only the declarations
listed in the report and their matching nodes.

2. **Compilation and proof hygiene.** Compiled all four sandbox modules with
`lcompile.py --all`; compilation succeeds. The parent target has no `sorry`, and
the only remaining holes are the three explicitly named split-off theorems. No
axiom, unsafe, opaque, extern, implemented_by, or hollow definition was added.

3. **Truth and strength of statements.** Read each new interface against its
docstring and source. `CupDerivedHomologyTensor` is an interface for the natural
derived homology tensor with cycle normalization; `CupDerivedClassComparison`
records the canonical resolution-class comparison; and
`moduleCup_single_pairing_homology` handles one realization. Each is strictly a
component of the parent argument and introduces no extra conclusion or weakened
hypothesis. Edge cases (degree zero and zero cycles) are covered in the stated
interfaces.

4. **Proof route and pruning.** The parent proof follows the node route through
the naive/derived compatibility theorem, the three component interfaces, and
injectivity of the comparison equivalence. The unit `sk-prop-av-cube` route is
retained. No import was removable: public imports provide statement data, while
the new parent import is proof-only. The node `proof` and `proof_deps` entries
match the declarations actually used.

5. **DAG and records.** Checked JSON validity and that each new node records its
exact Lean declaration, source, proof steps, search record, chapter, unit, and
blueprint ancestry. The elaboration change record is present and reports no
semantic interface change.

I changed only this second-reading report section; no Lean proof or statement
required repair.

## Second reading by N4

1. **Signatures and accidental changes.** Compared all six delivered modules with the repository. The existing target theorem signature and definitions are unchanged; its only differences are the proof-only import, elaboration settings, and proof body. The five added modules contain the declarations listed in this report. New node `lean` records now match their module and theorem declarations.

2. **Compilation and proof hygiene.** Compiled all six modules with `lcompile.py --all`; compilation succeeds. The target theorem has no `sorry`; the five remaining `sorry`s are exactly the named split-off theorems and occur only as theorem proofs. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was added.

3. **Truth and strength of statements.** Read each split-off interface and its docstring against the source route. The homology tensor, class comparison, and single-pairing statements are strict components of the target argument. The representability and shifted-unit statements provide the explicitly required representative and generator compatibilities. Their hypotheses and conclusions preserve the needed degree, cycle, and naturality data, including degree zero and zero values.

4. **Proof route and pruning.** The target proof uses the existing naive/derived compatibility and the three component interfaces, then rewrites by the supplied map and input-class equalities and applies injectivity of the class comparison. Proof-only imports remain private; public imports are needed by exposed definitions and theorem signatures. The unit `sk-prop-av-cube` route is retained. No original proof dependency is claimed unused.

5. **DAG and records.** Checked all six node files as valid JSON. Existing target proof steps and dependencies agree with the proof, and each new node has its exact Lean declaration, source, proof steps, proof dependencies, chapter, unit, blueprint ancestry, and `lean` record. The elaboration change record is present and documents no semantic interface change.

I repaired the missing second-reading section and populated the five new node Lean records; no Lean proof or statement required repair.
