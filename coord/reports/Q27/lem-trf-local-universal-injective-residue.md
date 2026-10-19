## Worker report

The module `lean/Sheaf/RingTheory/LocalUniversalInjectiveResidue.lean` states
`Module.universallyInjective_of_residueField_injective` for a commutative local ring
`R`, an `R`-linear map `u : M →ₗ[R] N`, projective source `M`, flat target `N`, and
injective residue-field tensor map. Its conclusion is injectivity of `u.lTensor L`
for every `R`-module `L`.

The local-ring hypothesis is `[IsLocalRing R]`; the source and target module
structures are `[AddCommGroup M] [Module R M]` and
`[AddCommGroup N] [Module R N]`; projectivity and flatness are exactly
`[Module.Projective R M]` and `[Module.Flat R N]`. The map is `(u : M →ₗ[R] N)`.
The induced map `M/𝔪M → N/𝔪N` is rendered by
`u.lTensor (IsLocalRing.ResidueField R)`, and its injectivity is `hres`.
Universal injectivity is rendered clause-by-clause as
`∀ (L : Type (max u v w z)) [AddCommGroup L] [Module R L],
Function.Injective (u.lTensor L)`.
The universe maximum permits arbitrary test-module universes while retaining the
ring and source/target universe constraints.

Dependencies used for the statement are Mathlib's `RingHom.Flat`/`Module.Flat`,
`Module.Projective`, and `TensorProduct`/`LinearMap.lTensor`; the corresponding
node records are `def-weil-pbc-flat-ring-map`, `def-weil-pbc-projective-module`,
and `def-weil-pbc-module-tensor-product`. The module also imports the stated
proof-plan declarations `Module.exists_directed_finite_free_presentation` from
`Sheaf.RingTheory.Flat.LazardPresentation` and
`Module.finiteFreeMap_residue_localization_strong` from
`Sheaf.RingTheory.FiniteFreeMapResidueLocalizationStrong`.

Edge cases checked: `M = 0`, `N = 0`, `u = 0`, and `u = LinearMap.id`; the zero
source case makes the residue hypothesis automatic and the conclusion is true,
while the identity case is immediate. No finite-generation hypothesis is added,
matching the arbitrary-rank source in Tag 05FQ. Mathlib's local-ring class includes nontriviality, matching the Stacks
convention that the maximal ideal is proper. Zero modules and empty bases are
allowed; a zero ring is consequently not a local ring in this convention.

Searches made: `msearch.py ... leanfinder "local ring projective source flat target
residue field injectivity universally injective tensor"` found only finite-source
`IsLocalRing.split_injective_iff_lTensor_residueField_injective` and unrelated
flatness results; no exact criterion. `msearch.py ... loogle "Module.Projective
Module.Flat lTensor Injective"` returned no match (application mismatch). `msearch.py
... grep "universally.injective|lTensor.*injective" RingTheory` found tensor-flat
lemmas but no local universal-injectivity criterion. `rg` over
`WeilConjectures` and `lean/Sheaf` found no duplicate declaration.

The canonical residue-field tensor/quotient identification sends
`ā ⊗ x` to `a • x + 𝔪M`, with inverse `x + 𝔪M ↦ 1 ⊗ x`.
These maps are mutually inverse by the tensor scalar relation and commute with
`u`, so `hres` is precisely the quotient-map hypothesis, not a different test.
The full seven-step node proof is reproduced in the declaration docstring.
The unstated proof dependency `lem-trf-projective-over-local-free` has no Lean
module recorded and hence no import yet; all recorded proof dependencies are
imported, including the Mathlib modules for the Mathlib leaves.

Read Stacks `flat.tex`, lemma-universally-injective-local, statement and proof
(lines 1946 onward): its three hypotheses and conclusion agree with this node.
The final source occurrence of `N_{i'}` instead of `N` is the typo already
identified and corrected in the node's proof plan.

No `STATEMENT-DISPUTED` flag or node fault.

Additional searches: `msearch.py loogle "Module.Projective, Module.Flat,
LinearMap.lTensor"` returned zero hits. `msearch.py leansearch "A linear map from
a projective module to a flat module over a local ring is universally injective
if its reduction modulo the maximal ideal is injective"` returned eight results,
including the finite-source finite-free-target splitting criterion and generic
flat/localization lemmas; none states this arbitrary-projective-source result.
Read the full signatures and docstrings of `Module.Projective`, `Module.Flat`,
`RingHom.Flat`, `TensorProduct`, `TensorProduct.lift`, and `LinearMap.lTensor`
in the prescribed source checkout. The upstream-name index and source grep
found no exact declaration.

Process note: an earlier staging command mistakenly used the shared checkout
as its working directory. Subsequent wrapper refresh restored its base node;
all final packet changes and repairs are in the sandbox only. No direct Git
command or global build was run.

## Second reading by Q27

Independent maintainer second reading of immutable delivery
9a95287a01da195109e0150dc04b16af2afc20a5, performed 2026-10-18. This
replaces the delivered placeholder; it does not assert that the worker performed
an independent review. The worker report above is preserved.

Read the packet, the complete check-brief2.md, the stage-2 contract and error
criteria, the immutable item node, all three immutable statement-dependency
records, and the delivered module, including both docstrings and its signature.
Source checked in /home/ubuntu/weil-newtargets-Q27/literature/stacks-project:
flat.tex:1946-1983, Tag 05FQ, lemma-universally-injective-local, statement
and complete proof; algebra.tex conventions, tensor-product construction
(00CX, lines 1716 onward), flatness (00HB, lines 8621 onward), and projectivity
(05CE/05CF, lines 18781 onward). These agree with the delivered statement.

Hypothesis and conclusion audit:

- The commutative local ring is `{R : Type u} [CommRing R] [IsLocalRing R]`.
  Stacks rings are commutative with 1. `IsLocalRing` extends `Nontrivial`,
  as required by the existence of a proper maximal ideal.
- The two arbitrary modules are `{M : Type v}` and `{N : Type w}`, each
  with `AddCommGroup` and `Module R`. Their universes are independent.
- Source projectivity is exactly `[Module.Projective R M]`. Read its actual
  canonical-free-surjection splitting definition (Projective.lean:71), the
  lifting property at line 91 and `Projective.iff_split` at line 236.
- Target flatness is exactly `[Module.Flat R N]`. Read Flat/Basic.lean:113,
  tensor-preserves-injections at lines 119-150 and its equivalence at lines
  308-319; RingHom/Flat.lean:27 defines the companion ring-map notion.
- The given map is `(u : M →ₗ[R] N)`. `LinearMap.lTensor` is
  `TensorProduct.map id u` (TensorProduct/Map.lean:326) and sends
  `l ⊗ m` to `l ⊗ u m`.
- `hres` is injectivity of `k ⊗ u`, where `k = IsLocalRing.ResidueField R`
  is literally `R ⧸ maximalIdeal R` (ResidueField/Defs.lean:30).
  The canonical natural isomorphism `k ⊗ V ≃ V/𝔪V` sends `ā ⊗ x` to
  `a x + 𝔪V`, with inverse `x + 𝔪V ↦ 1 ⊗ x`. Changing lifts or adding
  an element of `𝔪V` has zero effect by the tensor scalar relation.
  Naturality identifies this hypothesis with exactly the quotient-map
  hypothesis in the node and source.
- The conclusion quantifies over every test module in
  `Type (max u v w z)` and asserts `Function.Injective (u.lTensor L)`.
  The free universe `z` allows arbitrarily large tests; the maximum is the
  contract's common-universe convention, with smaller modules transported
  by ULift if necessary. It neither identifies `u`, `v`, `w` nor imposes a
  cardinal bound. There are no finiteness, Noetherian, characteristic,
  finite-presentation, or free-target assumptions.

The item's `lean.statement` equals the text from `theorem` up to `:= by`
verbatim (checked programmatically). All variables and universes are bound.
No statement correction or citer audit is needed.

Proof-plan audit: the docstring carries all seven node steps. Arbitrary-rank
Kaplansky freeness is precisely Tag 0593 (algebra.tex:20683); finite-support
reduction uses split finite basis spans and includes an empty span. Read the
record and source of `Module.exists_directed_finite_free_presentation`
(Sheaf.RingTheory.Flat.LazardPresentation): it provides a nonempty directed
partial order, finite coordinate-module equivalences, compatible cocone maps
and the canonical colimit isomorphism. Tensor right exactness plus flatness
supplies its exactness hypothesis. The filtered-colimit representative and
equality declarations in ConcreteCategory/Basic.lean:130,175, with the
ModuleCat forgetful preservation instance (FilteredColimits.lean:202), give
both the common-stage factorization and eventual zero detection. Read the
exact finite-free localization declaration in
Sheaf.RingTheory.FiniteFreeMapResidueLocalizationStrong: it gives an explicit
left inverse outside the prime, exactly what step 6 uses after choosing finite
bases. `baseChange_eq_ltensor` identifies its base-change map with the same
underlying tensor map. Localizing at a unit transports that retraction back
to R. The tensor-colimit assertion follows from the recorded closed ModuleCat
tensor-right adjunction and `isColimitOfPreserves`, whose declarations were
read. No compatible choices of retractions are needed. The final source typo
writing a stage target instead of N is already resolved by the node's explicit
zero-detection argument and has not changed the theorem.

The unstated Kaplansky theorem is a proof dependency only: this statement does
not require its object or a helper to type. The stage-2 contract imports proof
dependencies that are already stated; it does not require all future proof
lemmas to have Lean declarations. All recorded proof-dependency modules and
Mathlib-leaf modules used by this plan are imported. No missing statement
prerequisite, hollow construction, or dependency interface repair was found.

Edge cases: zero source, zero target, zero map, identity, empty finite basis
span, infinite basis, arbitrary flat target, all residue characteristics, and
independent module universes are retained. In particular a zero map with
nonzero projective source cannot satisfy hres (local projectives are free);
this is not a missing special case. The zero ring is correctly excluded by
the local-ring convention. Schemes and pro-etale sites do not occur.

Independent duplicate search: ran LeanFinder via msearch.py with query
"pure injection from projective module into flat module detected by reduction
over a local ring". Eight hits included `Module.Flat.of_projective`, finite
flat local freeness, and `IsLocalRing.split_injective_iff_lTensor_residueField_injective`.
Read the latter at LocalRing/Module.lean:334: it needs finite source and finite
free target, so it is not the delivered arbitrary-rank criterion. Grepped
Mathlib/RingTheory, upstream WeilConjectures, group lean/Sheaf and the upstream
name index for universally injective, pure monomorphism and residue-field
injection variants; no duplicate of this theorem was found. Existing tensor,
flat and projective notions are reused without a new definition.

Pilot gates: the sole delivered theorem has exactly `by sorry`; there are no
new definitions, hidden data holes, local proofs, local instances or private
copies. Module and declaration docstrings have the source and blueprint id,
and the declaration carries the complete proof plan. Lines are at most 100
characters. No dependency in stmt_deps or proof_deps is on the current route-
pivot dropped list; the item's repair-note path is absent. No dropped machinery
or pro-etale replacement appears.

Compiler evidence: the immutable report did not record a compiler transcript.
Reproduced using the prescribed command:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py Q27 lem-trf-local-universal-injective-residue snapshot/lean/Sheaf/RingTheory/LocalUniversalInjectiveResidue.lean

Exit code 0, no diagnostics. The current wrapper uses the server side overlay
and reports sandbox Sheaf/Stage2/Sandbox0.lean [5.5 s], then library
Sheaf/RingTheory/LocalUniversalInjectiveResidue.lean [56.3 s], each under the
unchanged 60-second per-file limit. This is server-confirmed per-file checking,
not a global build. No direct ssh or Git mutation was performed, and no live
Lean or project-clone file was edited.

Finding H11 (also the substantive section-content requirement of H1): the
original second-reading section was a placeholder saying no review occurred.
This complete replacement supplies the independent reading required by the
review prompt. The absent compiler evidence is also supplied above. No
mathematical or Lean change was necessary. Verdict: FIX, report only.
