## What changed

Deleted the false public declaration
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_model_pointing`.
The module retains its proved private counterexample and now has no public statement.
Repair X-039e3 removes `counterexample_exists_pointing` and `counterexample_pointing_over`: both
duplicated private library lemmas. The counterexample now directly uses Mathlib’s
`SpecToEquivOfField` and its inverse law, with the point computed as the image of the
field’s closed point. The existing private lemmas cannot be called across modules;
no duplicate theorem or additional import replaces them. The sole caller, `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel`, was forcibly adapted: its two proof-only imports of `AuxModelStructure` and `AuxModelPointing` were replaced by `UniqueAuxCompatible`, and its proof now applies `etaleResidueTriples_primeLocalization_component_extension_compatible` directly. Its public imports, theorem signature, visibility, and docstring are unchanged.

Forced adaptation: before the deletion, the caller failed with unknown identifier
`etaleResidueTriples_primeLocalization_component_extension_model_pointing` at the old
proof application. The changed lines are the two imports and the proof body; these are
necessary and sufficient to compile against the deleted declaration.

## Proved and sorry left

Holes proved: none. The one original hole,
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_component_extension_model_pointing`,
is deleted as false, not proved. Holes added: none; split-off statements: none.
No declarations with `sorry` remain in the delivered modules. The compatible-model caller compiles
from the existing `etaleResidueTriples_primeLocalization_component_extension_compatible`
theorem, and the private counterexample declarations remain proved.

## No longer needed

The duplicate private helpers `counterexample_exists_pointing` and
`counterexample_pointing_over` are removed; their modules
`Sheaf.RingTheory.StrictHenselizationTriplesPresentation` and
`Sheaf.RingTheory.EtaleResidueTriplesFiltered` need no imports for this proof.
Mathlib’s field-point equivalence is already available from the public imports.

The deleted public declaration and its DAG `lean` record are no longer available. The
caller no longer needs modules
`Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelStructure`
or `Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelPointing`;
the old caller proof dependencies
`new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-structure`
and `new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model-pointing`
are both no longer needed. The DAG caller proof and dependencies now name only
`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible`.
The historical pointing node remains only as a retired DAG record with `lean: null`.

## Where the brief, the DAG or earlier work was wrong

Return X-039e3 correctly identified duplicate private field-point helpers. Both are
removed, and the retained counterexample uses Mathlib’s equivalence directly.
`deliver3.py --no-push` fetches sheaf-dag and rebuilds the delivery on that base;
no direct repository git mutation is needed.

The pointing statement is false. For `B = R × R` with diagonal structure map, the two
coordinate projections satisfy the structure equation but differ on `(1, 0)`. The
counterexample in the module certifies this under the original hypotheses. The earlier
DAG step incorrectly inferred equality of pointings from the structure equation.
The repair instead uses the already proved identity-triple construction, which supplies
both equations simultaneously. No target statement or caller signature changed.

## New nodes

None.

## Earlier second reading (a previous round; superseded)

The delivered pointing module and the adapted caller compile independently. The deleted
public declaration is absent, while the private counterexample remains proved. The caller
signature and visibility are unchanged, and its replacement proof uses only the existing
compatible-model theorem. The DAG pointing node has `lean: null`, no proof dependency, and
records retirement; the model node records the compatible theorem as its sole dependency.
The forced adaptation and deletion are documented in
`coord/changes/remove-false-component-model-pointing.md`.

## Historical second reading by R2 (before repair X-039e3)

1. Compared both delivered modules with the repository using `diff -u`. The
   caller's complete signature, visibility, docstring, and public imports are
   byte-for-byte unchanged. The sole interface change is the explicitly recorded
   deletion of the false pointing theorem, in
   `coord/changes/remove-false-component-model-pointing.md`. A repository-wide
   reference search finds only the adapted caller. No target or definition changes.
   Verdict: pass, as an interface repair, not a proof of the deleted statement.
2. Compiled both modules with `lcompile.py --all`, without errors or warnings.
   Compiled a scratch copy with `#print axioms` for all three private helpers:
   each uses only `propext`, `Classical.choice`, and `Quot.sound`. The caller's
   separate #print axioms check also shows only those three permitted axioms;
   the delivery probe checks all delivered declarations again. No sorry, axiom,
   unsafe, opaque, implemented_by, extern, or hollow definition is introduced.
   The field-point witnesses come from a proved equivalence, and the product
   ring and maps are actual constructions. Verdict: pass.
3. No statements are split off and no public helper is introduced. Read the
   complete counterexample: diagonal R-algebra Fin 2 → R is etale, evaluation
   at coordinate 0 defines the pointing, and evaluation at coordinate 1 defines
   the structure-compatible map. The vector (1, 0) contradicts pointing equality
   using Field K's nontriviality, for every supplied local triple. Searched the
   library for compatible-model and field-point results, and used msearch grep
   with SpecToEquivOfField; the existing compatible-model theorem is reused,
   and the factorization helpers use Mathlib's proved equivalence. Verdict: pass.
4. Read UniqueAuxCompatible: its identity triple over R supplies both equations
   directly, with no descent or arbitrary-witness assumption. The caller needs
   only that proof import; both removed imports and both old proof-dependency
   nodes are now explicitly listed above. Read sk-prop-input-spreading.json:
   neither repaired node realizes a unit statement or step (realized entries
   are empty); this changes only a subordinate erroneous argument, not the
   unit route. Verdict: pass.
5. Compared the two node files with the Lean. The caller names exactly its
   compatible-model dependency; the retired node has lean null, no proof
   dependencies, and an explicit counterexample/retirement explanation.
   Restored the pointing node's historical reviewed_proof field: workers own
   only lean, proof, proof_deps, and proof_origin here. No new nodes. Verdict: pass.

Second reading changed report accounting (deletion is not a proof), completed
pruning by naming both old dependency nodes, removed a stale missing-artifact
claim in the change record, and restored the node's historical review metadata.
The Lean proofs needed no repair.

Delivery dry run passed (CODEX interface repair). Its counterfactual check confirms
that the unchanged caller compiles against the shared baseline and fails against
the delivered pointing deletion; the adapted caller compiles. This establishes
necessity of the minimal import/proof edits, independently of the earlier scratch
experiment. The delivery probe found no forbidden axioms.

## Forced adaptations

### Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-o6p1qprc/lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel.lean:40:4: error(lean.unknownIdentifier): Unknown identifier `etaleResidueTriples_primeLocalization_component_extension_model_pointing`
/tmp/forced-adaptation-o6p1qprc/lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel.lean:35:66: error: unsolved goals
R : CommRingCat
p : ↥(Spec R)
K : Type u
inst✝¹ : Field K
χ : (Spec R).residueField p ⟶ CommRingCat.of K
q : ↥(Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶ CommRingCat.of K
inst✝ : Algebra (Localization.AtPrime p.asIdeal) K
hψ :
  (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
    CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K)
hK :
  CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
    (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ
c : EtaleResidueTriples R p K χ
i : c.B ⟶ t.B
hiα : c.α ≫ i = CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫ t.α
⊢ ∃ c i,
    c.α ≫ i = CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ

(with the modules compiled into /tmp/forced-adaptation-o6p1qprc/.lbuild) [2.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by R2

1. Compared both delivered modules with the repository. The caller's theorem signature,
   visibility, docstring, and public imports are unchanged; the deleted pointing declaration
   is recorded in the change record, and no target or definition changed. Verdict: pass.
2. Compiled the delivered modules with `lcompile.py --all`; both compile without warnings.
   The counterexample and caller use only permitted axioms, with no sorry, axiom, unsafe,
   opaque, implemented_by, extern, or hollow definition. Verdict: pass.
3. The disputed pointing assertion is false: the diagonal map into a product has two
   coordinate projections satisfying the structure equation but giving different pointings.
   No new public statement or split-off sorry is introduced. Verdict: pass.
4. The caller now uses the existing compatible-model theorem, which supplies both equations
   simultaneously. The unit route is preserved; the retired pointing node realizes no unit step.
   Verdict: pass.
5. The caller node's Lean proof and dependency list match the source, while the retired node
   has `lean: null` and records its counterexample and retirement. Verdict: pass.

The second reading changed only this report section; the proof and forced adaptation were
already verified by compilation and the counterfactual check.

## Forced adaptations

### Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel
Original against changed dependencies failed:
```
/tmp/forced-adaptation-jmqp55fq/lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel.lean:40:4: error(lean.unknownIdentifier): Unknown identifier `etaleResidueTriples_primeLocalization_component_extension_model_pointing`
/tmp/forced-adaptation-jmqp55fq/lean/Sheaf/RingTheory/EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModel.lean:35:66: error: unsolved goals
R : CommRingCat
p : ↥(Spec R)
K : Type u
inst✝¹ : Field K
χ : (Spec R).residueField p ⟶ CommRingCat.of K
q : ↥(Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶ CommRingCat.of K
inst✝ : Algebra (Localization.AtPrime p.asIdeal) K
hψ :
  (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
    CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K)
hK :
  CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
    (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ
c : EtaleResidueTriples R p K χ
i : c.B ⟶ t.B
hiα : c.α ≫ i = CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫ t.α
⊢ ∃ c i,
    c.α ≫ i = CommRingCat.ofHom (algebraMap (↑R) (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ = (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ

(with the modules compiled into /tmp/forced-adaptation-jmqp55fq/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
