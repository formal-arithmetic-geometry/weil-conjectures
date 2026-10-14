## What changed

Corrected `AlgebraicGeometry.Scheme.root_normalization_localization_comparison` by adding
`hbranch : IsPullback k (𝟙 _) i (j0 ≫ Spec.map ... ≫ ψ)`. This identifies the entire generic
pullback of U and excludes the extra branches identified by reviewer X-42d0f E3. The return
explicitly permits a formally sufficient branch-identification hypothesis instead of Mono i.
The attempted Mono repair is replaced: the caller does not assume i monic or an open immersion.

Forced proof adaptation in `RootNormalizationDvrComparison`: transport the supplied chart's
pullback along beta, paste with the open-immersion lift pullback, and pass the resulting hbranch.
Existing caller signatures, definitions and imports are unchanged. The comparison docstring and
both matching nodes now record this argument. No new declaration or module was introduced.

Change record: `coord/changes/root-normalization-localization-mono.md`.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0; split off: 0. The original hole remains in
`AlgebraicGeometry.Scheme.root_normalization_localization_comparison`
(node `lem-sbc-root-normalization-localization-comparison`). This delivery repairs its statement;
it does not claim a completed proof or net proof progress.

`AlgebraicGeometry.Scheme.root_normalization_dvr_comparison` remains proved conditionally on the
comparison theorem; its existing private algebraic helpers remain proved. The new local proof
steps hchart and hbranch are complete proofs with no holes.

## No longer needed

None. No proof-dependency import or node was removed. NormalizationStalkBaseChange remains a
plain proof-only import for the unchanged normalization route. All public imports provide types,
notations or instances used by the public statement. No unit route or realized field changed.

The unrestricted statement's extra-branch counterexample is excluded by hbranch; the branch
identification is supplied, not inferred from the compatibility equation hk alone.

## Where the brief, the DAG or earlier work was wrong

The first repair report claimed that the caller assumes IsOpenImmersion i. Its actual signature
has no such assumption: it supplies an isomorphism of the pullback with a principal open instead.
Adding global Mono i cannot be inferred from this chart. The explicit branch pullback is the
sufficient local hypothesis, and is proved from that chart. The comparison's old docstring and
node had hidden this necessary branch-identification step in their pullback-associativity claim.

## Forced adaptations

Only `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationDvrComparison` is adapted (unclaimed).
The original file compiles against the original dependency. Against the corrected dependency,
it fails at the existing call (original line 228): argument T has type GaloisCover but is expected
to have type IsPullback k (𝟙 _) i (j0 ≫ z ≫ Spec.map b ≫ φ). The independent scratch compilation
against the sandbox overlay reproduced this error.

The necessary changes add hchart via IsPullback.of_iso, hbranch via
IsOpenImmersion.isPullback_lift_id and IsPullback.paste_horiz, and the hbranch argument at the call.
No other proof, import, helper or signature changes. The two delivered modules compile together.

## Second reading by V3

1. Compared both delivered Lean modules with repository versions. The only existing signature
change is the explicitly recorded hbranch hypothesis in the comparison. The caller's signatures,
private algebraic helpers, definitions and visibility are byte-for-byte unchanged. No target
statement changes. The reviewer return authorizes this branch-identification alternative.
2. Compiled both modules in import order with lcompile.py, without errors or warnings. The only
sorry is the reported original comparison theorem. No axiom, unsafe, opaque, implemented_by,
extern, hollow definition or unproved arbitrary data choice was added. Explicit axiom checks
and the delivery probe check the declarations; sorryAx remains through the original open theorem.
3. No split-off statements or new nodes. Checked the repaired mathematical statement: hbranch
identifies the entire generic pullback, so pasting hT gives exactly the original cover after
coefficient localization. Tested n=1, trivial covers, and extra/disconnected branches: the first
two are ordinary localization, and the counterexample's additional branch violates hbranch.
The localization certificate and contraction equality preserve the root prime and structural germ.
4. Repeated searches with different queries through Loogle, LeanFinder and Mathlib grep, and
searched project Lean sources. Found the existing normalization-stalk base-change and stalk
isomorphism APIs; no complete comparison theorem that closes the remaining hole. The forced
caller proof uses the short Mathlib pullback transport and pasting route. No imports or nodes
are pruned; the unit sk-prop-input-spreading and all realized fields remain unchanged.
5. The comparison node's statement and verbatim Lean signature match hbranch. Its proof plan
now uses the pasted cartesian squares. The caller node records how hbranch is proved from the
chart. Existing proof_deps are unchanged and agree with both proofs/plans; no new node fields
are required.

Second reading changed the insufficient global-Mono repair to explicit hbranch, proved it in the
unchanged caller, corrected the docstring, DAG and change record, and replaced the inaccurate
caller/compilation claims in the report. The main comparison hole remains open.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationDvrComparison
Original against changed dependencies failed:
```
/tmp/forced-adaptation-c1p72_7d/lean/Sheaf/AlgebraicGeometry/Morphisms/RootNormalizationDvrComparison.lean:228:30: error: Application type mismatch: The argument
  T
has type
  GaloisCover G (Spec (CommRingCat.of (FractionRing ↑B)))
of sort `Type (u + 1)` but is expected to have type
  IsPullback k (𝟙 (Spec (CommRingCat.of (FractionRing ↑B)))) i
    (Spec.map (CommRingCat.ofHom (algebraMap (↑B) (FractionRing ↑B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↑H ↑B)) ≫ Spec.map b ≫ φ)
of sort `Prop` in the application
  root_normalization_localization_comparison i G W H B ((CommRingCat.Hom.hom b) f) hpi (Spec.map b ≫ φ) k hk T

(with the modules compiled into /tmp/forced-adaptation-c1p72_7d/.lbuild) [5.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
