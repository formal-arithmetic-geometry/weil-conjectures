## What changed

In `Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization`, completed
`schemeTensorShift_first_normalization_core` and
`schemeTensorShift_second_normalization` from a shared binary localization square.
The private, fully proved `first_generic` and `second_generic` establish the actual
categorical compositions using tensor-shift naturality, lax monoidal associativity,
whisker interchange, localization shift naturality, and tensorator naturality.
The second calculation uses closure of upstream K-flatness under tensor products.
All existing signatures, definitions, visibility, and public imports are retained.
Added one proof-only import, `Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare`.
Local instance caches retain the existing constructions and reduce repeated elaboration.
The second reader also cached `CochainComplex.HasMapBifunctor` in both modules
and reused the existing graded/cochain/derived instance caches in the binary module
after reproducing a compile timeout from repeated total-tensor instance inference.
See `coord/changes/K4-tensor-shift-normalization-local-instances.md`.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.schemeTensorShift_first_normalization_core`
  (`aux-sc-target-comparison-first-core`).
- `AlgebraicGeometry.schemeTensorShift_second_normalization`
  (`aux-sc-target-comparison-second`).

Also proved the new shared binary localization square:

- `AlgebraicGeometry.schemeTensorShift_binary_localization_square`
  (`lem-sc-scheme-tensor-shift-binary-localization-square`).

No sorry remains in either delivered module, and no hole is added elsewhere.
The binary square is proved by evaluating the generic localization comparison's
shift equation and transporting its tensorator and shift structure to Q.
Net original holes closed minus added: two. The already proved invertibility,
first wrapper, and combined normalization theorem are retained.

## No longer needed

No original imports or dependency modules were removed. The first calculation
needs only the K-flatness of P; the second needs that of P and T. The original
hT/hU hypotheses are retained exactly. No complex associator-shift coherence
is used to prove either normalization, and no additional tensor K-flatness lemma
module is imported: the existing upstream monoidal object property suffices.
No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing first-core proof plan says only to unfold abbreviations, but its
substantive missing ingredient is the binary localization shift square. The two
remaining nodes previously named only definitions as proof dependencies. Their
updated plans now name that binary square and explain the fully proved glue.
The original first-core docstring is retained unchanged. Stacks Tag 06YH is the
definition of derived tensor; the detailed localization comparison argument is
an agent expansion of the parent node's proof using the recorded library
localization construction, not a verbatim theorem at that tag.
LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder,
Loogle, and source searches found the generic localization and naturality ingredients,
but no exact canonical scheme binary square. Zero complexes and the empty scheme
require no exceptional case: all maps and cancellations are categorical isomorphisms.

## New nodes

`lem-sc-scheme-tensor-shift-binary-localization-square`, module
`Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare`, records the
binary first-variable square for Q and the canonical scheme tensor shift.
It is strictly smaller than either triple normalization, introduces no chosen
data, and does not depend on this item's module or either normalization result.
Its complete Lean proof evaluates `commShift_liftingIsoApp` for the flipped localization
bifunctor, cancels the K-flat inclusion shift comparison, and transports from
quotient followed by Qh to Q. The new statement has its own source, proof in words,
search records, and module. The change record is
`coord/changes/K4-tensor-shift-normalization-local-instances.md`.

## Second reading by K4

1. Compared the entire normalization module with the repository version by diff,
   then separately compared the seven existing public declaration signatures.
   All seven signatures are byte-for-byte identical. Both comparison definition
   bodies and the three previously proved wrappers are unchanged. The extra
   universes belong to private generic proofs. Local instance caches use the
   existing constructions; no chosen object or public instance registration is
   added. The local-cache change record describes these additions. Verdict: pass.
2. Read both modules in full, including all four new private generic proofs.
   Scanned the delivered sources for sorry, axiom, unsafe, opaque,
   implemented_by, extern and kernel-check bypasses: none occur. The squareL
   cancellation is of the image of the K-flat inclusion's shift isomorphism,
   hence legitimately epic, not of a general tensorator. squareQ transports
   along quotientCompQhIso using its actual identity components. The two upper
   calculations use naturality, whisker interchange and lax monoidal
   associativity, with no asserted associator-shift coherence. Compilation and
   axiom-check results are recorded below. All eight public declarations
   (the two comparison definitions, five original theorems and the new binary
   square) print exactly propext, Classical.choice and Quot.sound, without
   sorryAx. Verdict: pass.
3. There are no split-off sorry statements. The new binary theorem has only
   two factors and an upstream K-flat hypothesis on its first factor; it has a
   complete proof, docstring and matching node, and does not import the item.
   Its equation has the correct Q(P)[1] tensor Q(T) source and Q((P tensor T)[1])
   target on both sides. The argument works when either complex is zero or the
   scheme is empty: all cancellations remain cancellations of isomorphisms.
   No flatness of the second factor, boundedness, or extra scheme assumption is
   smuggled in. Independently searched LeanFinder for preservation of tensor
   translation by lax monoidal localization, Loogle for shift_app_comm, and
   grep for commShiftTensorRight, commShift_liftingIsoApp and tensorator
   naturality; also read the upstream Shift and ShiftUnitor constructions.
   The hits are ingredients, not this canonical independent-universe binary
   square. Read Stacks Definition 20.26.14 (Tag 06YH): it defines the derived
   tensor functor, not the displayed coherence square; the report and
   proof_origin correctly identify the latter as an agent expansion using the
   proved localization construction. Verdict: pass.
4. Checked the top-down reductions. first_generic uses the square for P,T
   tensor U and naturality at mu(T,U); second_generic uses the squares for P,T
   and P tensor T,U, with ObjectProperty.prop_tensor proving the needed
   K-flatness. No equivalent new hole replaces either original hole. The
   scheme-canonical-shift and KFlat imports supply public signature data; the
   cochain monoidal import supplies the cochain tensor structures used there.
   The new binary-square import in the item is correctly proof-only. No old
   proof_deps or imports have been removed, so No longer needed is complete.
   Read dag/units/sk-thm-picard-duality.json, including its statement, step and
   realized record: the delivered nodes are below that unit's route and no
   realization is changed or bypassed. Verdict: pass.
5. Compared both existing node JSONs with the repository: changes are confined
   to proof, proof_deps and proof_origin. Their plans accurately name the binary
   square and the actual generic calculations. The new node's Lean signature
   matches the new theorem verbatim; its proof-dependency union, source,
   agent proof_origin, searches, creation, chapter, unit and blueprint ancestry
   fields are present. All old dependency nodes remain used. Verdict: pass.

Changes by the second reader: added local caches of the existing
CochainComplex.HasMapBifunctor existence proofs in both modules and reused
the normalization module's existing graded/cochain/derived caches in the
binary module, including generic cochain and derived monoidal caches, to repair
reproduced 60-second compile timeouts; updated this report and the local-cache
change record. No theorem statement, definition body or proof route changed.

Final local verification: lcompile.py --all compiled the binary square in 49.6 s
and the normalization module in 48.6 s, with no errors or warnings. A scratch
axiom probe against these compiled modules completed in 2.0 s: all eight public
declarations use only propext, Classical.choice and Quot.sound. Both original
holes are closed; no new hole is added, including in the new binary module.

The first second-reader dry run passed compilation and axiom probes but required
four additional conservative local-instance users in the change record. Added
PerfectImmersionTensorAcrossUniverses, SmoothProperCurveDualizing,
SmoothProperDualizingTensorEvaluation and SmoothProperRelativeDualizing to
its Users table; no adaptation is required because only local caches of
existing constructions were added.
