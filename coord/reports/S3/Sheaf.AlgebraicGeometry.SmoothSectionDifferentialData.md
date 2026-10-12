## What changed

Replaced the hole in `AlgebraicGeometry.exists_smooth_section_differential_data`
with a complete compiling assembly, without changing its signature or public imports.
The proof constructs `S = SymmetricAlgebra A₁ K` and `D = S ⊗[A] B`, constructs
`τ` from the augmentation and the original section, and constructs `j` by the tensor
inclusion. It proves the section identity, surjectivity and smoothness directly, then
transfers freeness through the reduced differential isomorphism.

Added `Sheaf.AlgebraicGeometry.EtaleLiftProjectiveComplement`, whose public theorem
`AlgebraicGeometry.exists_etale_lift_projective_complement` has a complete local proof from the
existing `lift_finite_projective_module_etale` and Mathlib. The private finite-complement
and quotient-tensor helpers are also completely proved. In particular the complement
is the kernel of an explicit split finite-free surjection, and all scalar transports
are actual linear equivalences. No definition chooses data from an unproved existence.

Added `Sheaf.AlgebraicGeometry.SymmetricStabilizationDifferentials` for the sole
remaining calculation. Updated the original node's proof and dependencies and added
the two corresponding nodes. All three delivered modules compile together with no
warnings using `lcompile.py --all`.

The route is Stacks Tags [07M7](https://stacks.math.columbia.edu/tag/07M7), first
paragraph, and [07M5](https://stacks.math.columbia.edu/tag/07M5). The underlying
`sk-thm-p1` unit and its realized steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_smooth_section_differential_data`
(node `lem-weil-pbc-smooth-section-stabilization-free`). This is a decomposition,
not a complete sorry-free proof: one upper hole closed and one lower hole added,
so the net hole reduction is zero.

Also proved `AlgebraicGeometry.exists_etale_lift_projective_complement`
(node `lem-weil-pbc-etale-lift-projective-complement`), and the private helpers
`finite_projective_complement` and `quotient_tensor_equiv` in its module.

Every sorry left or added by this delivery:
`AlgebraicGeometry.symmetric_stabilization_differentials`
(node `lem-weil-pbc-symmetric-stabilization-differentials`), in its own new module,
with its entire proof `:= by sorry`. No sorry remains in the original module or
the projective-complement module. No other holes are added.

The remaining theorem asserts only a general linear isomorphism of reduced
differential modules; it constructs no étale ring, smooth algebra, section or
projective complement. It is strictly one calculation in step 4 of the original plan.
Its complete universal-property proof is in the docstring and node.

## No longer needed

No dependency module is pruned. The old direct proof dependency
`lem-weil-pbc-kahler-differentials-base-change` is no longer used by the
assembly and is removed from its `proof_deps`: the new differential lemma
uses the differential and tensor universal properties directly. The original
projective lift, symmetric smoothness, smooth base change/composition, symmetric
universal property, and differential universal property remain in the argument. The original direct proof import
of `Sheaf.AlgebraicGeometry.LiftProjectiveModuleEtale` is replaced by the proved
complement module, which imports it itself. Thus the lift module remains in the
import closure. No public imports are removed or made private. An unused exploratory
proof import of `Mathlib.LinearAlgebra.Projection` was removed from the new module.

The construction writes `Sym(K) ⊗[A] B` directly rather than materializing the nested
`(A₁ ⊗[A] B) ⊗[A₁] Sym(K)`. Tensor associativity and symmetry give the same stabilization;
no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's universal-property differential calculation
was a genuine unstated step: the listed base-change lemma alone does not give the
simultaneous splitting with the symmetric factor. It is now an explicit node.
The existing `cotangentComplex_symmetricAlgebra` gives the symmetric-factor
calculation for finitely generated modules, but does not give this tensor-product
splitting. No exact ready-made splitting was found in Mathlib or the source library.

Searches were actually run with LeanFinder, Loogle, grep and LeanSearch, and are
recorded in `searches.jsonl` and the new nodes. LeanSearch returned Internal Server
Error; this is recorded as unavailable, not as evidence of absence. Searches of
all blueprint records for 07M7, projective complements and symmetric differentials
found no duplicate blueprint statement. The blueprint ancestor is obtained by
following the existing node references to `thm-weil-pbc-finite-etale-lifting`;
the ancestor script returns None for the module-named created-item chain.

Edge cases checked: `J = ⊤` makes the quotient and all its modules zero and does
not invalidate the surjections or tensor cancellation; `P = 0` and a zero-rank
finite cover give the same explicit kernel construction. For the differential
statement, `K = 0` reduces to the base-change differential identity, `B = A`
reduces to the symmetric-algebra differential identity, and `Q = 0` makes both
sides zero. The statement permits arbitrary evaluation of the degree-one
symmetric generators, so it does not silently assume the augmentation. Its
compatibility equations supply the exact scalar actions used in each tensor product.

## New nodes

`lem-weil-pbc-etale-lift-projective-complement` records the fully proved finite
projective complement and its étale lift in `EtaleLiftProjectiveComplement.lean`.
Its proof explicitly splits a finite free module, applies the existing Tag 07M5
lemma, and cancels the quotient/base-change tensor products.

`lem-weil-pbc-symmetric-stabilization-differentials` records the single remaining
hole in `SymmetricStabilizationDifferentials.lean`. Its proof is the inverse
restriction of derivations on the two tensor factors, together with the symmetric
and differential universal properties. No interface changes, change records or
forced adaptations are needed.

## Second reading by S3

1. Compared the original module with the repository by `diff`. The entire
   `exists_smooth_section_differential_data` signature, declaration visibility,
   original docstring and all original public imports are byte-for-byte unchanged.
   The only original-file changes are its proof and two private proof imports.
   There are no existing definitions changed, targets changed or forced adaptations.
   Both other modules are genuinely new. Verdict: pass.
2. Compiled all three modules together with `lcompile.py --all`: clean, no warnings.
   Searched the delivered Lean for forbidden constructs and holes: the only hole
   is the whole public theorem `symmetric_stabilization_differentials := by sorry`.
   There are no definitions containing holes and no new data definitions at all.
   A scratch axiom probe of all three public theorems reports only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx`. The complement proof is complete
   locally, but its existing lifting dependencies still carry `sorryAx`; it is
   not an axiom-closed theorem. The chosen complement is the explicit kernel of
   a split finite-free surjection, and eta, S, D and tau are explicit terms.
   The differential hole is used only to transport freeness through an equivalence,
   not to choose arbitrary algebra or module data. Verdict: pass as a decomposition,
   one original hole closed, one new hole added, net zero.
3. Read both new signatures and their docstrings and nodes. Read Stacks
   [07M7](https://stacks.math.columbia.edu/tag/07M7), first proof paragraph,
   and [07M5](https://stacks.math.columbia.edu/tag/07M5).
   The complement uses exactly finite projectivity over A/J: the retraction
   x - g(f(x)) establishes finiteness/projectivity of ker f, the displayed
   equivalence gives freeness, and quotient/base-change cancellation transports
   the lifted module back via alpha inverse. No surjectivity or lifting
   hypothesis is silently added. For the remaining calculation, restrictions
   of derivations to S and B have exactly the compatible actions supplied by
   hSigma and hEta; the inverse is d(s tensor b) = sigma(b)dS(s) +
   tau(s tensor 1)dB(b). The symmetric universal property with the square-zero
   algebra proves the generator summand even at nonzero generator evaluation.
   Checked K=0, B=A, Q=0 and A1=A (ordinary polynomial stabilization), including
   evaluation of a rank-one generator at a nonzero element: the same differential
   splitting holds. For the complement, P=0, J=top and the zero-rank cover cause
   no failure. The new hole is strictly the linear differential calculation,
   not a restatement of the original existence theorem.
   Independently searched LeanFinder for the cotangent module of a symmetric
   tensor product, Loogle for `SymmetricAlgebra, KaehlerDifferential`, and grep
   for derivation/tensor and symmetric/differential names (logged by msearch).
   Read Mathlib Kaehler/TensorProduct and the library's
   `cotangentComplex_symmetricAlgebra`: the former supplies only base change,
   the latter includes a presentation-dependent symmetric-factor result and
   remains sorry; neither states the simultaneous splitting. Searches in
   lean/Sheaf and upstream WeilConjectures found no exact replacement.
   Closing this general calculation is more than a few-minute repair.
   Verdict: pass; keep the named, sourced calculation open.
4. Read the construction top-down: the proved complement helper feeds explicit
   S and D, augmentation computes both compatibility identities, smoothness
   comes from symmetric smoothness and base change/composition, and the final
   line transfers the free instance. The proof imports are private; public
   imports supply types and structures occurring in the signatures. No public
   import used only for a proof was introduced. The original direct lifting
   import is replaced by the complement import, but lifting remains in its
   closure. Corrected `No longer needed` to name the old direct differential
   base-change node removed from proof_deps. No module is pruned. Read
   dag/units/sk-thm-p1.json, including realized: nothing there is changed or
   bypassed; the algebraic stabilization remains below the same approximation
   route. Verdict: pass after the report correction.
5. Matched original-node proof steps with the actual Lean: finite-projective
   reduction and complement lift; explicit symmetric tensor algebra and
   augmentation; then the new differential equivalence and freeness transfer.
   Matched each new node's hypotheses/conclusion and proof to its declaration.
   In the complement node, the split retraction, lifting invocation and three
   scalar-cancellation equivalences match the code. In the calculation node,
   the three universal-property steps match the full docstring proof.
   proof_deps is the union of each node's uses, proof_origin records this route,
   and chapter, unit, source, creation and blueprint fields are present.
   Corrected both new lean.statement records to the literal multiline Lean
   signatures instead of whitespace-flattened versions. The original node's
   statement and all non-proof metadata remain unchanged. Verdict: pass.

Second-reading changes: corrected the pruning report and clarified inherited
sorryAx in the complement theorem; made the two new node signature records
verbatim; appended this reading. No mathematical statement or Lean proof changed.
