## What changed

Proved `AlgebraicGeometry.qcoh_ordinary_tensor_resolution_comparison_independence`
in `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionNaturality`, preserving its
signature and visibility. Cancel the coefficient equations using `sN` and the
augmentation equations using `sM`, construct a homotopy between the augmented lifts,
tensor its components with the common semilinear coefficient map, and apply
`Homotopy.homologyMap_eq` to transfer the witnessed naturality equation.

Repair of the return: removed the duplicate private theorem
`AlgebraicGeometry.prevD_chain`. The pure-tensor calculation now uses the existing
Mathlib theorem `Homotopy.prevD_chainComplex` directly. Loogle returned that theorem,
and its source and explicit type were checked against the removed helper.
It is already available through the existing public imports, so no additional import
or modification of `Sheaf.Algebra.Homology.QuotientTensorResolutionLiftHomotopy`
is needed. That module's similarly named helper is private.

The three remaining private theorem helpers and the private tensor-map construction
are fully proved. The lifting induction follows Stacks Tag 00LS(2),
`algebra.tex`, `lemma-compare-resolutions`, with projectivity in place of freeness.
Restriction of scalars preserves exactness; its target terms need not be projective.
The coefficient tensor map is constructed by `TensorProduct.map`, with no arbitrary
choice from an unproved existence theorem.

Removed the original proof-only import `Mathlib.AlgebraicGeometry.Modules.Tilde`.
All public imports remain unchanged. The scoped heartbeat allowance accommodates
the existing dependent tensor-comparison types; the scoped unused-variable linter
exception retains the fixed `hK` and `hq` binders. The repaired single-file compile
completed cleanly in 10.0 seconds, within the unchanged 60-second limit.

Retained the delivered DAG attachment for this already existing theorem, and updated
its proof and search record to name the Mathlib lemma now used. There are no adapted
modules or change records. The prior second reading described the superseded version;
its section is left for the new independent reader to replace.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.qcoh_ordinary_tensor_resolution_comparison_independence`
(node `new-j1-qcoh-ordinary-tensor-resolution-comparison-independence`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivered
Lean module. Its proof uses Mathlib and the fully proved local helpers, with no holed
Sheaf theorem used. An explicit `#print axioms` check of the repaired public theorem
and all four remaining private helpers completed cleanly: every declaration uses
only `propext`, `Classical.choice` and `Quot.sound`. The delivery probe checks them again.

Degree zero uses augmented exactness; positive degrees use resolution exactness.
Zero modules, zero rings, empty affine opens, identity inclusions and nonflat ring
restrictions do not require extra assumptions. The argument works for every supplied
coordinate family `c` and does not require boundedness of `K`.

## No longer needed

Removed import: `Mathlib.AlgebraicGeometry.Modules.Tilde`.
Removed duplicate helper: `AlgebraicGeometry.prevD_chain`.
The redundant `Mathlib.Algebra.Category.ModuleCat.Abelian` import from the first
attempt remains absent.

For this conditional independence theorem, the proposed common K-flat refinement,
chart tilde comparison, exact tilde homology comparison and section-unit naturality
are unnecessary. The proof does not need the planned nodes
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-pc-open-kflat-tensor-homology-comparison`,
`lem-pc-affine-chart-total-tensor`,
`new-affine-derived-tilde-homology-comparison`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-pc-affine-tilde-kflat`, `lem-pc-kflat-open-restriction`, or
`lem-pc-module-bounded-flat-kflat`. These may still be used by coordinate existence;
no global unreachability is asserted.

No Sheaf proof-dependency import was present to remove. The public quotient tensor
lift homotopy theorem is specialized to quotient-ring coefficients and is not used.
No unit statement or step is bypassed: `sk-thm-picard-duality` has empty `realized`
statement and step lists; the repaired argument remains below its unit level.

## Where the brief, the DAG or earlier work was wrong

The returned version reproved the chain-complex differential identity as a private
helper, duplicating `ModuleCat.prevD_chain` in the quotient tensor homotopy module.
Mathlib already states the identity as `Homotopy.prevD_chainComplex`. The repair
removes that helper and calls Mathlib directly, without renaming or restating it.

The original docstring describes a common-resolution zigzag plan, but independence
of a supplied comparison follows algebraically once naturality for one comparison
is a hypothesis. K-flatness and quasi-coherence do not enter this proof; all existing
binders are retained. Mathlib's projective-resolution comparison API requires a
projective target resolution, whereas restriction of scalars only gives the exact
target complex needed here. The local induction uses that weaker property.

The original item had no matching node attachment, and neither blueprint ID in its
file had a node file. The delivered node records the existing conditional independence
theorem using the parent coordinate-existence node's chapter, unit and blueprint
ancestor. The parent's earlier unsplit DAG route is unchanged.

Earlier LeanFinder and Loogle searches found the projective-resolution homotopy API;
Mathlib grep confirmed the relevant types. LeanSearch was unavailable. The repair's
Loogle search found the exact Mathlib differential identity now used in the proof.

## New nodes

`new-j1-qcoh-ordinary-tensor-resolution-comparison-independence` attaches the already
existing public theorem to its complete proof. Its source is Stacks Tag 00LS(2),
with explicit projective lifting and semilinear tensor calculations. It adds no Lean
statement, module or hole. Its search records include the exact Mathlib lemma used
by this repair, and its proof records the removal of the duplicate helper. The
parent's chapter, unit and blueprint ancestry are preserved.

## Second reading by F4

1. **Visible declarations: PASS.** Read the repository and sandbox modules whole and
   compared them with `diff -u`. The existing theorem's signature is byte for byte
   identical, including both quasi-coherence instances, `MA`, `NA`, `sM`, `sN`, `P`,
   `K`, `q`, `hK`, `hq`, `n`, the arbitrary coordinate family `c`, the basic-open
   hypothesis, and all three compatibility equations. The existential naturality
   premise and universally quantified conclusion are unchanged. Existing declaration
   visibility, definitions and docstrings are unchanged. The only removed import is
   the proof-only tilde import; the additions are private proved helpers and scoped
   elaboration/linter options. No other module or change record is delivered.

2. **Proof and axioms: PASS.** Independently compiled the delivered file through
   `lcompile.py`: exit 0, no warning, 10.1 seconds. Confirmed that the axiom-check
   scratch copy contains exactly the delivered module followed by five checks, and
   compiled it independently. The public theorem, `augmented_lift_homotopy`,
   `semilinearTensorLift`, `semilinearTensorLift_tmul`, and
   `tensor_resolution_lift_homotopy` each use only `propext`, `Classical.choice`,
   and `Quot.sound`. No `sorry`, axiom, unsafe/opaque/external declaration or kernel
   bypass occurs. The tensor-map definition constructs `TensorProduct.map` from
   supplied maps; it chooses no witness from any unproved existence statement.
   Read the induction's zero-degree and successor equations: projectivity is used
   only for source terms and exactness only for the restricted target. Checked the
   tensor homotopy componentwise, including its support condition and the
   `j = 0` truncated predecessor, against `Homotopy.prevD_chainComplex`.

3. **Split statements and small cases: PASS.** No statement is split off and no
   hole is added. The private augmented comparison lemma needs no projectivity of
   the target and no surjectivity of its augmentation: exactness at its degree-zero
   term suffices for the difference of the two lifts. In degree zero the source's
   outgoing differential is zero; positive degrees use the successor exactness
   assumptions. Zero modules and zero rings cause no exception. For an identity
   inclusion the same cancellation and homotopy argument applies. A nonflat ring
   restriction causes no problem because restriction of scalars is exact and the
   tensor operation is applied to a homotopy, not to a quasi-isomorphism. Verified
   the cited induction against [Stacks Tag 00LS(2)](https://stacks.math.columbia.edu/tag/00LS),
   replacing free lifting by precisely the projective lifting property.

4. **Route, search and pruning: PASS.** Followed the proof downward from the public
   conclusion: cancel `sN` to identify coefficient maps, cancel `sM` to identify
   augmentations, lift the difference, tensor the homotopy with the common
   coefficient map, then rewrite by `Homotopy.homologyMap_eq`. Independently searched
   with Loogle (`"Homotopy", "Exact"`), LeanFinder (degreewise projective maps into
   acyclic complexes), Mathlib grep (`nonempty_homotopy|liftHomotopy|mkInductive`),
   and repository `rg`. Results supply no shorter applicable augmented semilinear
   comparison. Mathlib `ProjectiveResolution.liftHomotopy` requires a projective
   target resolution, and the K-projective API would require conversion to integer
   cochain complexes and an augmented acyclic target. The quotient coefficient
   theorem is a special case, and its generic induction helper is private, hence
   unavailable for reuse here. The differential identity already uses Mathlib
   directly. All retained public imports provide objects or constructions appearing
   in the unchanged signature; no newly introduced proof-only import is public.
   The original module had no attached node with its own `proof_deps`; the report
   separately lists all eight unused dependencies of the parent coordinate plan,
   without claiming that they are globally pruned. Read the parent and
   `dag/units/sk-thm-picard-duality.json`: its `realized.statement` is empty and
   `realized.steps` is `[[]]`. This proof changes no unit realization or unit route.

5. **DAG agreement: PASS.** Read the new node and all three proof-dependency records.
   Its Lean statement is byte for byte the theorem signature; its mathematical
   statement includes the supplied naturality premise, every compatibility equation,
   the exact restriction-of-scalars homology comparison, and the universal conclusion.
   Its four proof steps match the cancellations, exact/projective induction,
   semilinear tensor calculation and homology rewrite. `proof_deps` is exactly the
   union of the steps' `uses`; the cited exactness/projectivity records point to
   Mathlib, and the homotopy-invariance node points to `Homotopy.homologyMap_eq`.
   The source and `proof_origin` accurately describe the projective form of the
   Stacks induction and use of the existing differential identity. Checked the
   new-node fields required by brief-stage3 section 3, its chapter, unit, blueprint
   ancestry and verbatim Lean attachment. There is no new Lean statement or hole
   hidden behind this bookkeeping attachment.

**Changes in this reading:** added this independent review and performed fresh
searches, compilation and axiom checks. No Lean or DAG repair was necessary. The
existing public docstring still describes the older common-K-flat-refinement plan;
that inherited documentation mismatch is already disclosed above and does not
alter the theorem or the proved algebraic route. Holes closed remain 1, holes added
0, split off 0. No global module pruning is asserted.
