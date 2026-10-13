## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.exists_pow_smul_eq_zero_of_perfect_supported`
with a complete Lean reduction of the affine/Mayer--Vietoris argument in
[Stacks Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ).
The original statement, binders, universes and visibility are unchanged.

The induction property ranges over every integer shift and every morphism on an open
between restrictions of the fixed global objects. It does not just range over restrictions
of global morphisms: the overlap preimage in Mayer--Vietoris is an arbitrary local morphism.
The union step chooses exponents a and b for the two restrictions, lifts f^(a+b) times the
map to the negative overlap term, kills that preimage using the overlap induction hypothesis,
and uses scalar equivariance to obtain exponent c+a+b. The exponent identities and the
restriction/precomposition compatibility are fully proved in the item's module.

The top-open restriction is proved faithful without a new hole: its underived functor is
an equivalence by `Modules.overFunctorEquiv`, restriction along `X.topIso`, and the identity
and composition comparisons for `Modules.restrictFunctor`. Its exact derived functor is
therefore an equivalence. The proof cancels the zero-shift isomorphism and converts
precomposition by the scalar identity to the original `schemeDerivedScalar` conclusion.

Added two separate modules for the unfinished affine argument and the scalar-compatible
Mayer--Vietoris boundary. Each contains one named public theorem, its source and detailed
proof in words, with a matching new DAG node. Updated the parent node's proof, proof_deps
and proof_origin to describe the compiled reduction.

Validation: the three modules compile together in import order with lcompile.py, without
errors or warnings. Lines are at most 100 characters. No existing statement, definition,
public import or target was changed; no forced adaptations are needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_pow_smul_eq_zero_of_perfect_supported`
(node `lem-sc-perfect-into-support-on-T`). Its body now contains no sorry.

Added these two holes, each exactly `:= by sorry` in its own new module:

- `AlgebraicGeometry.Scheme.perfect_support_affine_open_torsion`,
  node `lem-sc-perfect-support-affine-open-torsion`, module
  `Sheaf.AlgebraicGeometry.PerfectSupportAffineOpenTorsion`.
- `AlgebraicGeometry.derived_open_hom_scalar_mayer_vietoris`,
  node `lem-sc-derived-open-hom-scalar-mayer-vietoris`, module
  `Sheaf.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris`.

This is a decomposition, not a completed proof of the mathematical theorem:
1 original hole closed, 2 holes added, raw difference -1. No claim is made about the
ledger's transitive closure count. Existing dependency holes were not changed.
The affine statement is only the affine-open case and has no qcqs hypothesis. The
boundary statement has no support, perfectness or quasi-coherence assumptions and
asserts an additive, scalar-compatible exactness interface, not power annihilation.
Neither restates the global theorem.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`.
- `Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective`.
- `Sheaf.Paper.DerivedHomMayerVietoris`.

The first two remain proof dependencies of the new affine node and are imported there.
The Mayer--Vietoris module is already publicly available through the unchanged
`DerivedGlobalScalar`/`DerivedCategory` statement imports and is used in the boundary
node. The corresponding old direct parent-node edges are replaced by edges to the two
new statements. None of these modules or nodes is globally dispensable, and no globally
pruned module is claimed. `QuasiCompactOpenInduction` remains directly used.

An intermediate experiment using `OpenExtensionRestrictionIso` was replaced by the
Mathlib top-scheme restriction equivalences; that experimental import is absent from
the delivery. No new dependency on extension by zero is required for top faithfulness.

## Where the brief, the DAG or earlier work was wrong

The high-level proof plan is mathematically correct, but its current interfaces are not
sufficient as a one-line application. `derived_hom_mayer_vietoris` supplies an additive
boundary and exactness for a cover of the whole ringed space; it does not assert scalar
linearity of that boundary or its localized-union, shifted-target form. The new boundary
statement isolates precisely this missing interface. Its proof follows the naturality
of the triangle and adjunction construction of
[Stacks Tag 08BW](https://stacks.math.columbia.edu/tag/08BW), as used in Tag 08EJ.

The affine equivalence and bounded-projective presentation do not themselves state
power annihilation of derived Hom. The finite-projective single-term calculation,
truncation induction, open-subscheme transport and scalar compatibility remain in
the new affine statement, with their full argument recorded in its docstring and node.

The unit `sk-thm-picard-duality` was read; its realized arrays do not designate this
node as a unit-level step. The existing affine-then-Mayer--Vietoris route is kept.
No false statement, source error or tool workaround was found.

## New nodes

`lem-sc-perfect-support-affine-open-torsion` is the affine-open base case of Tag 08EJ,
for all local morphisms into every shift of the restricted target. It depends on the
existing affine equivalence and perfect-projective model nodes, plus the existing
open-derived restriction comparison. Edge cases checked mathematically: empty affine
open, zero source/target, f=0, f=1, arbitrary negative shifts, and non-qc ambient X.
For f=0 exponent 1 suffices; for f=1 the target restricts to zero, so every local Hom
is zero. No assumption that the ambient scheme is affine or separated was introduced.

`lem-sc-derived-open-hom-scalar-mayer-vietoris` is the scalar-compatible boundary on
an arbitrary union, with source the overlap Hom into shift k-1. It is a structural
consequence of the natural Mayer--Vietoris sequence and canonical restriction/shift
comparisons, independent of the affine torsion statement. Edge cases checked:
empty U or V, equal U and V, empty overlap, k=0 and negative k, r=0 and r=1.
Exactness is asserted only at the union Hom term, not surjectivity onto overlap Hom.

For both new nodes, LeanSearch was attempted but returned Internal Server Error.
LeanFinder, Loogle and Mathlib grep were run with results recorded
in their JSON. Whole-library and whole-DAG searches found ordinary section torsion,
module support and additive Mayer--Vietoris results, but no statement of either new
interface. The new nodes inherit the parent's chapter and unit and trace back to
`lem-sc-finite-duality`. No change record is required because no existing interface
was changed.

## Second reading by T3

1. Compared the complete delivered item against the repository version by diff.
   The existing theorem signature, universes, binders, visibility and docstring are
   byte-for-byte unchanged. All existing public imports are unchanged. The only
   additions are three private proved helpers, the reduction, and two new theorem
   modules; there are no definitions or interface changes. Verdict: pass.
2. Compiled the item and the delivered dependency set locally with lcompile.py.
   The item has no sorry. The two new named theorems are the only delivered holes,
   each exactly `:= by sorry`. A scratch copy with explicit `#print axioms` for all
   three public theorems reports only propext, Classical.choice, Quot.sound and
   sorryAx. There is no axiom, unsafe, opaque, extern, implemented_by, or chosen
   data definition in the delivery. Verdict: pass, conditional on the two reported
   lower holes, not a sorry-free proof of the original mathematical result.
3. Read Stacks Tags 08EJ and 08BW online (the cited local TeX files are absent on
   this machine), and read both new Lean modules and nodes. The affine theorem
   is the affine-open case of 08EJ, with arbitrary local maps and integer shifts;
   removing ambient qcqs is valid because its argument takes place on affine U.
   Tested empty U, zero source/target, f=0 (exponent 1), f=1 (zero restricted target),
   and negative shifts. The boundary theorem is the negative Ext boundary of 08BW
   on W=U union V; shift comparison gives k-1, and naturality of the open-cover
   construction in E gives precomposition compatibility with global scalars.
   Checked empty opens/overlap, U=V, r=0, r=1 and negative k. No surjectivity onto
   arbitrary overlap Hom is asserted. Neither theorem restates the global item.
   Independent LeanFinder searches used finite-projective localization and
   connecting-map naturality wording; Loogle checked localization and the triangle
   name, and grep checked torsion/boundary and Mayer--Vietoris. Searches of lean/Sheaf,
   lean/WeilConjectures and the upstream checkout found no duplicate. Mathlib's
   K-projective and single-projective Hom lemmas help the affine proof, and ordinary
   sheaf Mayer--Vietoris helps the boundary proof, but neither closes either whole
   statement in a few minutes. Verdict: pass; both remain substantive subproblems.
4. Read the affine equivalence, bounded-projective model, open restriction comparison,
   derived Hom Mayer--Vietoris and quasi-compact induction interfaces. The existing
   Mayer--Vietoris statement lacks scalar compatibility and applies to a whole-space
   cover, so it cannot replace the new boundary by direct application. The reduction
   correctly quantifies over arbitrary local maps, kills restrictions with a+b,
   kills the overlap lift with c, and uses c+(a+b). Top faithfulness and cancellation
   are proved, not assumed. The report lists every removed old parent proof edge;
   their modules remain needed below the new nodes. The unit sk-thm-picard-duality
   has empty realized statement/step arrays, and the affine/Mayer--Vietoris route
   is retained. No globally pruned module is claimed. Verdict: pass.
5. Compared the parent-node changes: only lean/proof/proof_deps/proof_origin fields
   differ. Its three proof dependencies match the three applications in the Lean
   proof. Both new nodes have source, detailed proof, search records, created,
   blueprint ancestry, chapter/unit and verbatim Lean statement records. Their
   module visibility and statement imports are appropriate; remaining plain proof
   imports retain the planned interfaces needed to discharge their holes.
   Verdict: pass.

Second reading changed only this report by adding the independent review and explicit
axiom/search evidence. No mathematical or Lean repair was needed. The accounting remains
one original hole closed and two strictly partial holes added: a decomposition with raw
net -1, not a completed mathematical proof and not claimed ledger progress.
