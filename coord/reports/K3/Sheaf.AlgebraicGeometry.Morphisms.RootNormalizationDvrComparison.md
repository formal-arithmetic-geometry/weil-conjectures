## What changed

Replaced the sole hole in `AlgebraicGeometry.Scheme.root_normalization_dvr_comparison`
by a compiling reduction with the original statement unchanged. Constructed the actual
principal-prime localization B and its uniformizer pi, proved its DVR structure and
irreducibility, transported the group-order unit, constructed the generic map through
the chart, and used the proved `GaloisCover.exists_baseChange` to obtain T.

The main module also proves the root-prime contraction and coefficient localization
of the root quotient in private helpers. The latter adapts the existing private
proof in RootFactorStalkLocalization; the DVR proof adapts the Krull-intersection
factorization pattern in FlatAssociatedPrimeDVR. Both helpers are fully proved.
The only remaining geometric step has its own module and node, and takes B, pi,
the generic map, T and its cartesian square, and the two algebraic certificates
as inputs. The new DVR module is fully proved; the new comparison module has one hole.
Only the sandbox was written. No existing signature, target, definition, or public
import of the item's module changed.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.root_normalization_dvr_comparison`.
Proved `IsLocalization.regular_principal_prime_dvr` without holes, together with
its private factorization helpers. The main private lemmas
`adjoinRoot_isLocalization_map` and `root_span_comap` are also proved.

Added one hole: `AlgebraicGeometry.Scheme.root_normalization_localization_comparison`,
node `lem-sbc-root-normalization-localization-comparison`. Its complete proof in words
and sources are in its docstring and node. There are no other holes in the delivery.
This is a decomposition (one upper hole closed and one strictly smaller geometric
hole added), not a claim that the original theorem is axiom-free. The original
algebraic and chart construction portions are genuinely proved.

## No longer needed

Second reading also removed the redundant proof import `Mathlib.RingTheory.Ideal.Quotient.Basic`
from the main module and the unused public import `Mathlib.Algebra.Regular.SMul`
from the new geometric comparison module. These Mathlib removals prune no project node.

Removed the direct proof import of
`Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange` from the item's module;
its general theorem is still needed by the remaining geometric comparison and is
imported there. Replaced the corresponding direct proof dependency edge by the
proved DVR node, the proved Galois-cover base-change node, and the new geometric node.
No node or module is globally pruned. No ramification, tame extension, or maximal-ideal
normalization statement is imported or used.

## Where the brief, the DAG or earlier work was wrong

The original DAG described the principal-prime DVR construction and the chart/torsor
construction without named dependencies, although these are substantial steps.
They are now concrete Lean proofs. The normalizing comparison still needs a geometric
assembly after the already-proved general stalk-base-change theorem; that remaining
assembly is the new comparison node, rather than a duplicate DVR-existence statement.
No mathematical error or changed statement was found. The unit route is unchanged.

Edge cases checked: H need not be a domain; the localization-domain proof uses regularity
and Krull intersection rather than an unjustified domain instance. A unit g is excluded
by primality of (g), and zero g is excluded by regularity and the nonzero quotient.
The root contraction proof works for n=1, and n>0 follows from the group instance.
Disconnected torsors are allowed; the supplied normalization point selects its stalk.

## New nodes

`lem-sbc-regular-principal-prime-localization-dvr` is fully proved in
`Sheaf.RingTheory.RegularPrincipalPrimeLocalizationDvr`. It states the principal-prime
localization criterion, with no domain hypothesis on H. Sources: Stacks 00IP and 00PD;
Mathlib localization, Krull intersection and DVR factorization APIs.

`lem-sbc-root-normalization-localization-comparison` is the sole remaining hole in
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationLocalizationComparison`. It proves
only the geometric comparison after all DVR, chart, torsor and root-algebra data have
been supplied. Source: Stacks 0307 and the affine normalization/stalk APIs.
LeanSearch was attempted but returned an internal server error; LeanFinder/Loogle
and source searches are recorded in the nodes. There are no change records because
no existing interface was changed.

## Second reading by K3

1. Interface: compared the existing module and node with the repository using diff.
   The original theorem signature is byte-for-byte identical after restoring one
   extra space before its proof delimiter. Its docstring and public imports are
   unchanged. No definition or target changed, and no matching open change record
   was found. The existing node changes only proof, proof_deps and proof_origin.
   Verdict: pass.
2. Proof: compiled all three modules locally in import order. Scratch-copy
   `#print axioms` checks covered all eight delivered declarations, including the
   private helpers. All six fully proved helper/DVR declarations use only propext,
   Classical.choice and Quot.sound. The original comparison and the new geometric
   comparison additionally use sorryAx, precisely as reported. There is exactly one
   written sorry, in the named new theorem; no definitions, arbitrary data choices,
   or prohibited declarations were introduced. B is the actual Localization.AtPrime,
   pi its generator image, and T comes from the proved GaloisCover.exists_baseChange.
   Verdict: pass as decomposition, not an axiom-free proof of the original theorem.
3. Split statements: read both new declarations and their docstrings and nodes.
   The principal-prime lemma handles rings with zero divisors using regularity and
   Krull intersection. A unit generator is excluded by primality; a zero generator
   by regularity in the nonzero local ring. For n=1, the root ideal contraction and
   coefficient localization still give the stated comparisons. Group nonemptiness
   gives n>0. Disconnected covers cause no problem: the supplied normalization point
   selects the local branch, and localization preserves its stalk. The remaining
   geometric theorem fixes B, pi, k, T, the cartesian square and the algebraic
   certificates; it does not restate their existential construction. Its proof in
   words follows localization of integral closure and the already proved stalk
   base-change theorem. Additional launcher searches used Loogle (IsLocalization,
   IsDiscreteValuationRing), LeanFinder (relative-normalization local-ring
   isomorphisms), and grep (integral-closure localization/normalizationPullback).
   Source searches of Mathlib, upstream and lean/Sheaf found general APIs and the
   previously reported private helpers, but no public exact replacement. Closing
   the remaining comparison requires substantial pullback and stalk transport,
   rather than a few-minute application. Verdict: pass.
4. Route/pruning: traced the proof from the original theorem downward. The DVR,
   chart lift, group-order unit, base-changed torsor, root contraction and quotient
   localization are real proved reductions. The only old proof dependency,
   lem-sbc-normalization-stalk-base-change, is no longer direct and is recorded in
   No longer needed; it remains used through the geometric node. Other added imports
   are proof-only. Removed two redundant/unused Mathlib imports as listed above.
   The unit sk-prop-input-spreading and its realized record (currently empty lists)
   are unchanged; no unit step is bypassed and no global project module is pruned.
   Verdict: pass.
5. DAG agreement: checked the existing node's three proof steps against the Lean
   construction and application, the union of their uses against proof_deps, and
   proof_origin against the actual route. Checked both new nodes' required metadata,
   verbatim Lean signatures, source/proof descriptions, chapter/unit and blueprint
   ancestry. The DVR node is fully proved; the geometric node has the sole hole.
   Verdict: pass.

Changes by the second reader: restored signature whitespace; removed the redundant
quotient proof import and unused public regularity import; corrected the new geometric
module's author to K3; retained the local unused-variable linter setting because the
unchanged signature contains the unused let-bound N0. No mathematical statement,
proof construction, definition or dependency node was changed by this reading.
