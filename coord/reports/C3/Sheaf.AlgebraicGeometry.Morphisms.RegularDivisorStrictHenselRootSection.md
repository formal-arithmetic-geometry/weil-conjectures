## What changed

Replaced `AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_section`'s hole
with a proof from a finite etale model over the root ring. The proof obtains a
section of that model, restricts it by a pullback lift, transports it through the
model's punctured-cover isomorphism, and projects to `W.P`. Both projection
identities are checked explicitly. The existing signature and docstring are
unchanged, and the three added imports are private proof imports.

Added `StrictHenselRootFiniteEtaleModel`, isolating the ramification and purity
argument. Added `FiniteStrictHenselianAlgebraEtaleSection`, proving the general
section theorem from the existing finite henselian algebra decomposition and the
source library's etale-neighbourhood section theorem. Finite group cardinality
positivity makes the root polynomial monic; Mathlib supplies its module finiteness.
Updated the original DAG proof to this assembly. No definitions or existing
statements changed. The second reading replaced the general section module’s public
StrictlyHenselian import with direct public Henselian and Etale imports, retaining
StrictlyHenselian as a private proof import.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_section`
(node `lem-sbc-regular-divisor-strict-hensel-root-section`).

The new general theorem
`AlgebraicGeometry.Scheme.finite_strict_henselian_algebra_etale_section`
(node `lem-sbc-finite-strict-henselian-algebra-etale-section`) has a complete proof.
It uses existing declarations, whose transitive dependencies may still have holes.

Added exactly one hole:
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model`
(node `lem-sbc-strict-hensel-root-finite-etale-model`). Its proof is exactly
`by sorry`, with a complete sourced argument in the docstring. This is a
one-for-one decomposition, not a net reduction in holes or a proof free of sorry.
The remaining theorem asserts an extension and an isomorphism over the puncture;
it asserts no section. The section and its projection equation are constructed by
Lean from it and the proved general section theorem.

## No longer needed

No modules were pruned. No existing imports were removed. The old direct proof
dependencies `def-sbc-normal-dominant-galois`,
`def-weil-pbc-strict-henselization-limit`, and `def-weil-regular-scheme` are no
longer direct proof dependencies of the original theorem; they remain statement
and geometric-model dependencies, so none is globally no longer needed. The original definition nodes still
underlie the signatures and the geometric model obligation; their replacement by
explicit proof nodes at the upper theorem does not prune those definitions.
No node or module of the unit's route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies recorded definitions, rather than declarations
for the ramification calculation and strict henselian splitting. The splitting
part can be assembled from the existing
`HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi` and
`Scheme.exists_section_of_etale_of_isStrictlyHenselianLocalRing`. The remaining
geometric model is now exposed as a separate obligation.

Read Stacks Tags 0EYG, 0EYE, 04GH and 04GK on the official site, and the existing
Lean signatures and proofs. Checked the zero finite algebra (empty coproduct),
finite product algebras, the trivial group (degree one), unit divisor equations,
and nonunit equations. The model's surjectivity follows from the dense puncture
and closed finite image; in the unit case the puncture is the whole root scheme.
The finite-algebra section theorem needs no finiteness assumption on its etale
morphism, because the section theorem applies separately to each local factor.

The Mathlib `sigmaSpec` isomorphism instance requires its finite index type to
have the scheme's universe. Reindexing `Fin n` by `ULift` supplies that requirement
without changing any public statement.

## New nodes

`lem-sbc-strict-hensel-root-finite-etale-model` records the finite etale extension
in the construction of C in 0EYG. It keeps the specified root algebra and divisor
equation, and carries the only new hole.

`lem-sbc-finite-strict-henselian-algebra-etale-section` records the proved general
section assembly, including the empty algebra. The finite henselian decomposition
is a generic tool from another unit, rather than a replacement of the spreading
unit's route.

`lem-sbc-strict-henselian-etale-neighbourhood-section` attaches the already proved
source declaration used for the local factors; no Lean module or hole is added
for it. No existing DAG node attached this specific section declaration.

## Second reading by C3

1. Compared the original module and DAG node with their repository versions.
   The original signature and docstring are byte-for-byte unchanged. Only its
   proof, private proof imports, and the node's proof/proof_deps/proof_origin
   changed; no target, definition, or existing interface was modified.
2. Compiled all three delivered modules with lcompile.py, in import order,
   without errors or warnings. A scratch module printed axioms for all three
   declarations: only propext, Classical.choice, Quot.sound and sorryAx occur.
   The only explicit hole is strict_hensel_root_finite_etale_model, a named
   theorem with a sourced full natural-language proof and matching node.
   There are no definitions, forbidden trust mechanisms, or arbitrary data
   definitions choosing witnesses of existence.
3. Read the model obligation and the general section assembly, including the
   imported finite-henselian decomposition and existing local section proof.
   Checked the trivial group (positive degree one), unit g (V=N), nonunit g
   (regular local root ring), empty finite algebra (empty coproduct), and finite
   product factors. The model is true and is the extension part of 0EYG,
   before choosing a section; it does not restate the original conclusion.
   Read Stacks 0EYG, 0EYE and 0BRM on the official site. Independent leanfinder
   search for “Abhyankar lemma finite etale extension across regular divisor
   after taking root”, loogle search for “AdjoinRoot”, and grep for
   “Abhyankar|purity|ramification|henselian.*section”, plus source searches with
   rg, found no shorter existing full model theorem. The geometric extension
   hole cannot be closed in a few minutes with the available declarations.
4. The original proof constructs the section and checks both projections using
   pullback identities; the general theorem assembles local sections via
   sigmaSpec and Sigma.desc, including the empty case. No shorter available
   route was found. All original imports provide statement vocabulary; the
   three additions to the original module are private proof imports. Fixed
   the new general theorem's proof-only public StrictlyHenselian import.
   Listed all old direct proof dependencies above; none of their modules is
   pruned. Read sk-prop-input-spreading.json, whose realized arrays are empty:
   this delivery preserves the trait/root-extension/splitting route described
   by the unit and does not alter any unit realization.
5. Checked the new node fields, verbatim Lean signatures, proof steps and
   proof-dependency unions. The original node matches its pullback assembly;
   the model node matches the geometric obligation; the general section node
   matches the product assembly. The existing local section declaration has
   no other DAG attachment. Kept its existing-declaration attachment without lean.file (as preflight
   requires), and corrected its proof_origin to the actual source theorem
   and Stacks 03QO.

Second reading changed only the general theorem's import visibility, the local
section attachment metadata, and this report. One original hole is closed and
one geometric hole added: a one-for-one decomposition, not a net sorry reduction.
