## What changed

Replaced the rejected equivalent core obligation with actual constructions in
`PrimaryModuleFiltrationFixedFieldComparison.lean`: restriction of R to H, the representation
on each invariant subgroup, the relative quotient with trivial action, the equivariant subtype
inclusion, the associated sheaf under a specified canonical stalk equivalence, and the short
complex formed from that inclusion and its categorical cokernel. The canonical comparison predicate's
signature includes both a natural additive stalk isomorphism and its action on every represented
germ. The equivalence is data; its canonical compatibility is a proposition, avoiding a large
dependent structure during compiled-module generation. The associated sheaf is explicitly the inverse equivalence on the specified representation,
followed by inverse image across e; no arbitrary sheaf family is selected.

The unchanged item defines F(a) from A(min(a,n)). It combines four strictly smaller obligations:
the fixed-field comparison independent of any chain; exactness and quotient comparison for one
invariant subgroup inclusion; identification of one finite prime-field quotient; and inverse
image/restricted-stalk compatibility independent of any filtration or prime. Index equalities,
endpoint comparisons, and composition of the two quotient isomorphisms are written in Lean.
The zero associated-sheaf lemma and top-subgroup isomorphism are proved without new holes.

Deleted both rejected auxiliary modules and nodes, including the entire terminal module.
The elementary terminal isomorphism composition is inline. No existing statement, definition,
visibility, or target signature was changed. There are no forced adaptations or interface-change
records other than the diagnostic-only linter record. The item's public signature remains
unchanged; its nested hypothesis binder names require the unused-variable linter setting.
The preflight requested `coord/changes/primary-filtration-linter.md`, which documents that
diagnostic option and its lack of effect on imported declarations.

## Proved and sorry left

The rejected delivery must be described accurately: The target theorem is reduced to an equivalent
unproved core obligation; this split does not establish a mathematical reduction.

The repaired `AlgebraicGeometry.Scheme.exists_sheaf_filtration_of_invariant_primary_chain` has a
complete Lean proof from the four smaller obligations below. This is a decomposition, not an
unconditional proof: the original item's one hole is closed and four named lower holes are added
(net minus three before any pruning). The retired `exists_primary_filtration_core` is not counted
as mathematical progress. No hole remains in the item, in
`AlgebraicGeometry.Scheme.primaryAssociatedSheaf_zero`, or in the constructed
`AlgebraicGeometry.Scheme.primarySubmoduleTopIso`. No definition contains a hole.

Every remaining hole in this delivery is exactly one named public theorem:

- `AlgebraicGeometry.Scheme.nonempty_primaryFixedFieldComparison`, node
  `lem-sc-primary-fixed-field-module-comparison`, in `PrimaryModuleFiltrationFixedFieldComparison`.
- `AlgebraicGeometry.Scheme.primarySheafSequence_shortExact`, node
  `lem-sc-primary-subgroup-sheaf-exactness`, in `PrimaryModuleFiltrationSheafExactness`.
- `AlgebraicGeometry.Scheme.primaryTrivialQuotient_constant`, node
  `lem-sc-primary-constant-quotient-identification`, in `PrimaryModuleFiltrationConstantQuotient`.
- `AlgebraicGeometry.Scheme.primary_inverseImage_restriction`, node
  `lem-sc-primary-inverse-image-restriction`, in `PrimaryModuleFiltrationInverseImage`.

The module and helper constructions compiled during repair. All five modules compiled without warnings and the dry-run axiom probe passed.
Final validation is the requested deliver3.py dry run; no push is requested or made.

## No longer needed

- Removed the direct import `Sheaf.AlgebraicGeometry.AbelianSheavesGModules` from the original item.
  The item now uses the specified comparison C; its existence lemma handles this equivalence.
  That module is retained as a proof dependency of the smaller comparison module, so this is not
  a claim that its theory leaves the entire target import closure.
- Removed the direct import `Sheaf.AlgebraicGeometry.EtaleFieldGsets` from the original item.
  The item no longer works with the etale-scheme/G-set classification. It works with actual
  subgroup representations and the canonical abelian stalk comparison. The classification is
  still used internally by the existing abelian equivalence; no global pruning is claimed.
- Removed the direct import `Sheaf.FieldTheory.OpenSubgroupFixedField` from the original item.
  Fixed-field identification is isolated in the smaller comparison obligation, whose module
  retains this dependency and whose node cites `lem-exc-etale-open-subgroup-fixed-field`.
- Removed `PrimaryModuleFiltrationSheafTransportCore.lean` and node
  `lem-sc-primary-module-filtration-sheaf-transport-core`. Their existence witness was equivalent
  to the entire item and did not specify any relationship with A.
- Removed `PrimaryModuleFiltrationSheafTransportTerminal.lean` and node
  `lem-sc-primary-module-filtration-sheaf-transport-terminal`. Isomorphism composition is inline;
  the old terminal theorem's whole hypothesis list is unnecessary.
- Removed the direct import of the new comparison module from the item once compilation showed
  it was already made available by the three proof-only compatibility imports.

- The old proof-dependency nodes `def-exc-discrete-modules-category`,
  `def-sc-constant-sheaves`, and `def-weil-pbc-inverse-image` remain needed by the
  unchanged signature and explicit constructions; they are not invoked as proof lemmas.
  The old theorem dependencies `lem-exc-abelian-sheaves-gmodules`,
  `lem-exc-etale-field-gsets`, and `lem-exc-etale-open-subgroup-fixed-field`
  are no longer direct dependencies of the item; their actual remaining roles are
  through the comparison construction and its imported upstream equivalence.
- Second reading removed unused proof imports `Mathlib.Algebra.Module.ZMod` and
  `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` from the constant-quotient module.

No further existing module is asserted to disappear from the global target import closure.

## Where the brief, the DAG or earlier work was wrong

D1/D2 and G1: the former core did not connect G to A. Choosing G=F made its extra witness
vacuous, so it was equivalent to the whole item. It is deleted, not renamed. The repaired
construction instead fixes F(a)=P_C(V_A(min(a,n))) and fixes S to the cokernel complex of the
actual inclusion. Exactness is for one pair A<=B, constants for one concrete quotient, and
inverse-image compatibility is for the ambient module independently of any chain. These
statements cannot be converted back to the whole item merely by composing witness isomorphisms.

B2/H3: every new node statement introduces all fields, embeddings, acting groups, the natural
stalk comparison and its germ action, schemes, representations, subgroups, maps, and hypotheses.
The Lean predicate records the claimed stalk/action relationship. The relative quotient in the
constant lemma is explicitly B/(A intersect B), so no unstated inclusion hypothesis is needed.
That lemma assumes Ks is a separable closure, ensuring that extensions of Galois automorphisms
exist and its canonical-action requirement is substantive.

C1/D3: the comparison node cites the actual fixed-field and abelian-equivalence theorem nodes,
not six definition nodes in place of their proofs. The inverse-image node cites the existing
stalk-of-pullback theorem, Galois automorphism-extension theorem, and inverse-image composition
node. The constant node cites the constant-stalk and automorphism-extension nodes. New nodes
state the exactness and the remaining compatibility facts these interfaces do not supply.

H8: the revised item and all four obligation docstrings explain the construction and proof.
They specify integer multiplication modulo ell, a finite basis of the finite prime-field
quotient, the restricted stabilizers, the pullback-stalk comparison on projected neighborhoods,
its equivariance using haction, exactness under the equivalences, inverse image across e,
and n=0. The zero and top endpoints are actually proved. In n=0 there are no step obligations;
in A=B or B=0 the quotient is zero and its basis cardinal is zero. No assumption that Omega/K
is algebraic is used. The inverse-image docstring describes automorphism extension through
algebraic closures; the existing extension theorem also covers transcendental Omega.

F4/G1: the previous report and second-reading claims were incorrect. This report replaces them
and does not claim a closed mathematical proof, a strictly smaller old core, or a formal
relationship that was absent from the old signature. The required three removed imports are
listed explicitly above, with their actual remaining role in the repaired route.

The three-way search found Mathlib's subrepresentation and subtype constructions, which are
used. LeanFinder found no direct transport theorem; Loogle returned the subtype APIs; source
search found no full primary filtration transport. LeanSearch returned Internal Server Error
and is recorded as unavailable, not as a negative result. Read the existing theorem/node
interfaces and the primary Stacks pages 04JQ, 03QT and 03SF; the latter is a section on Galois
covers rather than the fixed-field correspondence itself, so the comparison docstring explicitly
adds the fixed-field correspondence source 0BML from the existing fixed-field node.

## New nodes

`lem-sc-primary-fixed-field-module-comparison` supplies only the canonical equivalence over the
fixed field, with its natural group stalk identification and represented-germ action. Its
statement has no R, M, ell, n, A or F. It also carries the actual representation/sheaf constructions
in its module, with the proved endpoint helpers. The natural stalk action determines the
functor up to natural isomorphism, hence its associated sheaves up to the isomorphisms used.

`lem-sc-primary-subgroup-sheaf-exactness` treats one invariant inclusion and the specified
inclusion-cokernel complex. It assumes trivial quotient action, and concludes exactness and
identification with the associated sheaf of that actual quotient. It has no finiteness, prime,
chain endpoints, or original sheaf.

`lem-sc-primary-constant-quotient-identification` identifies the associated sheaf of one finite
trivial relative quotient annihilated by a prime with an iterated constant-sheaf biproduct. It
has no chain, no exact-complex conclusion and no terminal comparison.

`lem-sc-primary-inverse-image-restriction` compares inverse image of the given M with the
associated restricted ambient representation, using the precise supplied additive isomorphism
and germ-action hypothesis. It has no prime, finite module, subgroup chain or filtration
conclusion. The nontrivial equivariance of the pullback-stalk comparison remains here openly.

All four nodes inherit chapter `sec-curve-estimates` and unit `sk-prop-cd-affine`; the unit
route is retained. The item's proof records point to exactly these four obligations. Each
new Lean statement has a complete proof in words in its docstring and a matching node.

Change record: `coord/changes/primary-filtration-linter.md` documents the diagnostic-only
option required to preserve the original nested binder names without warnings.


## Second reading by R3

1. Compared the delivered item with its repository version by diff and checked the
   entire existing theorem signature byte for byte, from `theorem` through the type
   before `:=`: identical. The other four modules are new, absent in the repository.
   There is no change to an existing definition or visibility. Restored the existing
   theorem's original docstring; the expanded construction explanation remains in this
   report and the new obligation docstrings.
2. Compiled all five modules locally with lcompile.py, cleanly. Inspected every
   construction: restriction, subrepresentation, relative quotient, subtype inclusion,
   inverse-equivalence sheaf and inclusion-cokernel complex contain actual data and no
   holes. There are exactly four named theorem holes, precisely those listed above,
   and no forbidden declaration mechanism. The delivery dry run supplies the appended
   axiom probes for all declarations. The original item is a decomposition, not an
   unconditional proof; the two endpoint helpers have complete proofs.
3. Read all four split signatures, docstrings and nodes, and the upstream abelian
   equivalence, fixed-field theorem, constant-stalk theorem and automorphism-extension
   theorem. Checked n=0, A=B, B=0, zero R, H equal to the whole group, and constant
   quotient with A not contained in B: the relative comap makes the latter B/(A intersect B),
   and hkill still annihilates it. The canonical natural stalk isomorphism and germ
   action determine the equivalence up to natural isomorphism, so this use of its
   inverse does not choose arbitrary undetermined sheaf data. Each remaining obligation
   is true, needed and strictly narrower than filtration transport. Independently
   searched Loogle for ShortComplex.ShortExact, LeanFinder for preservation of cokernels
   and stalk/restriction/constant-action comparisons, and grep for alternate stalk,
   restriction and trivial/constant phrasing. Also searched the project's sheaf and
   representation modules. InvariantFlagCategoricalFiltration has a private quotient
   helper in ordinary Rep over a prime field, not this discrete integer/sheaf comparison;
   it supplies no direct replacement. No remaining obligation admits a few-minute
   closure from the inspected interfaces. Verified the mathematical sources at
   https://stacks.math.columbia.edu/tag/04JQ,
   https://stacks.math.columbia.edu/tag/03QW, and
   https://stacks.math.columbia.edu/tag/0BML.
4. Followed the proof from the item downward: F is constructed using min indexing,
   each successor uses the explicit inclusion and its cokernel, and the two quotient
   isomorphisms and top endpoint are composed inline. No equivalent restatement of
   the item remains. Removed two unused proof imports in ConstantQuotient and added
   the missing proof-only GaloisAutomorphismExtension import for its recorded planned
   dependency. The original item's public imports remain required by its signature.
   No longer needed now accounts for every old proof_dep. The unchanged unit record
   sk-prop-cd-affine has empty realized statement/step lists; this item is not a realized
   unit key node and this delivery does not bypass or alter a unit step.
5. Read all five node records. The item's proof and its four proof_deps match the
   actual calls. Each new node has its self-contained statement, source, complete
   proof steps, their dependency union, proof_origin, search records, split status,
   creation/blueprint/chapter/unit records, and matching verbatim Lean signature.
   The inverse-image composition dependency is already available through the public
   UpperLowerStar.Defs import; the constant lemma's automorphism-extension dependency
   now has its missing import. No node statement repair was needed.

Second-reading changes: restored the original item docstring, removed two unused
Mathlib proof imports, added the missing proof-only automorphism-extension import,
and completed the pruning accounting. No signatures, definitions, proof bodies,
new node statements or hole counts changed.
