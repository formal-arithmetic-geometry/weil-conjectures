## What changed

Proved `AlgebraicGeometry.Scheme.ideal_power_affine_denominator_map` with its
original signature and visibility. Its three public imports stay unchanged.
Added proof imports for compatible denominators, a compatible-pair presentation,
localization of quasi-coherent modules, and elementary quotient/unit algebra.
The local helper `annihilates_on_affine_subopens` is proved and private.

The argument follows the affine denominator construction of Stacks 01PM/01PQ.
It uses exponent `n=t*k+1`, a convenient nonminimal bound. Instead of choosing
images of monomials and checking their relations, it constructs the submodule
of compatible pairs `(b,m)` satisfying `g_i^k*m=j_n(b)*y_i`. The first projection
is surjective by ideal-span induction; the second descends modulo the common
kernel using the first isomorphism theorem. Localized cancellation proves the
required restriction identity, even in F before applying its cokernel map.

Added four proved modules: `AffineIdealGeneratorCover`,
`AffineCompatibleDenominatorData`, `GeneralIdealPowerAffineSections`, and
`IdealPowerNumeratorPresentation`. The general-power module exposes the already
proved private helper `Modules.powers_affine_sections` from
`CoherentSupportVanishingIdealNilpotence`, rather than reconstructing an
IdealSheafData or proving the support theorem. All imports of these ingredients
are proof imports. Updated the original node's proof and proof dependencies to
match the implementation. Existing definitions and statements are unchanged;
there are no forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ideal_power_affine_denominator_map`.

The new declarations `AlgebraicGeometry.Scheme.affine_ideal_generator_cover`,
`AlgebraicGeometry.Scheme.affine_compatible_denominator_data`,
`AlgebraicGeometry.Scheme.general_ideal_power_affine_sections`, and
`AlgebraicGeometry.Scheme.ideal_power_numerator_presentation` are all proved.
Both private helpers (local annihilation and the ideal-power bound) are proved.
No `sorry` remains in any delivered module; no holes were added. This is a proof,
not a decomposition into unproved intermediate statements. Imported declarations
retain whatever dependency status the last green build has; no assertion about
the entire targets' axiom closure is made here.

Edge cases are covered by the uniform constructions: zero generators yield
`n=1`, the whole module as K, and an empty cover; a unit ideal needs no special
case; empty affine opens and the zero ring are included. The numerator lemma
also allows `k=0`.

## No longer needed

No original public import was removed. The original planned dependency
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`, module
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`, is not
used by this proof: its IdealSheafData-specific interface is replaced by the
already proved general recursive-power calculation. The new route does not
need affine identification of A_n with a localized annihilator, nor of Q_n with
an affine quotient. It proves local annihilation directly, so the finite
generation/localization-of-annihilator subargument is pruned.

The original direct proof dependencies on the affine tilde/Gamma adjunction,
finite-type affine equivalence, tensor-product affine sections, and cokernel/image
modules are replaced by the four explicit intermediate nodes. These existing
nodes still occur indirectly in the proved helpers; they are not claimed to be
removed from the global target closure. The explicit localization-away definition
need not be a separate direct proof dependency: localization is invoked through
the already proved module-section lemmas in Modules.Tilde. No claim is made that
a module is globally unreachable from all five targets.

## Where the brief, the DAG or earlier work was wrong

No original statement was disputed or changed. The original plan unnecessarily
identifies affine annihilator and cokernel sheaves and describes a monomial
presentation; the compatible-pair construction avoids both extra interfaces.
The generic recursive-power fact was already proved as a private helper in
CoherentSupportVanishingIdealNilpotence but had no separately recorded node;
the delivery gives it a public wrapper and a node.

The recorded local source file `literature/stacks-project/properties.tex` is
absent on this machine. The source was read from the official Stacks 01PM and
01PQ pages. The recorded blueprint `_section.md` for `sk-thm-p1` is also absent;
the unit JSON contains its statement, proof steps, and realized-node list, which
were read. No unit statement or realized step is bypassed. The leansearch service returned an internal server error; those
searches are recorded as unavailable, with leanfinder/loogle/grep searches and
local library searches providing the other checks. Shared compiler-slot waits
are substantial; no compilation mechanism or limit was bypassed.

## New nodes

`lem-weil-pbc-affine-ideal-generator-cover`: finite generators of the affine
section ideal cover exactly the locus of surjectivity on stalks. Its proof uses
finite affine sections, the unit-module stalk isomorphism, localization, and
zeroLocus_span. Module: `Sheaf.AlgebraicGeometry.AffineIdealGeneratorCover`.

`lem-weil-pbc-affine-compatible-denominator-data`: localization, finite maxima,
and overlap clearing produce numerators with exact cross relations and a common
positive exponent. Module: `Sheaf.AlgebraicGeometry.AffineCompatibleDenominatorData`.

`lem-weil-pbc-general-ideal-power-affine-sections`: public access to the existing
proved generic quasi-coherent ideal-power/affine-section calculation. Module:
`Sheaf.AlgebraicGeometry.GeneralIdealPowerAffineSections`. Its proof is an
application of the existing helper, with no new unproved premise.

`lem-weil-pbc-ideal-power-numerator-presentation`: the bound on ideal powers and
the compatible-pair submodule produce a surjective linear presentation with the
scalar identities used for quotient descent. Module:
`Sheaf.AlgebraicGeometry.IdealPowerNumeratorPresentation`.

Each node has a complete source-based proof, self-contained statement, recorded
searches, exact Lean signature, and the original item's blueprint ancestry and
unit. There is no change record because no existing interface changed.

## Second reading by X3

1. Compared the delivered target module with the repository by `diff` and
   extracted its complete theorem header: the original signature is byte for
   byte identical, including Mono, quasi-coherence, finite type, hann, hquot,
   both open inclusions, the representative condition, and the cokernel formula.
   No existing definition or visibility changes. The other four modules are
   new; there are no adapted modules or interface change records. PASS.
2. Read all five modules and both private helpers. The compatible-pair submodule
   is constructed by linear equations; its surjectivity follows by span
   induction. Quotient descent uses the first isomorphism theorem, with its
   kernel inclusion proved, and cancellation uses unit restrictions on actual
   basic opens. Local annihilation uses quasi-coherence of the power, not of
   arbitrary F. All five modules compiled cleanly through lcompile.py. No sorry,
   axiom, unsafe, opaque, implemented_by, extern, or holed data construction
   occurs in the delivered Lean. Explicit axiom checks are recorded below. PASS.
3. No unproved statements are split off. Each new proved theorem supplies a
   proper part of the argument, with a source and a complete proof docstring.
   Checked t=0 (J=0, n=1, E=P_1(V) times M, K=M, empty cover), k=0 in the
   numerator presentation (for t>0 the cross relations identify all x_i and
   H=R), n=0 in the general power formula, the unit ideal, zero ring, and empty
   affine opens. The bound also holds for t=0,k=0 because J^1=0. Independent
   leanfinder search for finite principal-open covers/common denominators,
   loogle search `Ideal.span, HPow.hPow`, launcher grep for ranges/powers/stalk
   surjectivity, and local rg searches found no shorter complete denominator
   theorem. StructureSheaf.normalize_finite_fraction_representation concerns
   ring sections; KoszulCechStageLifting.finite_affine_denominators concerns
   modules over Spec and does not supply the overlap compatibility or ideal
   cover. Existing powers_affine_sections is reused directly through import
   all; the public wrapper records and exposes it without a duplicate proof.
   Checked the Stacks sources [01PM](https://stacks.math.columbia.edu/tag/01PM),
   [01PQ](https://stacks.math.columbia.edu/tag/01PQ), and
   [01IN](https://stacks.math.columbia.edu/tag/01IN). PASS.
4. The proof opens the original hole and reduces it to proved localization,
   finite sections, recursive-power and quotient facts. It avoids the planned
   affine annihilator/cokernel identification. Read sk-thm-p1.json, including
   all realized statement and step nodes: none is bypassed by this calculation
   below the unit level. Original public imports are preserved. Narrowed two
   new modules' imports: ModuleStalkFunctor supplies their signatures;
   IdealModuleProductStalk is only a plain proof import of the generator cover
   and is no longer a direct import of compatible denominator data. The exact
   old direct proof dependencies removed are:
   def-weil-pbc-module-localization-away,
   lem-weil-pbc-affine-tilde-gamma-adjunction,
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections,
   lem-weil-pbc-quasi-coherent-finite-type-affine,
   lem-weil-pbc-quasi-coherent-module-cokernel-image,
   lem-weil-pbc-quasi-coherent-tensor-product-affine-sections.
   The spec-module-tilde-sections dependency remains direct. These removals
   describe the node's direct proof dependencies, not global module pruning.
   No existing import or globally unreachable module is claimed pruned. PASS.
5. Read every delivered node against its Lean theorem and proof. Each
   proof_deps set equals the union of step uses, and all referenced nodes exist.
   The target's three dependencies match compatible data, numerator presentation,
   and localization; the new nodes record finite sections/stalks, localization,
   or the already proved power helper, as appropriate. Checked sources,
   proof_origin, created item/group, chapter/unit, blueprint ancestry, searches,
   and matching declarations. Corrected all four new lean.statement fields to
   preserve the exact multiline Lean signatures; in particular this restores
   the syntactically significant newline after `let n := t * k + 1`. PASS.

Second reading changed import visibility/dependencies in the two cover/data
modules and verbatim signatures in the four new node records. The mathematical
proofs needed no repair; no hole was added or removed by these review edits.

Explicit `#print axioms` audit compiled successfully after the import repairs:
all five public theorems and both private helpers depend only on propext,
Classical.choice, and Quot.sound. None depends on sorryAx. The scratch audit is
retained under scratchpad/Audit.lean, outside the delivered modules.
