## What changed

Repaired return X-fd7ae (H9, review point 5): deleted the unused proof import
`Mathlib.GroupTheory.GroupAction.Hom` from the orbit-product module.

Repaired return X-605c7: deleted the unused group-action import (H9) and
replaced the equivariant-descent node's top-level statement with the reviewer's
self-contained text (B2). The Lean theorem and its `lean.statement` are unchanged.

Corrected `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits` in the owned
DescentCore module: the number of orbits and stabilizers are now existentially
chosen, with `m ≤ d`, instead of arbitrary inputs. The former interface has a
Mathlib-only counterexample in the same module. The counterexamples remain.

Added the explicit `affineTorsorEquivariantAlgebra` construction (intersection
of algebra equalizers) and completely proved
`affine_torsor_equivariant_orbit_product`: actual orbit quotient, representatives,
stabilizers, a pointwise algebra map, and injectivity/surjectivity by transport.
No finite-group or domain hypotheses are needed for this algebraic proof.

The corrected core composes an isomorphism to that equivariant algebra with the
proved stabilizer product equivalence. It explicitly restricts the Spec map to
the correct principal open and verifies the equation over Spec H. This is a
real composition proof, not a restatement or application of the false helper.
The core also has the standard copyright header.

One forced caller adaptation preserves the public statement and visibility of
`affine_torsor_fixed_puncture_descent`, taking its witnesses from the repaired
core instead of the vacuous orbit-data theorem. Core and caller DAG proofs are
updated. Change record:
`coord/changes/affine-torsor-fixed-orbits-actual-stabilizers.md`.

## Proved and sorry left

Closed in the owned module:
`AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits`
(node `lem-sbc-affine-torsor-fixed-puncture-descent-core`), after the necessary
source-faithful statement correction. The former false universal statement is
not claimed proved. No `sorry` remains in DescentCore or the adapted parent.

Added and completely proved:
`AlgebraicGeometry.Scheme.affine_torsor_equivariant_orbit_product`
(node `lem-sbc-affine-torsor-equivariant-orbit-product`). Its proof uses only
Mathlib and the explicit equivariant-algebra definition, and no sorry axiom.
The already proved vacuous `affine_torsor_orbit_data` and the three private
counterexample helpers are preserved.

Only added hole:
`AlgebraicGeometry.Scheme.affine_torsor_equivariant_descent`
(node `lem-sbc-affine-torsor-equivariant-descent`), in its own module. It asserts
descent to the whole equivariant-function algebra over Spec H; it does not
assert the orbit decomposition or the fixed-ring product. Its docstring and
node explain the torsor recognition, component action, affine descent, and
injective-localization argument, with Stacks sources. No data are chosen from
this unproved existence theorem in any definition.

This is an interface repair and decomposition: one owned hole closed, one
strictly smaller geometric hole added (net zero holes); the algebraic part and
principal-open transport are genuinely proved. Every delivered module compiles
without errors or warnings using lcompile.py. The delivery dry run probes axioms.

## No longer needed

Removed unused proof import Mathlib.GroupTheory.GroupAction.Hom from Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct.

Repair H9: removed unused public import `Mathlib.GroupTheory.GroupAction.Basic`
from `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra`.

Removed proof import
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric`
and proof dependency `lem-sbc-affine-torsor-fixed-puncture-geometric`.
Its arbitrary-orbit conclusion is false for the same empty-orbit example and
is never used by this proof. This delivery does not edit its unheld statement.

Removed proof import
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureCompatibility`
and proof dependency `lem-sbc-affine-torsor-fixed-puncture-compatibility`.
The compatibility equation follows directly from Mathlib's `Over.w` for the
actual isomorphism over Spec H. No bespoke compatibility theorem is needed.

The parent no longer uses `affine_torsor_orbit_data` or node
`lem-sbc-affine-torsor-fixed-puncture-orbit-data`; that theorem merely chooses
an empty family unrelated to the cover. It is preserved for interface stability
but has no role in this route. No additional public imports were removed.
The parent DAG's old abstract Galois-category dependencies are replaced by the
repaired core, which records the precise remaining geometric subproblem.
Explicitly, the parent no longer directly uses `lem-fet-galois-category` or
`thm-galois-abstract-equivalence`. The former remains a planned dependency of
the new open geometric descent theorem, so it is not globally pruned. Its module
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`, together with
`WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra`, is imported privately
by that open theorem, matching its recorded proof plan (stage 2 §3.7).

## Where the brief, the DAG or earlier work was wrong

The original core and geometric helper omit every condition relating `m,K` to
the split-cover descent action. The former core accepts `m=0` for a nonempty
identity cover, a contradiction certified by the preserved private theorem.
The old caller compounds the error by choosing all stabilizers as bottom.
A plain scheme isomorphism also does not imply compatibility over H, as the
Compatibility module's independent swap counterexample records. This delivery
uses an isomorphism in Over(Spec H) at the geometric interface and proves the
remaining projection transport explicitly.

Tag 0EYG concerns tame ramification and its normal-domain argument; it is not
by itself a proof of the arbitrary-orbit statement. Tag 03SF and affine descent
(Tags 023R and 0245) support the corrected reduction. The new node source and
proof text identify exactly what remains to formalize. LeanSearch returned an
Internal Server Error; the semantic search, local Mathlib/source search, and
blueprint searches were completed and recorded. The compiled baseline briefly
still exposed the old Compatibility signature; the proof uses the stable
Mathlib Over API directly and no unavailable source-only declaration.

## New nodes

`def-sbc-affine-torsor-equivariant-algebra`: explicit H-subalgebra of functions
on Fin d satisfying `ρ a (f i) = f (α a i)`, with real data and no proof hole.
Module `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra`.

`lem-sbc-affine-torsor-equivariant-orbit-product`: algebraic orbit decomposition,
fully proved for arbitrary groups and commutative algebras. Module
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct`.

`lem-sbc-affine-torsor-equivariant-descent`: strictly geometric descent to that
whole equivariant algebra, one remaining public theorem with exactly `by sorry`.
Module `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent`.
For d=0 the function algebra and fixed-ring product are zero rings with empty
Spec; for a trivial action the algebraic decomposition has d singleton orbits
and full-group stabilizers; for a trivial torsor it yields the original split
cover. These are consistent with the repaired statement and the node proof.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent` (unclaimed)
is the only adapted module. Original lines 93–97 no longer type-check against
the changed core: `K` is supplied where the new theorem expects its etale
hypothesis. The adapted proof obtains `m,K` from the conclusion instead and
forgets the extra bound. Its existing signature and visibility stay identical.
The counterfactual compiler error is recorded below and checked by deliver3.py.


## Earlier second reading (a previous round; superseded)

1. Compared both existing delivered modules with the read-only repository using
   diff. The parent's complete signature, docstring, universes, imports and
   visibility are byte-for-byte unchanged; only its forced application changes.
   The owned core's sole signature change is the recorded correction from
   arbitrary input m,K to existential orbit data. The original is false, as
   its preserved Mathlib-only empty-orbit counterexample proves. No target or
   existing definition changes. Verdict: documented interface repair, not an
   unchanged-statement proof of the former false theorem.
2. Compiled all five modules in import order through lcompile.py, without
   errors or warnings. The only textual sorry is the public named theorem
   AlgebraicGeometry.Scheme.affine_torsor_equivariant_descent, with its own
   docstring and node. No forbidden declaration or hollow definition occurs.
   Explicit scratch-copy #print axioms checks cover every delivered declaration,
   including the three private counterexample helpers. The algebraic construction,
   orbit decomposition and counterexamples use only the allowed axioms; the
   geometric descent, corrected core and parent additionally use sorryAx from
   the one recorded geometric hole. Verdict: sound conditional reduction.
3. Read the split-off descent statement and its whole natural-language argument.
   Nonzero h in the domain gives a nonempty connected torsor open; finite faithful
   flatness persists after localization. The etale and unique-rotation assumptions
   identify its torsor relation, so the splitting gives a permutation action.
   Faithfully flat affine descent and simultaneous denominator clearing then
   give precisely the asserted equivariant algebra puncture over H. The action
   convention agrees with the proved transport equation in OrbitProduct.
   Tested d=0, d=1, trivial torsor and trivial component action in the mathematical
   argument; none needs extra hypotheses. The split-off result contains no orbit
   quotient or fixed-ring product: those are a separate, completely proved part.
   The new explicit subalgebra uses no existence witness. Fresh LeanFinder,
   Loogle and grep searches with semilinear/permutation/equalizer terminology found
   ingredients only. Read TotallySplit.fixedPointsCoordFamilyEquiv (coordinate
   invariants only), DescentDatum.descendedEquiv (requires a supplied descent
   datum), and geometricFiber_quotient_of_isAffine (geometric points only).
   None closes this geometric recognition theorem in a few minutes. Sources
   checked: [03SF](https://stacks.math.columbia.edu/tag/03SF),
   [023R](https://stacks.math.columbia.edu/tag/023R), and
   [0245](https://stacks.math.columbia.edu/tag/0245). Verdict: true, strictly
   smaller geometric subproblem with sufficient proof documentation.
4. Read the proof from the core downward: geometric descent, actual orbit
   decomposition, Spec of the inverse algebra equivalence, restriction of the
   principal open, and Over.w for compatibility. The transport is an actual Lean
   proof. The old arbitrary-data geometric helper and compatibility helper are
   absent; both removals and all old parent proof dependencies are now named.
   Existing public imports support the signatures; the new proof imports are
   private. Added the recorded proof-plan imports to the sole open theorem, as
   stage 2 section 3.7 requires. Read sk-prop-input-spreading.json: its realized
   entries are empty and are untouched; this below-unit repair keeps the trait
   argument and bypasses no realized unit step. Verdict: reduction and pruning
   are faithful; this remains a net-zero-hole decomposition.
5. Read all five delivered nodes against Lean and the existing node versions.
   Core and parent proof_deps follow their actual applications; the algebraic
   proof uses Mathlib only; the open theorem's two planned dependencies now have
   matching private imports. New records have source, proof, searches, creation,
   blueprint, chapter, unit and Lean fields. Verified the empty statement-change citer list against old DAG edges; the
   old parent DAG omitted its actual Lean use of the core, now corrected in its
   delivered proof_deps.
   Verdict: node records agree with the delivered route.

Second-reading changes: added two private proof-plan imports to EquivariantDescent;
made the change record's Old/New signatures verbatim; completed the explicit old
parent dependency names under No longer needed; verified the empty statement-change
citer list against the baseline DAG; appended this review. No mathematical statement, definition or proof
body was changed by the second reading.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent
Original against changed dependencies failed:
```
/tmp/forced-adaptation-cs0dnh_o/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:96:43: error: Application type mismatch: The argument
  K
has type
  Fin m → Subgroup G
of sort `Type u` but is expected to have type
  Etale
    (Opens.ι (PrimeSpectrum.basicOpen ((algebraMap (↑H) C) (ι g))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (↑H) C)))
of sort `Prop` in the application
  affine_torsor_fixed_orbits R H g ι C G ρ hρone hρmul hne p j hj m K
/tmp/forced-adaptation-cs0dnh_o/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:95:9: error: Tactic `rcases` failed: `x✝ : ?m.356` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-cs0dnh_o/.lbuild) [2.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier second reading (a previous round; superseded)

1. I compared every delivered existing module with the repository. Existing
   declarations keep their signatures and visibility; the core theorem's
   corrected existential interface is the declared change, and the parent edit
   is a forced proof adaptation. Verdict: statements are accounted for.
2. I compiled all five modules with `lcompile.py --all`. There is one named
   `sorry`, `affine_torsor_equivariant_descent`, with its node and proof
   docstring; no forbidden declarations or hollow definitions occur. Verdict:
   clean conditional proof.
3. I checked the new algebra and orbit-product statements on empty, singleton,
   and trivial actions. They are true and strictly smaller than the geometric
   target; the remaining descent theorem is the documented geometric hole.
   Verdict: split is justified.
4. I traced the core proof through geometric descent, orbit product, principal
   open transport, and `Over.w`. Removed imports and proof dependencies are
   listed above, and the unit route remains intact. Verdict: pruned route.
5. I checked all delivered node records against declarations and proof uses,
   including the change record and forced adaptation. Verdict: DAG agrees.

I added this required second-reading record only; no Lean statement or proof
body was changed during the review.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent
Original against changed dependencies failed:
```
/tmp/forced-adaptation-uqix6lg_/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:96:43: error: Application type mismatch: The argument
  K
has type
  Fin m → Subgroup G
of sort `Type u` but is expected to have type
  Etale
    (Opens.ι (PrimeSpectrum.basicOpen ((algebraMap (↑H) C) (ι g))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (↑H) C)))
of sort `Prop` in the application
  affine_torsor_fixed_orbits R H g ι C G ρ hρone hρmul hne p j hj m K
/tmp/forced-adaptation-uqix6lg_/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:95:9: error: Tactic `rcases` failed: `x✝ : ?m.356` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-uqix6lg_/.lbuild) [3.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by E3

1. Compared the delivered core and parent with the repository using `diff -u`.
   The core signature changes only as declared in
   `coord/changes/affine-torsor-fixed-orbits-actual-stabilizers.md`: arbitrary
   input orbit data become existential output data with the same bound. The
   preserved empty-orbit counterexample proves the former interface false.
   The parent signature, visibility and imports are unchanged; only its forced
   application changes. All other existing declaration signatures are unchanged.
   Verdict: documented statement repair; no silent weakening or target edit.
2. Compiled all five modules in import order with `lcompile.py --all`, cleanly.
   Independently compiled scratch copies with explicit `#print axioms` for all
   nine declarations, including private helpers. The construction, orbit
   product and counterexamples use only propext, Classical.choice and Quot.sound.
   The repaired core and parent additionally depend on sorryAx through the sole
   named geometric hole, affine_torsor_equivariant_descent. No forbidden
   declaration, proof hole in data, or arbitrary unproved witness definition
   occurs. Verdict: kernel-checked conditional reduction, not a completed
   geometric proof.
3. Read the geometric split theorem, its node and docstring, checking every
   hypothesis. Finite faithful flatness localizes to a surjective finite flat
   cover of D(iota(g)); the nonzero image in a domain makes its source nonempty
   and connected. Unique rotations on field points identify its torsor relation.
   A pulled-back splitting then gives a permutation descent action. In the
   localization calculation, choose one common denominator h^N for all d
   coordinates; because rho fixes h, equivariance says each numerator
   difference vanishes after localization, and injectivity forces that
   difference to vanish already in C. This yields the stated equivariant algebra
   puncture over H. Checked d=0, d=1, the trivial torsor and trivial component
   action. The algebraic orbit product is separately proved and strictly removes
   part of the original argument. Fresh LeanFinder, Loogle and grep searches
   with semilinear/permutation/subalgebra terminology found only ingredients.
   An initial Loogle query rejected the identifier Pi; the corrected query ran.
   Read TotallySplit.fixedPointsCoordFamilyEquiv and DescentDatum.descendedEquiv:
   the former has coordinate actions only, the latter requires the descent
   datum still to be constructed. Neither closes the remaining geometric hole
   in a few minutes. Checked the sources
   [03SF](https://stacks.math.columbia.edu/tag/03SF),
   [023R](https://stacks.math.columbia.edu/tag/023R), and
   [0245](https://stacks.math.columbia.edu/tag/0245).
   Verdict: true, documented geometric subproblem, not a relabelled fixed-ring
   product conclusion.
4. Traced the core through equivariant descent, evaluation at orbit
   representatives, Spec of the inverse algebra equivalence, restriction to
   the principal open and Over.w. No shorter existing route was found.
   The surviving public imports support signatures; new proof imports are
   private. The No longer needed section names both old core dependencies and
   both old parent dependencies, and explains the retained Galois-category
   input. Read the unit sk-prop-input-spreading: its realized entries are empty
   and unchanged; this repair keeps the trait route. Verdict: faithful
   decomposition and documented pruning; zero net holes closed by the
   one-for-one replacement, and no proof claimed for the false former type.
5. Read all five delivered node records and checked their proof dependency
   unions against their steps and the Lean applications. New nodes have
   sources, complete proof arguments, searches, creation, blueprint, chapter,
   unit and Lean records. Core and parent records match the new route; the
   recorded statement change and forced caller adaptation match the diffs.
   Verdict: DAG agrees with the delivery.

Second-reading changes: appended this independent review and recorded fresh
searches. No Lean proof, definition, statement, import or node was changed;
the previously repaired unused imports and self-contained descent statement
are correct. One former false hole is repaired and replaced by one smaller
geometric hole; the algebraic orbit-product theorem is fully proved.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent
Original against changed dependencies failed:
```
/tmp/forced-adaptation-9vpnk5ir/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:96:43: error: Application type mismatch: The argument
  K
has type
  Fin m → Subgroup G
of sort `Type u` but is expected to have type
  Etale
    (Opens.ι (PrimeSpectrum.basicOpen ((algebraMap (↑H) C) (ι g))) ≫ Spec.map (CommRingCat.ofHom (algebraMap (↑H) C)))
of sort `Prop` in the application
  affine_torsor_fixed_orbits R H g ι C G ρ hρone hρmul hne p j hj m K
/tmp/forced-adaptation-9vpnk5ir/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorFixedPunctureDescent.lean:95:9: error: Tactic `rcases` failed: `x✝ : ?m.356` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-9vpnk5ir/.lbuild) [2.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
