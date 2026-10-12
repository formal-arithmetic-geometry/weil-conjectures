## What changed

Reduced `AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_spec_ring_colimit`
following step 9 of `lem-weil-pbc-etale-cohomology-limit-of-schemes`. Its proof is complete
and contains no `sorry`, relative to the existing general continuity theorem and one new
sheaf-coherence lemma. No existing signature or definition changed.

The proof maps the opposite ring-colimit cocone through `Scheme.Spec` and uses preservation
of limits. Affine stages provide compactness, quasi-separatedness and affine transitions
by instances. A proved private lemma `continuity_constant_pullback` constructs the stage
pullbacks and their canonical transition maps. It obtains their identity, cocycle and
constant-diagram compatibility laws from `compatiblePullbackSheafSystem`. The diagram
on the limit is constant, so `isColimitConstCocone` supplies its colimit: the directed
nonempty index is connected. The general continuity theorem then applies. The resulting
cohomology cocone legs agree with the supplied legs after removing composition with an
identity. This establishes the supplied cocone's universal property, including its maps.

Added the proof imports `Sheaf.AlgebraicGeometry.CompatiblePullbackSheafSystem`,
`Mathlib.CategoryTheory.Limits.Connected`, and `Mathlib.CategoryTheory.Filtered.Connected`.
The new module imports the existing pullback coherence module for its proof plan.
The parent node's ninth step and proof dependencies now record the new lemma. Its first
eight steps remain the plan for the unresolved general theorem. The unit route is unchanged.

Local compilation of both modules succeeded without warnings (new module 2.6 seconds,
item module 46.8 seconds). The required delivery dry run supplies the final checks.

## Proved and sorry left

Reduced, with complete Lean glue and unchanged statement:
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_spec_ring_colimit`.
The private helper `AlgebraicGeometry.Etale.continuity_constant_pullback` is also proved.

One original `sorry` remains unchanged:
`AlgebraicGeometry.Etale.nonempty_isColimit_etale_cohomology_of_isLimit`, node
`lem-weil-pbc-etale-cohomology-limit-of-schemes`.

One new `sorry` is split off:
`AlgebraicGeometry.Etale.compatiblePullbackSheafSystem`, node
`lem-weil-pbc-compatible-pullback-sheaf-system`. It concerns only inverse-image identity,
composition, and comparison laws for sheaves on an arbitrary cone. It has no cohomology,
colimit universal property, compactness, or limit assumption. Thus it is strictly the
sheaf-system construction part of step 9, not a renamed continuity statement.

This closes one of the module's two original unfinished proofs. It does not claim to
close the transitive axioms of continuity.

## No longer needed

None established. The general continuity theorem is still needed, and its original
affine-site and Mayer-Vietoris dependencies remain its unfinished proof plan. No existing
import was removed, and no node or module is claimed pruned. The ring specialization needs
no new cohomology functoriality or Mayer-Vietoris argument beyond that general theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The new lemma is the sheaf-system construction that
step 9 describes in words; its explicit identity, cocycle and comparison equations were
not already a single stated declaration. Source searches found the component laws in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` and the inverse-image-composition
node. Attempts to assemble those laws directly passed isolated categorical checks but
encountered expensive conversion of the dependent sheaf-diagram data in the whole proof.
The assembly is left as the named new lemma with a complete proof in words. Its successor
should use the existing unit and associativity laws, with careful control of equality
transport and local definitions.

Searches for continuity found only global-section continuity in Mathlib and a vanishing
consequence in the source library. Searches for the new sheaf-system lemma: LeanSearch
was unavailable (HTTP Internal Server Error); LeanFinder returned general topological and
module-sheaf pullback comparisons, not this scheme-diagram statement; logged grep found
no `upperStarComp` or `upperStarId` in Mathlib's CategoryTheory sources. Local source grep
and blueprint search found no duplicate assembled statement. The existing inverse-image
composition node remains the proof dependency of the new lemma.

Edge cases: the new lemma allows the empty preordered index (all three equations are
vacuous), an arbitrary cone rather than a limiting one, and the zero sheaf. No directedness
or antisymmetry is needed for its coherence laws. In the ring specialization the existing
nonempty/directed assumptions give connectedness; no initial stage is chosen. The zero
ring, empty spectra and degree zero are included without additional hypotheses.

## New nodes

`lem-weil-pbc-compatible-pullback-sheaf-system`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-compatible-pullback-sheaf-system.json`,
is stated in `lean/Sheaf/AlgebraicGeometry/CompatiblePullbackSheafSystem.lean`. It assembles
the identity and associativity comparisons of inverse image into the canonical stage
sheaf system and identifies its pullbacks on the cone with a constant diagram. Its source
is Stacks Sites Tag 03CB and the compatible inverse-image construction preceding Etale
Cohomology Tag 09YQ, as used in the parent's ninth step. The docstring and node give the
three equations and their proof. No change record is needed: no existing statement or
definition is changed.

## Second reading by M1

1. Compared the delivered modules with the repository versions. Existing theorem signatures and definitions are unchanged; the only additions are the private helper, its split-off theorem module, proof-only imports, and corresponding DAG updates. Verdict: pass.
2. Compiled `CompatiblePullbackSheafSystem.lean` and `EtaleCohomologyLimitOfSchemes.lean` with `lcompile.py`; both compile without errors or warnings. The item theorem has no `sorry`; the two documented open theorems are the general continuity theorem and the new sheaf-system lemma. Verdict: pass.
3. Checked the split-off statement and node against the Lean declaration. It is a strict coherence component of the planned ring reduction, with the source and proof description recorded; it is not a restatement of the target. Verdict: pass.
4. Read the proof route and imports. The ring specialization uses the general continuity theorem, the sheaf-system coherence lemma, the Spec limit preservation, and connected constant-cocone result. The unit route remains intact; no import was identified as safely removable because the parent theorem's unresolved proof still uses the listed plan dependencies. Verdict: pass.
5. Checked the parent and new DAG records, including proof steps, dependencies, origin, unit, and realized route. The parent records the ninth-step reduction and the new node records the three coherence equations. Verdict: pass.

Changed only this report during second reading; no Lean or DAG repair was necessary.
