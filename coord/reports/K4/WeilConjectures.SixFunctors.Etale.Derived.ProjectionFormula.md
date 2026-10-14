## What changed

Proved `AlgebraicGeometry.Etale.hasProjectionFormula_id` without changing its statement or
any definition. The proof uses the chosen compactification `c` of the identity. Its open
immersion `c.i` is also closed. The existing derived comparison `D(c.i)_! ≅ R(c.i)_*`
identifies the supported image. The open-immersion projection isomorphism places
`R(c.i)_* K ⊗ L` in the essential image of the fully faithful `R(c.i)_*`, so the explicit
unit formula for the right-adjoint projection map proves the projection formula for `c.i`.
The identity pullback is an equivalence, hence its projection map is invertible. The
proved composition law for `c.i ≫ c.g = 𝟙 X` then proves the projection component of `c.g`
at `R(c.i)_* K`. Naturality transports this to `D(c.i)_! K`. The remaining factors of the
compactification projection map are isomorphisms.

Added two plain proof imports: `Etale.Derived.LowerShriekToLowerStar` and
`Etale.Derived.LowerStarProjectionComp` (under `WeilConjectures.SixFunctors`). Every public
import and existing declaration signature is unchanged. The finite theorem's proof is
identical to the current repository version. Updated only `proof`, `proof_deps`, and
`proof_origin` of `lem-etale-proper-projection-formula-finite` to describe its actual
existing objectwise assembly.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Etale.hasProjectionFormula_id`, the only direct hole in
the repository's item module (1 of 1). Holes added: none. No direct `sorry` remains in the
item or in any new delivered module; no new module is delivered.

`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite` was already
proved on the baseline and is not counted as newly proved. Both this theorem and the new
identity proof still depend transitively on existing open library statements. In
particular, the identity proof uses the existing
`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar` in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`, whose clopen-comparison
proof remains open upstream. Its data is the explicit comparison construction, not a
witness selected from an arbitrary existence theorem. The derived tensor infrastructure
also remains open. Axiom checks of the identity and finite theorems print exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; this delivery does not claim
that the targets' transitive proof closure is complete.

The provisional `isIso_rightDerivedLowerStarProjectionMap_of_identity_support` theorem,
its module, and its new node were removed before delivery. Thus this is one local hole
closed using existing dependencies, not a decomposition introducing another hole.

## No longer needed

No repository import was removed and no repository module is claimed pruned.
The provisional `IdentityProjectionFormulaSupport` import/module/node is not delivered.
The first worker's added `EtaleInverseImageModulesExact` import is redundant and was
removed, consistent with the landed `projection-formula-imports.md` change record.
The trial `Etale.UpperLowerStar.Coherence` proof import was also redundant and removed.

The old direct proof dependencies `lem-kun-0f0g` and
`prop-weil-pbc-inverse-image-modules-exact` of
`lem-etale-proper-projection-formula-finite` are replaced by
`lem-etale-proper-projection-formula-finite-objectwise`: the parent theorem applies the
existing assembly theorem, whose components carry those geometric dependencies.
They remain indirect dependencies of that objectwise node; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier report incorrectly counted the finite theorem as newly proved relative to
the present repository and called the identity theorem still sorry even though its body
had been replaced. More seriously, its support theorem moved essentially the remaining
identity projection obligation to a new hole. Its proof sketch claimed that an adjunction
hom-equivalence reflects isomorphisms, which is false in general. The repaired proof uses
an explicit essential-image isomorphism to obtain an invertible unit and then uses the
composition formula and cancellation of actual isomorphisms.

The finite node still described a direct torsion-ring specialization, while its current
Lean body applies `finite_projection_iso`. Its proof metadata now records that assembly;
its statement, source, unit, and Lean attachment are unchanged.

## Second reading by K4

1. Compared the delivered module against the repository with `diff` and the stage-3
   declaration parser: identical declaration sets and byte-identical statements; the
   identity theorem is the sole changed body. Compared the elaborated `#check @...`
   output for the identity theorem in scratch copies of both versions: identical,
   including coefficient hypotheses and universes. No definition, public import, or
   declaration visibility changed. Verdict: preserved interface.

2. Compiled the final proof locally through `lcompile.py`, without errors or warnings
   (about seven seconds). Searched the delivered code for direct holes and forbidden
   constructs; none remain. Explicit `#print axioms` checks of the identity and finite
   declarations use only the three allowed axioms and existing `sorryAx`. The delivery
   tool additionally probes every delivered declaration. Verdict: valid local proof,
   with the pre-existing dependency holes disclosed above.

3. Read the provisional support statement and its node. Its transpose argument lacked
   the hypotheses needed to infer invertibility, and the split was too close to the
   parent obligation. Searched the library by clopen comparison, projection composition,
   and identity pullback, and ran different Loogle, LeanFinder, and Mathlib grep searches
   via `msearch.py`. The existing clopen comparison, open-immersion projection iso, and
   composition theorem give the reduction now written. No split statement remains.
   Checked the argument on the trivial identity compactification, an identity
   compactification with extra disjoint components, the empty scheme, and zero tensor
   factors: only equivalences, clopen support, and isomorphism cancellation are used.
   No finite-coefficient, boundedness, or dualizability assumption was inserted.
   Verdict: no new unresolved statement.

4. Read `dag/units/sk-prop-sf-pf-coherence.json` and its identity/mate proof step.
   The repaired proof follows that identity-adjunction and composition route. Its
   intermediate clopen support argument is below the unit level. The unit's `realized`
   record is unchanged (empty in the baseline), and no protected unit import is removed.
   Removed redundant trial imports; the two added proof imports provide respectively
   the clopen comparison and the composition/naturality formulas. Verdict: route kept.

5. Checked both provisional node files against the Lean. Removed the identity-support
   node together with its withdrawn declaration. Retained the finite node's legitimate
   proof-route correction while preserving all other fields: its only step cites the
   existing objectwise node, and `proof_deps` is exactly that step's `uses` union.
   The new identity proof is the identity clause of the existing coherence unit, not a
   claim to prove the full multi-clause coherence node. Verdict: delivered metadata
   describes the actual proof; no new node or change record is needed.

Second reading changed the unsupported identity split into a complete local proof using
existing library statements, removed its module/node and redundant imports, restored the
already-landed finite proof verbatim, corrected finite proof metadata, and rewrote the
progress report against the current baseline.
