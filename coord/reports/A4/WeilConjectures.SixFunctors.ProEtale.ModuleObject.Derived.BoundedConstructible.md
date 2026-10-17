## What changed

Repaired the return at head `1de5b4ee2` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
The internal-Hom `STATEMENT-DISPUTED` comment now precedes both monoidal instances.
The hole scanner includes comments before the next declaration in the preceding
instance's scanned body. Its position between the instances caused the rejection
of `isMonoidal_boundedConstructible`, whose actual `:= sorry` body had not changed.
Both instances' signatures and complete scanned bodies now equal the current shared
source exactly. Running the existing supplementary hole gate on the shared source
and repaired sandbox source returns no failures. No tool was modified.

Retained the two completed preservation proofs from the returned delivery. Pullback
uses `leftDerivedUpperStarIsoMapDerivedCategory`, exact-functor preservation of
boundedness, `mapDerivedCategoryHomologyFunctorIso`, and
`isConstructibleModuleObject_upperStar`. Extension by zero uses its exact-functor
boundedness and homology comparisons and
`isConstructibleModuleObject_openImmersionLowerShriek`. Local noetherianity follows
from the finite-type hypothesis over the field. The two proof-only imports are
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback` and
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero`.

The local irreducibility attributes now apply from the start of the public
section to `DerivedCategory.monoidalClosed`, `CategoryTheory.Mod.monoidalClosed`,
and `AlgebraicGeometry.ProEtale.upperStarFromPoint`. This also prevents expansion
of the underlying module internal Hom and coefficient inverse-image constructions.
The change record is
`coord/changes/A4-bounded-constructible-local-closed-transparency.md`.
There are no changed public signatures, public imports, definitions, consumers,
new nodes, or new holes. The current blueprint's unit route remains unchanged.

Validation: the existing hole scanner confirms that the only remaining holes are
the three declarations listed below, and that both holed instance bodies are
unchanged. The complete module compiled on the server in 53.2 seconds using the standard
`lcompile.py` command and the unchanged 60-second limit. The required
`deliver3.py A4 WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
--no-push` dry run printed OK at commit `f47cc496c4`: compilation, the axiom
probe and preflight passed except for the independent second reading, which the
next reader supplies. Nothing was pushed.

## Proved and sorry left

Closed 2 of the 5 original holes; added 0 holes and split off 0 theorems:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_obj`;
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_openImmersionLowerShriek_obj`.

The three original holes remain unchanged:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`.

Their existing blueprint parent is `sk-def-sfb-dc-restricted-functors`. The current
blueprint preservation nodes are `lem-sfb-dc-lower-star-preserves`,
`lem-sfb-dc-tensor-preserves`, and `lem-sfb-dc-hom-preserves`. These three unrestricted
upstream statements remain disputed; no coefficient-specific theorem is claimed
as a proof of them.

## No longer needed

No imports, DAG nodes, or library modules are pruned. Both added proof imports
are used. The returned delivery's earlier redundant private helper
`boundedConstructible_of_iso` remains removed; the current proofs use the existing
boundedness, homology and constructibility transport APIs directly.

## Where the brief, the DAG or earlier work was wrong

The latest hollow-data rejection was triggered by the placement of a comment,
not by a newly introduced or modified instance proof. Moving the comment before
both instances preserves the mathematical warning and leaves the complete
scanned bodies identical to the baseline. This repairs the source submitted to
the gate without changing the gate or hiding any hole.

The unrestricted pushforward assertion is false for arbitrary condensed
coefficients: for the affine line over an algebraically closed field of
characteristic p and the constant coefficient F_p, Artin-Schreier cohomology
has infinite-dimensional H¹, so pushforward is not constructible. The hypotheses
constrain ℓ without relating it to Λ.

The two unrestricted monoidal assertions fail for constant discrete Λ = Z/4
on a geometric point and the finitely presented module Z/2. The periodic free
resolution has nonzero Tor and Ext in every nonnegative degree, making both
derived self-tensor and internal Hom unbounded. The two dispute comments now
appear together before the monoidal instances; the pushforward comment remains
before its declaration. The current blueprint restricts these claims to suitable
coefficient rings. Their signatures and original holes are retained.

## Second reading by A4

1. Compared the delivered module with the shared repository. Existing declaration signatures and
   bodies are unchanged except for the two completed proofs; the two proof-only imports, local
   transparency attributes, and disputed comments are the declared changes. Verdict: pass.
2. Compiled the complete module with `lcompile.py` (50.0 seconds, exit code 0). The only remaining
   `sorry`s are the three named declarations above; there are no hollow definitions, forbidden
   declarations, or newly introduced holes. Verdict: pass.
3. Checked the two completed arguments against their hypotheses and the imported preservation,
   boundedness, homology, and constructibility transport lemmas. The disputed comments give valid
   edge-case counterexamples and retain the original statements. Verdict: pass.
4. The proofs use the shortest available imported APIs. Both added imports are used, and no
   existing import or DAG dependency is removable. The unit's realized route and all public
   signatures remain unchanged. Verdict: pass.
5. Checked the proof dependencies against the Lean terms and reviewed the change record for the
   local attributes. No DAG node or proof dependency update is needed; the declared local change
   is limited to elaboration transparency. Verdict: pass.

No further changes were needed in the second reading.
