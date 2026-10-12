## What changed

Proved `AlgebraicGeometry.IsConnectedCurve.proper_pic_torsion_baseChange_bijective`
with its statement unchanged. Constructed the torsion pullback map directly from
`Scheme.Pic.mapHom`. The Picard decomposition proves that torsion classes have degree
zero; degree invariance constructs the subgroup pullback homomorphism; the existing
`picZero_torsion_base_change` supplies injectivity and torsion lifting. The proof then
assembles the bijection and its canonical-value equation explicitly.

Added a proof-only import of `Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange`.
The degree lemmas are already available through the retained public imports; the second
reader removed the redundant direct proof-only EulerChar import. Updated the item's node
proof, proof dependencies and proof origin to match this route. No statements,
definitions, public imports, or other modules changed.

## Proved and sorry left

Closed the one hole:
`AlgebraicGeometry.IsConnectedCurve.proper_pic_torsion_baseChange_bijective`
(node `lem-sc-proper-pic-torsion-base-change`). No holes remain in the delivered module;
no holes added or split off. The proof uses the existing, still unproved declaration
`AlgebraicGeometry.picZero_torsion_base_change`
(node `lem-sc-piczero-torsion-base-change`); its hole is not duplicated or moved.

## No longer needed

Removed direct proof-only imports:
- `Sheaf.AlgebraicGeometry.GenusInvariant` (`lem-sc-genus-invariant`);
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
  (`lem-sc-proper-dim-one-projective`);
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`
  (`thm-sc-jacobian-representability`);
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Final` (`thm-av-final`).

The degree-zero comparison encapsulates Jacobian representability and finite etale
torsion invariance. Those results remain indirect dependencies of that existing lemma;
this delivery does not claim they leave the targets' import closure. ProperProjective
is not needed on this route. Retained BaseChangeCurve and PicardDecomposition.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the Jacobian torsion comparison already stated as
`picZero_torsion_base_change`. Reusing it avoids duplicating the representing-functor
and torsion-scheme glue. Degree preservation is needed to define the subgroup map
and is recorded explicitly as `lem-pc-degree-base-change`, an existing tool from the
Picard Riemann-Roch unit. The unit route remains the degree-zero Jacobian comparison.

Edge cases: n=1 gives the identity singleton by the same argument; genus zero
requires no separate assumptions or choices. The proof uses NeZero n exactly to
cancel the positive integer n in the integer degree coordinate, and uses nonzero n
in k for the existing torsion comparison. No arbitrary data is selected from an
unproved existence theorem: F is the explicit Picard pullback with a power proof.

Local cache initially lacked the compiled PicZeroTorsionBaseChange module despite
its source and DAG record being present. The glue was first checked with temporary local proof holes. Then an unchanged
sandbox copy of the existing dependency was compiled with lcompile.py, followed by
the full item, against the available green imports. Both compiled without errors
or warnings. The unchanged dependency source is not delivered; no duplicate
declaration, changed dependency, or temporary proof hole is included.


## Second reading by W3

1. Compared the entire delivered module and node against the repository with `diff`.
   The existing theorem signature is byte for byte unchanged, including both algebraically
   closed fields, the field algebra, connectedness, smoothness, properness, `NeZero n`,
   nonvanishing in k, bijectivity, and the canonical pullback-value equation. Public imports,
   docstrings, and all definition data are unchanged. No change record is required. Verdict: pass.
2. Compiled the module locally without errors or warnings. An independent scratch copy with
   `#print axioms AlgebraicGeometry.IsConnectedCurve.proper_pic_torsion_baseChange_bijective`
   reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last comes
   from existing open dependencies, including `picZero_torsion_base_change`; this is a
   reduction of the upper hole, not an unconditional completed target. No forbidden
   declaration, new sorry, or holed definition occurs in the delivered module. `F` is
   constructed as Picard pullback; the subgroup/equivalence witnesses come from the already
   proved `exists_mulEquiv_prod_picZero`. Verdict: pass.
3. No statements or nodes were split off, so there are no new holes, existence choices,
   duplicate lemmas, or new edge cases to approve. Checked the existing comparison's
   hypotheses against its application: the subgroup equalities are supplied by decomposition,
   and `j` has the exact pullback-value equation. For n=1 both torsion subtypes contain only
   the identity; genus zero requires no extra hypothesis; n=0 is excluded by the unchanged
   hypotheses. Verdict: pass.
4. Read the degree-zero comparison, the proved Picard decomposition, the degree-base-change
   declarations, and `dag/units/sk-prop-ext-invariance.json`. The proof follows the unit's
   proper degree-one Jacobian torsion route through the existing comparison; the unit's
   `realized` entries are empty and unchanged. Searched lean/ for torsion/base-change and
   Picard degree facts, and used msearch grep with
   `Pic.mapHom|picDegree.*pullback|torsion.*picZero`: no shorter matching theorem was found.
   Every removed old proof dependency is listed under No longer needed. EulerChar is already
   visible through retained imports; a scratch compile without its direct import passed,
   so I removed that redundant import. The degree-base-change node remains a genuine proof
   dependency even without this direct import. Verdict: pass after import pruning.
5. Checked each node step against the Lean: baseChange_curve supplies the curve instance;
   decomposition gives torsion degree zero by cancellation in Z; degree_congr and
   degree_pullback justify the subgroup map; picZero_torsion_base_change supplies injectivity
   and torsion lifting; subtype extensionality assembles the bijection. The node's proof_deps
   are exactly the four mathematical nodes used, and proof_origin describes this route.
   Only proof, proof_deps, and proof_origin changed in the node. Verdict: pass.

Second-reading changes: removed the redundant proof-only import of
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`; corrected the import description
above and appended this review. No proof or statement repair was needed.
