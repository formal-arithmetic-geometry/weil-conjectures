## What changed

Proved the body of `AlgebraicGeometry.finiteDimensional_etaleCohomology_one_of_scalar_model`
without changing its statement. Added the proof-only import
`Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison`, and the existing
`DirectImage.AffineMorphism` and `Affine.Cech` modules.

The proof makes the additive comparison linear using the two scalar identities in the
hypothesis. In the proper branch it establishes coherence of the unit module, uses
`Scheme.Modules.finiteDimensional_H_of_isProper`, and transports finiteness along that
injective linear map. In the affine branch ordinary quasi-coherent vanishing gives a
subsingleton codomain, hence source; this proves finiteness for the given action.

The new comparison is independent of properness and finiteness. Its missing proof covers
section-sheaf identification, natural derived/Ext and coefficient comparisons, and scalar
naturality. The full finite-cover proof is in its docstring and node. The source read was
[Stacks 03P2](https://stacks.math.columbia.edu/tag/03P2), especially its separated-case proof,
and [Stacks 03FD](https://stacks.math.columbia.edu/tag/03FD).

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.finiteDimensional_etaleCohomology_one_of_scalar_model`
(node `lem-sc-additive-cohomology-finite-dimensional`). The item's module contains no sorry.

Added one hole:
`AlgebraicGeometry.exists_addEquiv_etaleCohomology_one_structureSheaf`
(node `lem-sc-additive-cohomology-scalar-comparison`) in its own new module.
This is a decomposition, not an unconditional proof: one hole closed, one added, net zero.
The final assembly is a complete Lean proof. The new statement has no finite-dimensional
conclusion or properness hypothesis and is strictly the comparison part of the argument.
Both modules compile locally without warnings.

## No longer needed

Removed direct proof imports from the item's module:
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`;
- `Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`;
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`;
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`.

The first two are used below the new comparison. `FiniteFreeComplex` is still imported
transitively by the proper-cohomology wrapper; `PlusSingle` remains below the existing
natural Ext/derived comparison. Consequently no entire dependency module is claimed pruned.
The parent's direct dependencies `lem-sc-etale-affine-qcoherent`,
`lem-sc-etale-zariski-qcoh-comparison`, and `lem-sp-derived-functor-single-identification`
move below the comparison; their mathematics is still needed. No unit statement or step is
bypassed. The parent now also cites existing `lem-pc-affine-vanishing`.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing coefficient-lift comparison
`nonempty_etaleTensorSectionsSheaf_cohomology_ulift` provides only an additive equivalence;
its signature does not assert naturality. An arbitrary additive equivalence cannot justify
scalar compatibility. The new hole explicitly requires one equivalence compatible with all
scalar maps, and its proof constructs that equivalence from the same finite affine open
cover. The finite affine open cover argument of 03P2 suffices here, so general finite affine
etale hypercovers from the original prose are not needed. The ordinary H model and the
ringed-space module-derived model are different encodings; the natural module/abelian
comparison and Ext-universe reindexing must be included.

Edge cases checked mathematically: affine curves have zero H^1 on both sides; proper
positive-genus curves allow nonzero H^1, so comparison alone does not assume vanishing;
zero cohomology has its unique module structure; arbitrary characteristic is permitted,
and no Frobenius or positive-characteristic hypothesis occurs. `IsCurve f` entails a finite
affine open cover and absolute separatedness, as required by the comparison proof.

## New nodes

`lem-sc-additive-cohomology-scalar-comparison` is the natural, scalar-compatible additive
comparison between larger-coefficient derived etale H^1 and canonical structure-sheaf H^1.
Its module is `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison`. It adds one named
public theorem with sorry, source and a complete proof in words. No definitions or existing
signatures change, so no change record or downstream adaptations are required.

## Second reading by R1

1. Compared both delivered modules against the repository: the existing theorem's
signature and docstring are byte-for-byte unchanged. The only existing Lean changes
are its proof and private proof imports. The comparison module is new; no definitions,
targets or externally visible imports of the existing module change. No change record
is needed. Verdict: pass.

2. Compiled both modules in import order with lcompile.py: no errors or warnings.
A scratch copy with #print axioms for both declarations showed exactly propext,
Classical.choice, Quot.sound and sorryAx. There is no forbidden declaration or hollow
definition; the sole new sorry is the named comparison theorem, listed above with its
node. The parent still depends on that hole and open upstream results. Verdict: pass.

3. Read Stacks 03P2 (59.22.4), especially its separated-case affine-open Cech argument,
and 03FD (21.12.4). Matched the field, IsCurve, natural section equivalences and scalar
formula to the comparison statement. IsCurve extends separatedness, finite type and
quasi-compactness; the field base is absolutely separated, so the finite affine cover
has affine intersections. The same finite cover works in both coefficient universes,
and componentwise lowering commutes with scalar multiplication and differentials.
The source library moduleH is induced by smulHom; moduleHOfField restricts it along
f.appTop and GammaSpecIso, exactly the displayed rho. Thus scalar compatibility is
needed, true, and strictly a comparison result: it assumes neither properness nor
finite-dimensionality. Tested empty and zero-dimensional curves (allowed by IsCurve),
affine curves, and proper positive-genus curves: the former have zero H1, while the
last may have nonzero H1; none contradicts the statement. No arbitrary witness is
stored in a definition: e is eliminated locally inside a proof.
Independent leanfinder search for natural scalar-compatible universe-change cohomology
returned HomComplex scalar lemmas, not this comparison; loogle Sheaf.H.map returned no
match. Searched lean/ with scalar/naturality and cohomology/universe-lift alternatives,
and read EtaleQcoherentCohomologyULift, EtaleZariskiQcohComparison,
ZariskiModuleAbelianCohomologyAgree and EtaleSheafHExtDerivedComparison. The existing
lift theorem supplies only Nonempty of an additive equivalence, so its statement
cannot supply the missing scalar naturality. This hole cannot be closed in a few
minutes from those interfaces. Verdict: pass as a decomposition, not a net proof.

4. Read the proof top down. The proper branch applies finiteDimensional_H_of_isProper
to the quasi-coherent finite-presentation unit module, then of_injective to the
linear map assembled from the scalar identities. The affine branch uses ordinary
quasi-coherent H1 vanishing and the additive equivalence's injectivity; no scalar
assumption is needed there. No shorter existing comparison was found. The added
imports are proof-only. The removed imports and all old proof dependencies absent
from the new parent's proof_deps are listed under No longer needed; coherent-hi and
proper-or-affine remain. No whole module is claimed pruned. Read sk-prop-cd.json:
its realized slots are currently empty and this subordinate additive comparison
preserves the Artin-Schreier/quasi-coherent route of its final step. Verdict: pass.

5. Compared the parent node diff: only proof, proof_deps and proof_origin change.
Its two steps accurately record the linear comparison and proper/affine assembly.
The new node has the required source, complete proof steps, dependency union,
search records, creation metadata, blueprint ancestry, chapter/unit, and verbatim
Lean statement. Read the natural comparison and affine-acyclicity declarations:
they give the component facts claimed, without falsely using the non-natural lift
existence theorem for naturality. The named comparison's docstring explicitly
includes the coefficient and Ext-model bridges. Verdict: pass.

Changes made by second reading: appended this review and recorded independent
searches; no Lean proof, statement, import or DAG repair was necessary.
