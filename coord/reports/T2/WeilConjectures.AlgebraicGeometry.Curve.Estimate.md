## What changed

Completed the two remaining proofs in
`WeilConjectures.AlgebraicGeometry.Curve.Estimate`, preserving every declaration signature
and the existing public imports. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Curve.Kummer`,
`WeilConjectures.AlgebraicGeometry.Sites.GmPicard`,
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`.

The proof follows the existing Kummer route of `thm-sc-proper-cohomology`, which realizes
unit `sk-thm-curveestimate`: choose a primitive root, identify the constant sheaf with
mu_n, apply Kummer in degrees one and two, then apply `Scheme.Hom.pic_proper_ntorsion`.
The genuine glue restricts the canonical Picard group equivalence to n-torsion and
proves that it carries the image of multiplication by n to the power-map image;
`QuotientAddGroup.congr` then identifies the quotients. Multiplicative Picard groups
are converted to additive groups only at these interfaces.

No new statements, nodes, or definition changes. The existing DAG route is unchanged.
There is no node with `lean.module` equal to this upstream module in this checkout;
the docstrings name `sk-thm-curveestimate`, whose realized statement is
`thm-sc-proper-cohomology`. Its existing four-step Kummer plan is implemented here in
degrees one and two, so no route update is needed.

Searches: LeanFinder for the etale curve computation returned unrelated function-field,
elliptic-curve, and group-cohomology results. Loogle for
`AddEquiv, AddSubgroup.torsionBy` returned no matches. Local rg found the existing
Kummer identifications, `pic_proper_ntorsion`, the canonical group equivalence in
GmPicard, and Mathlib's quotient congruence. No shorter mathematical route was found.

## Proved and sorry left

Proved both formerly sorry declarations:
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`.
- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`.

No sorry remains in the item, and none is added elsewhere. Degree zero was already
proved and is unchanged. This is a stage-3 reduction to existing named declarations,
not a claim that the transitive axiom closure is now sorry-free:
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion` remains sorry in the existing
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion` module
(node `lem-sc-pic-proper-ntorsion`). Its Jacobian and abelian-variety dependencies
remain the intended downstream work.

Edge cases: `hn` excludes n = 0; n = 1 is included without any extra hypothesis, and
all equivalence constructions work for trivial torsion and quotient groups. No genus
positivity is assumed, so genus zero is included. The dimension-one hypothesis is
preserved through `IsConnectedCurve`, excluding Spec k in degree two.

Local compilation passes without warnings. The delivery dry run supplies the final
server compile and preflight checks.

## No longer needed

Removed the first worker's redundant proof import
`Mathlib.Algebra.Group.TypeTags.Basic`; its declarations are already available through
the retained imports. No original imports removed, and no DAG nodes or modules pruned.
All three retained added proof imports are used. The Jacobian, Picard decomposition, genus comparison, and abelian-variety
estimate are retained through `lem-sc-pic-proper-ntorsion`, as required by the unit's
route; no direct imports of those downstream modules are needed in this item.

## Where the brief, the DAG or earlier work was wrong

The requested exact `lean.module` search returns no node for this adopted upstream
module. The unit record and the already proved wrapper
`Sheaf.AlgebraicGeometry.Curve.ProperCohomology` identify its place in the existing
DAG. No mathematical statement fault was found. The cohomological Picard group is
additive while the geometric Picard group is multiplicative; the proof includes the
needed subgroup and quotient transport rather than assuming the types coincide.


## Second reading by T2

1. Compared the entire delivered module against the repository using `diff -u`.
   The only original Lean changes are the degree-one and degree-two proof bodies;
   all three existing theorem signatures, universes, instance hypotheses, namespace,
   definitions, public imports, and docstrings are unchanged. No change record is needed.
2. Compiled the complete delivered file locally without errors or warnings. Searched
   the delivered Lean for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   `extern`, and kernel-check bypasses: none occurs. A scratch copy with `#print axioms`
   for all three declarations reports only `propext`, `Classical.choice`, and
   `Quot.sound` in degree zero; degrees one and two additionally report `sorryAx`
   from existing open dependencies, including `Scheme.Hom.pic_proper_ntorsion`.
   The local torsion equivalence maps exactly n-annihilated elements to the
   power-map kernel, with both inverses and additivity checked by Lean. The quotient
   equivalence proves equality of the transported multiplication image and the
   power-map image in both directions before using `QuotientAddGroup.congr`.
3. No statements are split off, and no new declarations or nodes are introduced.
   Checked the unchanged hypotheses: `hn` excludes zero; n = 1 and genus zero
   require no additional hypotheses. The torsion and image transports are general
   group identities, so these edge cases are included. Independently searched local
   Mathlib and both library roots for torsion equivalences and power-map kernel
   equivalences; Loogle query `AddEquiv, AddSubgroup, Additive` returned no hits.
   Existing Kummer, GmPicard, and PicProperNTorsion declarations supply the needed
   mathematics; no duplicate lemma is proposed.
4. Read Curve.Kummer, Sites.GmPicard, PicProperNTorsion, ProperCohomology, and
   `dag/units/sk-thm-curveestimate.json`. Primitive-root trivialization, the Kummer
   identifications, and Picard torsion/cokernel computation are retained; the
   wrapper retains degree zero and higher vanishing. Its unit realization remains
   `thm-sc-proper-cohomology`. No shorter mathematical route preserving that route
   was found. Removed the redundant added TypeTags.Basic proof import after a
   scratch compilation without it passed. The three remaining added imports supply
   the Kummer computations, canonical additive Picard equivalence, and Picard
   torsion/cokernel theorem respectively. No old proof dependency is pruned.
5. Read `thm-sc-proper-cohomology.json` and the PicProperNTorsion statement and
   node. There is no DAG node assigned directly to this adopted upstream module;
   ProperCohomology is the recorded realization and imports this module. Its four
   proof steps, proof dependencies, and document origin still describe the route
   implemented across the wrapper and this module, so no node edits are required.

Verdict: the reduction is valid with unchanged statements. Second reading changed
only the redundant added proof import and this report; no proof repair was needed.
