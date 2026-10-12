## What changed

Replaced the proposed generic proper-torsion base-change reduction with the prescribed
curve-calculation route. The existing declaration
`AlgebraicGeometry.IsCurve.proper_constant_base_change_one` retains its full signature and
all public imports. Its proof splits on `(r : k) = 0`.

For `(r : k) ≠ 0`, the proof directly establishes annihilation of the constant module
sheaf, applies prime-injective cohomology comparison with the existing algebraically
closed extension section and injective-acyclicity lemmas, then transports from the
standard pullback to the supplied square. These are proof-only imports.

In characteristic r, the new module
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel` isolates the identification
of the degree-one comparison with the coordinatewise map on Frobenius fixed points.
The target applies the already proved
`LinearMap.Frobenius.bijective_tmul_fixedPoints`, applies bijectivity of mapRange
to finitely supported families, and transports injectivity and surjectivity. This keeps
sk-thm-p1 step (i), C7, and its Artin--Schreier calculation. No general proper-base-change
theorem is used. The new module imports publicly only what its signature uses; every
new import of the existing target is plain `import`.

Removed the proposed, unlanded generic torsion theorem and its node, and removed the
unnecessary file-wide unused-section-variable suppression and associated change record.
No existing definition, statement, public visibility or target interface changes.

## Proved and sorry left

Closed the direct hole of
`AlgebraicGeometry.IsCurve.proper_constant_base_change_one`
(node `lemma-weil-pbc-smooth-curve-proper-base-change-one`). Its proof contains no sorry.

Added one named theorem hole:
`AlgebraicGeometry.IsCurve.exists_constantModSheaf_one_frobenius_baseChange_model`
(node `lem-sc-artin-schreier-base-change-model`). Its entire proof is `by sorry`.
The statement identifies the Artin--Schreier/coherent-base-change model, without asserting
bijectivity of the map on fixed points. Its docstring explains the remaining argument,
including arbitrary coefficient rings and the dimension-zero case.

This is a decomposition: one upper hole closed, one lower hole added, net zero direct
holes closed. The target still depends on sorryAx through this new theorem and possibly
through existing imported lemmas; it is not an axiom-free completed proof. The rejected
generic theorem does not belong to this delivery. No data definitions were added, and
no object is chosen from an unproved existence assertion in a public definition.

## No longer needed

No repository imports or old proof dependency nodes are pruned: the old node's
proof_deps was empty. Pruned modules: none.

The proposed `Sheaf.AlgebraicGeometry.Etale.ProperTorsionCohomologyBaseChange` and its
`lemma-proper-torsion-cohomology-base-change` node were rejected before delivery.
They were not in the repository baseline and are not counted as pruned modules.
The unit record `dag/units/sk-thm-p1.json`, including every realized step, is unchanged.

## Where the brief, the DAG or earlier work was wrong

The proposed generic torsion theorem omitted `[IsAlgClosed k]` and is false: take the
proper identity on Spec R, r = 2, Λ = Z/2, F the constant Z/2 sheaf, and extend to C.
H¹(Spec R,Z/2) = Hom(Gal(C/R),Z/2) is nonzero, whereas H¹(Spec C,Z/2) = 0.
The hypothesis r • id = 0 does not fix this.

Merely repairing that hypothesis would still leave a wrong proof route: the generic
proper-base-change proof proposed in the old docstring is downstream of the curve
calculations in sk-thm-p1, so using it here would bypass the unit and introduce a circular
mathematical argument. Both faults were repaired by replacing that reduction.

The existing DAG node's proof plan was only a degree-split placeholder. Its proof,
proof_deps and proof_origin now describe the actual characteristic split, the prime-
invertible comparison, and the Artin--Schreier model followed by proved linear algebra.
Its statement and other fields are unchanged.

## New nodes

`lem-sc-artin-schreier-base-change-model` states the compatible fixed-point model in
`Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel`. It follows Stacks Tag 0A3P's
Artin--Schreier argument and flat coherent base change (02KH), with the existing
finite-sum coefficient presentation and large-universe filtered-colimit continuity.
The model alone does not claim that the comparison is bijective: the target supplies
that final step from the separately proved fixed-point invariance theorem. It is true
for arbitrary coefficient rings, including the zero ring, an empty prime-field basis,
infinite bases, and connected dimension-zero schemes.

Independent searches used leanfinder (Artin--Schreier/Frobenius description), loogle
(cohomologyMap, unknown identifier), and rg in both library roots. LeanSearch was also
attempted and returned an Internal Server Error, recorded as unavailable. The returned
Mathlib results do not identify this cohomological model; Finsupp.mapRange_bijective is
used rather than restated. The existing semilinear Frobenius theorem, characteristic-
invertible comparison lemmas, coefficient presentation and continuity are reused.
There are no change records, because no existing interface changes.


## Second reading by R2

1. Compared the delivered target module with the repository version. The theorem signature and all existing public imports are byte for byte unchanged; the delivery adds only proof-only imports and the proof body. The new Artin--Schreier module has a separate declaration and does not alter an existing interface. PASS.

2. Compiled both delivered modules with `lcompile.py --all`; both compile without warnings. The proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition contains `sorry`. The target's axiom probe reports `sorryAx` only through the explicitly split-off model theorem; the remaining allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. PASS for compilation and mechanism checks; the split-off theorem is recorded as an open hole.

3. Read the split-off model statement, docstring, and node. It is a strict intermediate Artin--Schreier/coherent-base-change identification: it gives additive equivalences to finitely supported Frobenius-fixed families and the coordinate formula, while leaving fixed-point invariance to the proved semilinear theorem. It does not restate proper base change and covers arbitrary commutative coefficients, including the zero and empty-basis cases. The statement is mathematically the needed model and its source and proof steps are documented. PASS.

4. Checked the proof route against the unit `sk-thm-p1`: the invertible-characteristic branch uses the existing prime-injective comparison and square transport, while the characteristic branch uses the Artin--Schreier model followed by the existing Frobenius and Finsupp bijectivity results. No generic proper-base-change theorem is introduced and no circular shortcut was found. The added imports are proof-only and the old empty proof dependency list is replaced by the five declarations actually used. PASS.

5. Updated the target DAG node's `proof`, `proof_deps`, and `proof_origin` to match the written proof, and added the model node with its Lean declaration and source metadata. Existing statement fields and unit realization are unchanged. PASS.

Changes made during second reading: added the target node's proof metadata and this review section; no Lean statements or definitions were changed.
