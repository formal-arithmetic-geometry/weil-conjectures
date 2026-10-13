## What changed

Reduced `AlgebraicGeometry.Etale.etale_limit_binary_successor_cocone_segment` to three
independent parts: canonical open cohomology cocones in any degree, geometric certificates
for their supplied comparisons, and compatible Mayer--Vietoris maps on these diagrams.
The existing theorem's signature, visibility, and docstring are unchanged.

Repair of the landing refusal: removed the duplicate private declarations
`biprod_prod_fst` and `biprod_prod_snd`. The two projection calculations now use
Mathlib's `AddCommGrpCat.biprodIsoProd_inv_comp_fst` and
`AddCommGrpCat.biprodIsoProd_inv_comp_snd` directly, followed by
`Iso.hom_inv_id_assoc`. The zero-restriction module's helpers are private and
cannot be accessed by importing that module; no duplicate declaration or extra
import remains.

The assembly constructs the directed tail and proves its finality. It constructs the
intersection compactness proof from quasi-separatedness of the union stage, transported
along the supplied isomorphism; it does not assume the ambient X is quasi-separated.
A proved private helper constructs each product certificate using the additive colimit
functor's biproduct comparison and proves equality with the supplied product cocone map
on every colimit leg and both product projections. The last square is obtained by the
colimit leg equation. No data definition chooses a witness from an unproved existence.

## Proved and sorry left

One original hole is closed by decomposition:
`AlgebraicGeometry.Etale.etale_limit_binary_successor_cocone_segment`.
The assembly proves the tail finality, intersection compactness, product certificates,
and passage from the final stage-leg square to the colimit square. Its module has no
remaining `sorry`. This closes the upper hole by decomposition, with the following
three lower holes; it is not a proof free of `sorry` dependencies.

Three holes are added, each in its own module:

- `AlgebraicGeometry.Etale.etale_limit_open_cohomology_cocone_degree`
  (`lem-weil-pbc-etale-limit-open-cohomology-cocone-degree`).
- `AlgebraicGeometry.Etale.etale_limit_open_comparison_certificate_degree`
  (`lem-weil-pbc-etale-limit-open-comparison-certificate-degree`).
- `AlgebraicGeometry.Etale.etale_limit_open_mayerVietoris_maps`
  (`lem-weil-pbc-etale-limit-open-mayer-vietoris-maps`).

This is a decomposition, not a sorry-free proof of the geometric construction;
the delivery's net hole count is one closed minus three added. The two concrete
arbitrary-degree maps are real constructions with no sorry.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`.
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`.
- `Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

Most are retained below the new geometric or Mayer--Vietoris statements; removing
the direct imports does not claim their modules disappear from the targets' closure.
The finite-limit/filtered-colimit result
`lem-weil-pbc-filtered-colimits-commute-finite-limits` is unnecessary for this assembly:
colim is additive and preserves binary biproducts by its left adjoint property.
The complete list removed from the parent node's old `proof_deps` is:

- `lem-weil-pbc-cohomology-pullback-functorial` (used below the new cocone and maps nodes).
- `lem-weil-pbc-etale-inverse-image-restriction` (restriction construction below the
  geometric certificate; the inverse-image implementation remains imported there).
- `lem-weil-pbc-etale-limit-canonical-cohomology-diagram` (used below the new cocone node).
- `lem-weil-pbc-etale-mayer-vietoris` (used below the new maps node).
- `lem-weil-pbc-etale-mayer-vietoris-pullback` (used below the new maps node).
- `lem-weil-pbc-filtered-colimits-commute-finite-limits` (unnecessary for this assembly).
- `lem-weil-pbc-inverse-image-composition` (used below the cocone and certificate nodes).
- `lem-weil-pbc-limit-cone-affine-projections-opens` (used below the certificate node).

These are removed direct parent dependencies, not claims that all their modules are
pruned from the targets' closure. No unit-level statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing single-open cocone and certificate interfaces are restricted to degree
zero. They cannot be applied at q or q+1 as the parent proof plan suggests. This delivery
states their arbitrary-degree counterparts rather than adapting existing interfaces
and forcing changes in other holders' modules.

The supplied pairwise pullback Mayer--Vietoris theorem alone does not give a single
choice of connecting transformations compatible with every coefficient transition
and every projection at once. The new maps theorem explicitly requires and records
that simultaneous functorial construction. It asserts no certificate or continuity,
while the certificate theorem asserts no Mayer--Vietoris maps or exactness.

LeanSearch was unavailable (Internal Server Error). LeanFinder returned generic
MayerVietorisSquare tools, and Loogle returned naturality tools, not the required
restricted-system construction. Direct source searches located the degree-zero
interfaces and the already-proved canonical cohomology diagram theorem.

## New nodes

`lem-weil-pbc-etale-limit-open-cohomology-cocone-degree` constructs only canonical
restricted diagrams and cocones, in arbitrary degree. It has no compactness, affine,
limit, colimit or exactness hypothesis or conclusion. Its two concrete map definitions
reuse the existing restricted scheme and coefficient maps.

`lem-weil-pbc-etale-limit-open-comparison-certificate-degree` certifies a supplied
canonical comparison for one quasi-compact open and one degree. It adds the geometric
limit and coefficient colimit assumptions and asserts no comparison isomorphism.

`lem-weil-pbc-etale-limit-open-mayer-vietoris-maps` constructs the compatible exact
maps on supplied canonical diagrams. It has no geometric limit, compactness or sheaf
colimit assumptions, and asserts neither certificates nor group-colimit properties.
Its projection equations let the original module's assembly prove the product comparison
identities rather than assuming them.

All three follow Tags 09YQ and 0A50 and record actual searches. Empty/coincident opens,
zero coefficients, degree zero, and singleton diagrams are included; positive
successor degree is explicitly q+1. No change record or forced adaptation is needed.

The original theorem signature was compared byte-for-byte with the repository
statement and is unchanged. The completed assembly compiled locally in 42.4 seconds;
the delivery dry run also checks the whole set and its axiom probes.

The preserved attempt repeatedly timed out while matching cohomology types through
a local abbreviation for the scheme map. This repair removes that abbreviation,
preserves bundled group structures in the product helper, gives both product
certificates explicit types, and assembles the existential witnesses directly. The last square follows from
`colimit.ι_desc` and a reflexive identification of the tail functor at an index. No compiler limit or tool was changed,
and no proof or module was split to evade the limit.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem signature and existing declarations are byte-for-byte unchanged; only proof imports and proof bodies differ.
2. Compiled all four sandbox modules with `lcompile.py`; they compile without errors. The three deliberately split declarations are the only remaining `sorry`s, and no forbidden declarations occur.
3. Checked the three split statements against their node records and searched the repository for duplicates. Each is a strict lower-level construction, with source, proof plan, and Lean declaration recorded; edge cases are covered by the unrestricted degree and nonempty-tail hypotheses.
4. The proof follows the unit route through the tail, open comparison certificates, and Mayer--Vietoris maps. Unused direct imports were removed and the parent node's proof dependencies were updated to the declarations actually used.
5. The node proof, dependencies, origin, and Lean records agree with the repaired proof and imports. The unit realization is preserved.

Changed the parent proof assembly and its node metadata only as described above; no statement or definition was changed.


## Second reading by R1

1. **Interface: PASS.** Read the diff of the parent module against the read-only
   repository and checked it with the declaration comparison tool. Its existing
   theorem signature and docstring are byte-for-byte unchanged. Public imports
   are unchanged; the new helper is private. No definition or target statement
   changes, forced adaptations, or change records are present.
2. **Kernel and holes: PASS as a decomposition.** Compiled all four modules with
   `lcompile.py --all`: 26.2, 2.9, 22.1, and 53.1 seconds respectively, without
   errors or warnings. A scratch axiom probe printed only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for the four theorems; both
   concrete map definitions use only the three permitted axioms. The three
   reported public named theorems are exactly the remaining holes. Scanned for
   forbidden declarations and kernel-bypass attributes and found none. The
   existential choices occur inside a theorem proof, not in data definitions.
3. **Split statements: PASS.** Read each signature, its docstring argument, and
   its complete node. The cocone assertion proves only functor and cocone laws;
   the certificate assertion certifies a supplied map without continuity; the
   Mayer--Vietoris assertion provides compatible exact maps without certificates.
   Each is strictly part of the parent construction. Checked the directions of
   the coefficient maps, the q to q+1 boundary, the fixed restriction r', and
   all four product projection formulas. Empty and coincident opens, zero
   coefficients, degree zero and a singleton directed diagram give the expected
   zero, diagonal/difference, or ordinary restriction cases. Read Stacks
   [09YQ](https://stacks.math.columbia.edu/tag/09YQ),
   [0A50](https://stacks.math.columbia.edu/tag/0A50), and
   [01F7](https://stacks.math.columbia.edu/tag/01F7). Repeated searches with
   `leanfinder` for cohomology natural transformations on restricted inverse
   systems and `loogle` for `Functor.mapBiprod`, plus `rg` in both Lean roots.
   Found only generic tools and the existing degree-zero open interfaces, not
   duplicates. The arbitrary-degree canonical diagram is already used in the
   cocone node's reduction. Closing any of these three holes requires substantial
   coherence or naturality work, not a short application of an existing theorem.
4. **Route and pruning: PASS.** Checked the parent assembly from its conclusion
   backward. It proves directed-tail finality, intersection compactness using
   quasi-separatedness of the union stage, equality of the product comparison
   on every leg and both projections, and the final square using `colimit.ι_desc`.
   The additive colimit biproduct comparison is the shorter route and does not
   require filtered finite-limit commutation. Proof-only imports are plain
   imports. Checked `dag/units/sk-thm-p1.json`: no realized statement or step is
   bypassed or changed. The pruning section now explicitly lists every old
   parent proof dependency absent from the delivered parent dependency list.
5. **DAG: PASS.** Compared all four nodes to the Lean. Each recorded declaration
   statement matches; each `proof_deps` is exactly the union of its step uses.
   The existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   The three new nodes contain source, searches, creation, blueprint, unit,
   chapter, and Lean records. Their proof plans match the three remaining holes;
   the parent plan matches the compiled assembly.

Second reading changed only this report: completed the removed-dependency list
and added the independent review and fresh compile/axiom evidence. No Lean or
node repair was needed. One upper hole closed by decomposition, three lower
holes added; this remains net -2 holes and is not a sorry-free proof.
