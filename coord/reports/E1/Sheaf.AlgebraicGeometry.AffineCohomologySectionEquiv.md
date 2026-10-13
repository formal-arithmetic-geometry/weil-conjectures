## What changed

Reduced `AlgebraicGeometry.Scheme.Modules.exists_affine_cohomology_section_equiv` without
changing its signature or docstring. Its proof now constructs the specified linear map,
proves its additive and scalar laws, and uses `LinearEquiv.ofBijective`.

The scalar argument is explicit: apply the supplied `hE` to multiplication by the image
of a section through `h`, apply `H.mapLinearEquiv.map_smul`, and use injectivity of `eH`
to identify its inverse on scalar multiples. Bijectivity follows by composition with the
additive equivalence `eH.symm`. The required normalization is reflexivity for the resulting
forward function. No data is chosen from a mere existence theorem.

Added two statement modules, each with one strictly smaller obligation:
`Sheaf.AlgebraicGeometry.AffineResolutionSectionBijective` and
`Sheaf.AlgebraicGeometry.ResolutionSectionScalarMap`. The former proves bijectivity of the
fixed resolution map without mentioning `E`, `hE`, scalar actions, or an equivalence. The
latter proves its multiplication-endomorphism identity on arbitrary opens, without
quasi-coherence, qcqs hypotheses, affineness, `E`, or bijectivity. Neither restates the
original existence of a normalized linear equivalence. Their docstrings and DAG nodes
specify the complete cocycle and resolution-comparison arguments.

Updated the original node's proof, dependencies and proof origin to match this reduction.
The unit `sk-thm-p1` and its realized nodes are unchanged. The original module's public
imports and exported signature are unchanged. A declaration-local heartbeat allowance
is needed for the explicit derived comparison types; the file compiles within the
single-file wall-clock limit.

Sources read: Stacks Tags 01F4 (2), 01XJ (1), 01E4 and 03FD on the Stacks website. Searched
the project and Mathlib through msearch LeanFinder, Loogle and grep. LeanSearch was
unavailable; it is recorded as unavailable rather than as a negative search. The existing
`AffineOpenHigherDirectImageSectionsIso` theorem gives an unspecified additive isomorphism;
it does not normalize `resolutionSectionClass` or give the required scalar law.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Scheme.Modules.exists_affine_cohomology_section_equiv`
(node `new-affine-cohomology-section-equiv`). Its body is complete Lean with no `sorry`.

Added two holes, both exactly `:= by sorry`, in new public theorems:

- `AlgebraicGeometry.Scheme.Modules.affine_resolutionSectionClass_bijective`
  (node `lem-pc-affine-resolution-section-bijective`).
- `AlgebraicGeometry.Scheme.Modules.resolutionSectionClass_map_smulHom`
  (node `lem-pc-resolution-section-scalar-map`).

This is a decomposition: one upper hole closed, two lower holes added, not a proof free
of postponed obligations. The main theorem still depends on these holes transitively.
No holes are left in a definition or a private declaration.

Checked the new statements against degree zero (augmentation and ordinary scalar action),
empty opens (zero section and cohomology groups), zero coefficients, and arbitrary natural
choices of `E`. The multiplication statement does not require an affine open; affineness
is used only for bijectivity. The proof uses the actual supplied `hE`, so it also covers a
natural comparison differing by an additive natural automorphism.

## No longer needed

Removed these proof-only imports from the original module:

- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
  (`lem-pc-leray-degenerate-sections`).
- `Sheaf.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent`
  (`lem-pc-ordinary-higher-image-quasi-coherent`).
- `Sheaf.AlgebraicGeometry.HigherDirectImageOpenRestriction`
  (`lem-pc-higher-direct-image-open-restriction`).
- `Sheaf.Paper.HigherDirectImagePresheaf`
  (`lem-weil-pbc-higher-direct-image-presheaf`).
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
  (`lem-pc-affine-vanishing`).

`pqf-def-cohomology` is also removed from the main node's `proof_deps`: it remains
a statement dependency and its definitions remain available through the public imports.

These are no longer direct dependencies of the main Lean proof. Their mathematical work
is still required by the bijectivity obligation's proof plan, whose DAG retains them.
Consequently no global mathematical pruning is claimed. No unit statement or realized
unit step is removed. The new modules import only what their statements need.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error found. The existing planned declarations supply the
Leray isomorphism and quasi-coherence, but their signatures do not directly identify the
arbitrary augmentation-preserving restricted-resolution formula with the edge and do not
express the local scalar compatibility of that formula. These are the two remaining
obligations; the scalar transport through `E` itself is proved in the original module.

## New nodes

`lem-pc-affine-resolution-section-bijective` is stated in
`lean/Sheaf/AlgebraicGeometry/AffineResolutionSectionBijective.lean`. It isolates affine
Leray degeneration together with cocycle normalization for the specified class map. Its
source is Stacks 01F4 (2), 01XJ (1), 01E4 and 01E5. The proof plan retains the relevant
existing nodes rather than duplicating the underlying quasi-coherence or vanishing lemmas.

`lem-pc-resolution-section-scalar-map` is stated in
`lean/Sheaf/AlgebraicGeometry/ResolutionSectionScalarMap.lean`. It isolates multiplication
naturality of the class map on arbitrary opens. Its source is Stacks 01E4 and 01E5 and
injective-resolution naturality. It is independent of the affine bijectivity argument.

Both inherit the original node's chapter, unit and blueprint ancestor, with the original
node prepended to `blueprint.from.via`. Blueprint searches for Leray and cohomology sections
and a project search for the normalized class-map/scalar formula found no exact existing
statement. No existing interface changed, so there is no change record or forced adaptation.


## Second reading by E1

1. Compared the original module with the repository by diff and checked the existing
   theorem signature byte for byte. It is identical; the docstring and public imports
   are unchanged. Only the proof, proof-only imports and declaration-local options changed.
   No definitions or target statements changed; no change record is required.
2. Compiled all three modules in import order through lcompile.py: clean, with no errors
   or warnings (4.6 s, 4.5 s, 45.3 s). The only direct holes are the two reported public
   theorems, each with a complete docstring proof and its matching node. No forbidden
   declarations or hollow definitions occur. The main proof constructs its linear map
   explicitly and uses the actual supplied naturality hypothesis, then ofBijective.
   A scratch module printed axioms for all three theorems: exactly propext,
   Classical.choice, Quot.sound and sorryAx. The delivery probe also checks every
   declaration. sorryAx is expected transitively because this is a decomposition,
   not a fully closed proof. The scratch file was removed before delivery.
3. Read both new statements, RestrictedResolutionSections and resolutionSectionClass.
   Augmentation pins the comparison on the resolved module, and components pins the
   section isomorphism; neither arbitrary comparison can change the derived class.
   Checked degree zero, zero coefficients and empty opens. Bijectivity is the affine
   Leray part; multiplication naturality applies on arbitrary opens and removes all
   affine and quasi-coherence assumptions. They are distinct parts of the argument,
   not renamed copies of the existence theorem. Read Stacks 01F4(2), 01XJ(1), 01E4 and
   01E5. Fresh msearch queries used LeanFinder for scalar multiplication on resolution
   cohomology, Loogle for isoRightDerivedObj_hom_naturality, and grep for smulHom and
   mapHomologyIso. Also searched both library roots and read the nearby affine sections
   isomorphism, affine cohomology presentation and coefficient comparison. These do not
   assert the fixed-R scalar identity or fixed-R bijectivity, so no immediate replacement
   was found. Closing either remaining hole requires the resolution normalization work.
4. Reviewed the proof from its target downward: additive transport and linearity are
   proved directly, leaving only the geometric bijectivity and local multiplication
   comparison. The imports are appropriate: proof-only imports are plain imports, and
   the new modules publicly import the definitions their statements use. All removed
   old proof dependencies are accounted for under No longer needed. The unchanged unit
   sk-thm-p1 realized record carries its statement and all steps; this reduction stays
   below that route and keeps the geometric prerequisites in the new bijectivity node.
5. Compared the existing node: only proof, proof_deps and proof_origin differ. Their
   dependencies agree with the actual Lean proof; each node's proof_deps equals the
   union of its step uses. Both new nodes have their source, searches, complete proof
   plan, creation record, inherited chapter/unit/blueprint and exact Lean statement.

Changes by the second reader: clarified that termwise multiplication is performed on
I restricted to U and conjugated by R.comparison, rather than on a global resolution
with a scalar defined only on U. Completed the removed-dependency report with
pqf-def-cohomology. No theorem statement or proof body needed repair.
