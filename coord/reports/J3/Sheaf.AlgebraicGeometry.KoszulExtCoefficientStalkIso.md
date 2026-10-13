## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.KoszulExtCoefficientStalkIso`
with a complete Lean proof. The existing definition and theorem signatures are
unchanged, as are all public imports. The proof uses a commuting stalk model,
proves the algebraic coefficient map bijective, extends that linear equivalence
along the actual germ/stalk ring map, and transports injectivity and surjectivity
through the two additive coordinates. No flatness assumption is introduced.

Added three modules:

- `Sheaf.RingTheory.KoszulQuotientCoefficientComplex` constructs the actual signed
  quotient-valued dual complex and reduction cochain map. Square-zero and
  differential compatibility are proved; no data is selected from an unproved
  existence theorem.
- `Sheaf.RingTheory.KoszulCoefficientTopHomology` proves that reduction induces an
  isomorphism on top cohomology, without any regularity hypothesis. It calculates
  the incoming image using the ordered top wedge, complementary coordinate
  functionals and unit signs; proves quotient differentials zero; and uses
  projective lifting and the short-complex opcycles criterion. The elementary
  private calculations reuse the proved arguments in
  `KoszulConormalTopHomologyPos` and `KoszulCoefficientExtensionChi`, rather than
  importing their conormal/localization interfaces. All private helpers are proved.
- `Sheaf.AlgebraicGeometry.KoszulExtCoefficientStalkModel` states the remaining
  geometric, natural comparison, in every nonnegative cohomology degree `m`,
  independently of sequence length `n`. It identifies a specified morphism with
  scalar extension of an explicit algebraic cohomology map; it does not assert
  bijectivity. Its resolution, restriction, finite-free Hom, stalk-exactness and
  tensor-stalk dependencies are imported for the next worker.

Read Stacks Tag 0BQZ, `lemma-regular-immersion-ext`, at
https://stacks.math.columbia.edu/tag/0BQZ. Its proof explicitly reduces the
coefficient-map assertion to the morphism of dual Koszul Hom complexes. The
existing unit and its realized steps are unchanged.

The four delivered Lean modules compile together, without warnings, using
`lcompile.py --all`. The algebraic theorem handles `r=0`, `I=A` and the zero ring
in its proof. At `r=0`, the generation equation forces `I=0`; no positive-rank or
nonzero-quotient assumption is hidden. The geometric model only requires
regularity on the specified affine chart and makes no assertion at other points.
No axiom, definition sorry or signature change is added.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.koszulRegularImmersion_ext_coefficient_stalk_iso`
(node `lem-sc-koszul-ext-coefficient-stalk-iso`). No sorry remains in the item's
module.

Also proved:
`ExteriorAlgebra.koszulCoefficientReduction_isIso_top_homology`
(node `new-j3-koszul-coefficient-top-homology`), together with every declaration
in `KoszulQuotientCoefficientComplex` and all private helpers in the algebraic
calculation.

Added exactly one hole:
`AlgebraicGeometry.koszulExtCoefficient_stalk_model`
(node `new-j3-koszul-ext-coefficient-stalk-model`). Its proof is exactly
`by sorry`; its docstring gives the complete natural-language argument. The
remaining work is the natural identification of the geometric derived
coefficient morphism with the explicitly constructed algebraic reduction map.
It must preserve the displayed commuting equation, not just the two objects.

This is a decomposition: one original hole closed and one new hole added. The
direct hole balance is zero; the maintainer computes closure figures against
the pinned ledger baselines. The algebraic top-degree calculation
and the transport argument are fully proved; the geometric comparison remains
open. The unchanged imported modules may still rest on their pre-existing holes.

## No longer needed

Removed the following direct proof imports from the item's module:
`Sheaf.RingTheory.KoszulProjectiveResolution`,
`Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`,
`Sheaf.Paper.DerivedInternalHomRestrictOpen`,
`Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`, and
`Mathlib.LinearAlgebra.ExteriorPower.Basis`.

They are still needed by the new stalk model, and the exterior basis is used by
the proved algebraic calculation. Consequently no old DAG node or module is
claimed pruned from the target's import closure. The former five proof-dependency
nodes remain dependencies of the new stalk-model node. Pruned modules: none.
The old direct `proof_deps` removed from the item's node are
`new-j3-koszul-projective-resolution`,
`lem-sc-affine-quotient-resolution-sheafification`,
`lem-sc-derived-internal-hom-restrict-open`,
`lem-sc-derived-hom-finite-free-model`, and
`lem-weil-pbc-exterior-power-free-basis`. They all remain used transitively by
the new nodes; none is claimed unnecessary in the target closure.

The second reader also removed the unused public import
`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` from
`KoszulQuotientCoefficientComplex` and the redundant public import
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` from
`KoszulCoefficientTopHomology` (already provided by `KoszulComplex`).
The conormal determinant comparison modules and localization-specific
coefficient-extension modules were read for their proved calculation but are
not imported by this delivery.

## Where the brief, the DAG or earlier work was wrong

The available derived finite-free Hom and open restriction lemmas supply object
isomorphisms. Their statements do not expose the naturality square for the
specified coefficient morphism. The old node's final step marked the
sheafification, tensor-pullback and stalk transport as elementary, but that
transport must retain the map, and it is not a short application of those object
isomorphisms. The new stalk-model theorem records this remaining argument
explicitly. No existing mathematical statement was found false or changed.

The algebraic top-degree calculation does not need Koszul regularity. The new
proved algebraic theorem therefore has only the ideal-generation hypothesis.
The geometric model retains regularity, which is needed for the resolution.

LeanSearch was unavailable; actual LeanFinder, Loogle and Mathlib grep searches
were also run and logged in the sandbox. None supplied the precise morphism
comparison. Searches for stalk localization found useful general tilde stalk
maps, which do not compute the natural derived coefficient morphism.

## New nodes

`new-j3-koszul-quotient-coefficient-complex` records the explicit complex and
cochain map in `Sheaf.RingTheory.KoszulQuotientCoefficientComplex`. Its construction
and supporting differential identities are fully proved.

`new-j3-koszul-coefficient-top-homology` records the proved algebraic top-degree
calculation in `Sheaf.RingTheory.KoszulCoefficientTopHomology`. It is valid over
arbitrary commutative rings, including zero rings, and requires no regularity.

`new-j3-koszul-ext-coefficient-stalk-model` records the one remaining theorem in
`Sheaf.AlgebraicGeometry.KoszulExtCoefficientStalkModel`. The independent degree
parameter separates this natural affine computation from the top-degree
invertibility assertion of the item. Both the original node and new nodes have
proof steps and proof dependencies synchronized with the delivered argument.
No change record is needed: existing definitions, statements, signatures and
visibility are unchanged.

## Second reading by J3

1. Compared the delivered item with the repository using `diff -u`. The existing
   coefficient-map definition is byte-for-byte unchanged. The theorem signature,
   documentation, visibility and public imports are unchanged; only its proof,
   a local heartbeat option, and private proof imports differ. The other three
   modules and nodes are new, with no adaptations or interface change to existing
   declarations. Verdict: pass; no change record is required.

2. Read all four modules and compiled the complete set locally. Every helper is
   proved. The sole `sorry` is the public named theorem
   `AlgebraicGeometry.koszulExtCoefficient_stalk_model`, exactly as listed above;
   no definition contains a hole or data chosen from an unproved existence
   theorem. Scanned for the forbidden trust escapes. Independently ran
   `#print axioms` for all six new coefficient-complex declarations, the algebraic
   top-homology theorem, the geometric model, and both existing declarations.
   The algebraic declarations and coefficient-map definition use only `propext`,
   `Classical.choice`, and `Quot.sound`. The model and original theorem additionally
   use `sorryAx`, as expected from the one open model theorem. Verdict: pass as
   a decomposition, not a sorry-free proof of the original theorem.

3. Checked the remaining geometric comparison against Stacks Tag 0BQZ and its
   finite-free Hom computation. It identifies the actual morphism, using the
   correct germ/stalk scalar structure and tensoring cohomology only after taking
   it. It does not assume flat pullback or interchange nonflat tensor with
   cohomology. For n=0, I=0 and the coefficient morphism is identity; for m>n both
   modeled cohomology groups vanish; for lower m the source and target need not
   coincide and the statement does not assert they do. A point z over U rules out
   the unit-ideal empty-preimage case. Its docstring and matching node record the
   naturality argument. This is strictly the geometric-comparison part of the
   argument: the algebraic top-degree invertibility is independently proved.
   Searched again with LeanFinder for naturality of sheaf Ext under coefficient
   maps, Loogle for a tilde stalk isomorphism, Mathlib grep for quotient homology
   and Ext stalk comparisons, and repository/upstream searches for Koszul
   coefficient constructions. No existing declaration states this commuting
   derived comparison. The existing conormal and coefficient-extension results
   have different interfaces; their applicable private calculations were reused.
   Verdict: pass; the remaining comparison is true and is not a renamed item.

4. Read the proof from the original theorem down through the algebraic theorem
   and explicit complexes. The transport uses scalar extension of a linear
   equivalence, requiring no flatness. The incoming-image calculation, projective
   lift and opcycles criterion prove the algebraic assertion over arbitrary
   commutative rings, including rank zero and the zero ring. No shorter existing
   public theorem closes the remaining comparison. Removed two redundant public
   imports from the new modules and recompiled all four successfully. Listed all
   five old direct dependency nodes above, distinguishing transitive retention
   from actual pruning. Read `dag/units/sk-thm-picard-duality.json`; its route and
   `realized` data are untouched, and no realized step is bypassed. Verdict: pass.

5. Compared the original node diff and all three new nodes with the Lean proof.
   Only the allowed proof fields of the existing node change. The new nodes have
   source, self-contained statements, proof steps, matching dependency unions,
   search records, creation and blueprint records, chapter/unit and verbatim Lean
   signatures. The original node uses exactly the geometric comparison and the
   proved algebraic top-homology theorem; the model retains all five former
   dependencies and records its stalk comparisons. Verdict: pass.

Changes by the second reader: removed the two redundant public imports above;
made the old direct dependency-node accounting explicit; appended this review.
No proof, definition, declaration signature or DAG route needed repair. No
additional hole was added or closed in this reading. The geometric comparison
cannot be closed in a few minutes from the current object-isomorphism interfaces.
